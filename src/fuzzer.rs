use std::collections::hash_map::Entry;
use crate::trie_map::BytesTrieMap;
use rand::Rng;
use rand_distr::{Pert, Distribution};
use std::marker::PhantomData;
use std::ptr::null;
use gxhash::{HashMap, HashMapExt};
use rand::distr::{Iter, Uniform};
use crate::TrieValue;
use crate::utils::{BitMask, ByteMask};
use crate::zipper::{ReadZipperUntracked, Zipper, ZipperIteration, ZipperMoving, ZipperReadOnly};


#[derive(Debug)]
pub struct Histogram<T : std::cmp::Eq + std::hash::Hash> {
  counts: Vec<usize>,
  lookup: HashMap<T, usize>
}
impl <T : std::cmp::Eq + std::hash::Hash> Histogram<T> {
  pub fn from(iter: impl IntoIterator<Item=T>) -> Self {
    let mut counts = vec![];
    let mut lookup = HashMap::new();
    iter.into_iter().for_each(|t| {
      match lookup.entry(t) {
        Entry::Occupied(i) => { counts[*i.get()] += 1; }
        Entry::Vacant(i) => { i.insert(counts.len()); counts.push(1) }
      }
    });
    let mut indices: Vec<usize> = (0..counts.len()).collect();
    indices.sort_by_key(|i| counts[*i]);
    counts.sort(); // this is wasteful, can use argsort
    for (_, v) in lookup.iter_mut() { *v = indices[*v]; }
    Histogram { counts, lookup }
  }

  pub fn table(&self) -> Vec<(&T, usize)> {
    // this is wasteful, perhaps we should use a deconstructed hashmap so &[(T, usize)] coincides with our internal representation
    let mut v = vec![(null(), 0usize); self.counts.len()];
    for (t, i) in self.lookup.iter() {
      v[*i] = (t, self.counts[*i])
    }
    unsafe { std::mem::transmute(v) }
  }
}

pub struct Filtered<T, D : Distribution<T>, P : Fn(&T) -> bool> { d: D, p: P, pd: PhantomData<T> }
impl <T, D : Distribution<T>, P : Fn(&T) -> bool> Distribution<T> for Filtered<T, D, P> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
    loop {
      let s = self.d.sample(rng);
      if (self.p)(&s) { return s }
    }
  }
}

pub struct Product2<X, DX : Distribution<X>, Y, DY : Distribution<Y>, Z, F : Fn(X, Y) -> Z> { dx: DX, dy: DY, f: F,
  pd: PhantomData<(X, Y, Z)> }
impl <X, DX : Distribution<X>, Y, DY : Distribution<Y>, Z, F : Fn(X, Y) -> Z> Distribution<Z> for Product2<X, DX, Y, DY, Z, F> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Z {
    (self.f)(self.dx.sample(rng), self.dy.sample(rng))
  }
}

pub struct Choice2<X, DX : Distribution<X>, Y, DY : Distribution<Y>, DB : Distribution<bool>> { dx: DX, dy: DY, db: DB,
  pd: PhantomData<(X, Y)> }
impl <X, DX : Distribution<X>, Y, DY : Distribution<Y>, DB : Distribution<bool>> Distribution<Result<X, Y>> for Choice2<X, DX, Y, DY, DB> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Result<X, Y> {
    if self.db.sample(rng) { Ok(self.dx.sample(rng)) }
    else { Err(self.dy.sample(rng)) }
  }
}

pub struct Dependent2<X, DX : Distribution<X>, Y, DY : Distribution<Y>, FDY : Fn(X) -> DY> { dx: DX, fdy: FDY,
  pd: PhantomData<(X, Y)> }
impl <X, DX : Distribution<X>, Y, DY : Distribution<Y>, FDY : Fn(X) -> DY> Distribution<Y> for Dependent2<X, DX, Y, DY, FDY> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Y {
    (self.fdy)(self.dx.sample(rng)).sample(rng)
  }
}

pub struct Concentrated<X, DX : Distribution<X>, A : Clone, Y, FA : Fn(&mut A, X) -> Option<Y>> { dx: DX, z: A, fa: FA,
  pd: PhantomData<(X, Y)> }
impl <X, DX : Distribution<X>, A : Clone, Y, FA : Fn(&mut A, X) -> Option<Y>> Distribution<Y> for Concentrated<X, DX, A, Y, FA> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Y {
    let mut a = self.z.clone();
    loop {
      match (self.fa)(&mut a, self.dx.sample(rng)) {
        None => {}
        Some(y) => { return y }
      }
    }
  }
}

pub struct Diluted<X, DX : Distribution<X>, A : Clone, Y, FA : Fn(X) -> A, FAY : Fn(&mut A) -> Option<Y>> { dx: DX, fa: FA, fay: FAY,
  pd: PhantomData<(X, A, Y)> }
impl <X, DX : Distribution<X>, A : Clone, Y, FA : Fn(X) -> A, FAY : Fn(&mut A) -> Option<Y>> Distribution<Y> for Diluted<X, DX, A, Y, FA, FAY> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Y {
    let mut a = (self.fa)(self.dx.sample(rng));
    (self.fay)(&mut a).expect("fay returns at least once per fa call")
  }

  fn sample_iter<R>(self, rng: R) -> Iter<Self, R, Y> where R : Rng, Self : Sized {
    panic!("This function returning a concrete object makes it impossible to override the iterator behavior")
  }
}

pub struct Degenerate<T : Clone> { element: T }
impl <T : Clone> Distribution<T> for Degenerate<T> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
    self.element.clone()
  }
}

pub struct Categorical<T : Clone, ElemD : Distribution<usize>> { elements: Vec<T>, ed: ElemD }
impl <T : Clone, ElemD : Distribution<usize>> Distribution<T> for Categorical<T, ElemD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
    self.elements[self.ed.sample(rng)].clone()
  }
}
pub fn ratios<T : Clone>(ep: impl IntoIterator<Item=(T, usize)>) -> Categorical<T, rand::distr::Map<Uniform<usize>, impl Fn(usize) -> usize, usize, usize>> {
  let mut elements = vec![];
  let mut cdf = vec![];
  let mut sum = 0;
  for (e, r) in ep.into_iter() {
    elements.push(e);
    cdf.push(sum);
    sum += r;
  }
  let us = Uniform::try_from(0..sum).unwrap();
  Categorical {
    elements,
    // it's much cheaper to draw many samples at once, but the current Distribution API is broken
    ed: us.map(move |x| { match cdf.binary_search(&x) {
      Ok(i) => { i }
      Err(i) => { i - 1 }
    }})
  }
}

pub struct Repeated<ByteD : Distribution<u8>> { length: usize, bd: ByteD }
impl <ByteD : Distribution<u8>> Distribution<Vec<u8>> for Repeated<ByteD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<u8> {
    Vec::from_iter(std::iter::repeat_with(|| self.bd.sample(rng)).take(self.length))
  }
}

pub struct Sentinel<MByteD : Distribution<Option<u8>>> { mbd: MByteD }
impl <MByteD : Distribution<Option<u8>>> Distribution<Vec<u8>> for Sentinel<MByteD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<u8> {
    let mut v = vec![];
    while let Some(e) = self.mbd.sample(rng) {
      v.push(e)
    }
    v
  }
}

pub struct UniformTrie<T : TrieValue, PathD : Distribution<Vec<u8>>, ValueD : Distribution<T>> { size: usize, pd: PathD, vd: ValueD, ph: PhantomData<T> }
impl <T : TrieValue, PathD : Distribution<Vec<u8>>, ValueD : Distribution<T>> Distribution<BytesTrieMap<T>> for UniformTrie<T, PathD, ValueD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BytesTrieMap<T> {
    let mut btm = BytesTrieMap::new();
    for i in 0..self.size {
      btm.insert(&self.pd.sample(rng)[..], self.vd.sample(rng));
    }
    btm
  }
}

/*
// fancier Trie Distributions WIP
pub struct GrowTrie<T, SproutD : Fn(&BytesTrieMap<T>) -> Distribution<BytesTrieMap<T>>> { seed: BytesTrieMap<T>, sd: SproutD }
impl <T, SproutD : Fn(T) -> Distribution<&BytesTrieMap<T>>> Distribution<BytesTrieMap<T>> for GrowTrie<T, SproutD> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BytesTrieMap<T> {
    let mut btm = BytesTrieMap::new();
    for i in 0..self.size {
      btm.insert(&self.pd.sample(rng)[..], self.vd.sample(rng));
    }
    btm
  }
}*/

pub struct FairTrieValue<T : TrieValue> { source: BytesTrieMap<T> }
impl <T : TrieValue> Distribution<(Vec<u8>, T)> for FairTrieValue<T> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (Vec<u8>, T) {
    // it's much cheaper to draw many samples at once, but the current Distribution API is broken
    let mut rz = self.source.read_zipper();
    let size = rz.val_count();
    let target = rng.random_range(0..size);
    let mut i = 0;
    while let Some(t) = rz.to_next_val() {
      if i == target { return (rz.path().to_vec(), t.clone()) }
      i += 1;
    }
    unreachable!();
  }
}

pub struct DescendFirstTrieValue<T : TrieValue, ByteD : Distribution<u8>, P : Fn(&ReadZipperUntracked<T>) -> ByteD> { source: BytesTrieMap<T>, policy: P }
impl <T : TrieValue, ByteD : Distribution<u8>, P : Fn(&ReadZipperUntracked<T>) -> ByteD> Distribution<(Vec<u8>, T)> for DescendFirstTrieValue<T, ByteD, P> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (Vec<u8>, T) {
    let mut rz = self.source.read_zipper();
    while !rz.is_value() {
      let b = (self.policy)(&rz).sample(rng);
      rz.descend_to_byte(b);
    }
    (rz.path().to_vec(), rz.get_value().unwrap().clone())
  }
}
fn unbiased_descend_first_policy<T : TrieValue>(rz: &ReadZipperUntracked<T>) -> Categorical<u8, Uniform<usize>> {
  let bm = ByteMask(rz.child_mask());
  Categorical{ elements: bm.iter().collect(), ed: Uniform::try_from(0..bm.count_bits()).unwrap() }
}

pub struct FairTriePath<T : TrieValue> { source: BytesTrieMap<T> }
impl <T : TrieValue> Distribution<(Vec<u8>, Option<T>)> for FairTriePath<T> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (Vec<u8>, Option<T>) {
    use crate::morphisms::Catamorphism;
    // it's much cheaper to draw many samples at once, but the current Distribution API is broken
    let size = Catamorphism::into_cata_cached(self.source.clone(), |_: &ByteMask, ws: &mut [usize], mv: Option<&T>, path: &[u8]| {
      ws.iter().sum::<usize>() + 1
    });
    let target = rng.random_range(0..size);
    let mut i = 0;
    Catamorphism::into_cata_side_effect_fallible(self.source.clone(), |_: &ByteMask, _, mv: Option<&T>, path: &[u8]| {
      if i == target { Err((path.to_vec(), mv.cloned())) } else { i += 1; Ok(()) }
    }).unwrap_err()
  }
}

pub struct DescendTriePath<T : TrieValue, S, SByteD : Distribution<Result<u8, S>>, P : Fn(&ReadZipperUntracked<T>) -> SByteD> { source: BytesTrieMap<T>, policy: P, ph: PhantomData<S> }
impl <T : TrieValue, S, SByteD : Distribution<Result<u8, S>>, P : Fn(&ReadZipperUntracked<T>) -> SByteD> Distribution<(Vec<u8>, S)> for DescendTriePath<T, S, SByteD, P> {
  fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> (Vec<u8>, S) {
    let mut rz = self.source.read_zipper();
    loop {
      match (self.policy)(&rz).sample(rng) {
        Ok(b) => { rz.descend_to_byte(b); }
        Err(s) => { return (rz.path().to_vec(), s) }
      }
    }
    unreachable!()
  }
}
fn unbiased_descend_last_policy<T : TrieValue>(rz: &ReadZipperUntracked<T>) -> Choice2<u8, Categorical<u8, Uniform<usize>>, T, Degenerate<T>, Degenerate<bool>> {
  let bm = ByteMask(rz.child_mask());
  let options: Vec<u8> = bm.iter().collect();
  let noptions = options.len();
  Choice2 {
    db: Degenerate{ element: noptions > 0 },
    dx: Categorical{ elements: options, ed: Uniform::try_from(0..noptions).unwrap_or(unsafe { std::mem::MaybeUninit::uninit().assume_init() }) },
    dy: Degenerate{ element: rz.get_value().cloned().unwrap_or(unsafe { std::mem::MaybeUninit::uninit().assume_init() }) },
    pd: PhantomData::default()
  }
}


#[cfg(test)]
mod tests {
  use rand::rngs::StdRng;
  use rand::SeedableRng;
  use rand_distr::Uniform;
  use crate::fuzzer::*;
  use crate::zipper::Zipper;

  #[test]
  fn fixed_length() {
    let mut rng = StdRng::from_seed([0; 32]);
    let path_fuzzer = Repeated { length: 3, bd: Categorical { elements: "abcd".as_bytes().to_vec(),
      ed: Uniform::try_from(0..4).unwrap() } };
    let trie_fuzzer = UniformTrie { size: 10, pd: path_fuzzer, vd: Degenerate{ element: () }, ph: PhantomData::default() };
    let trie = trie_fuzzer.sample(&mut rng);
    let res = ["aaa", "aac", "bba", "bdd", "cbb", "cbd", "dab", "dac", "dca"];
    trie.iter().zip(res).for_each(|(x, y)| assert_eq!(x.0.as_slice(), y.as_bytes()));
  }

  #[test]
  fn variable_length() {
    let mut rng = StdRng::from_seed([0; 32]);
    let path_fuzzer = Filtered{ d: Sentinel { mbd: Categorical { elements: "abcd\0".as_bytes().to_vec(),
      ed: Uniform::try_from(0..5).unwrap() }.map(|x| if x == b'\0' { None } else { Some(x) }) }, p: |x| !x.is_empty(), pd: PhantomData::default() };
    let trie_fuzzer = UniformTrie { size: 10, pd: path_fuzzer, vd: Degenerate{ element: () }, ph: PhantomData::default() };
    let trie = trie_fuzzer.sample(&mut rng);
    // println!("{:?}", trie.iter().map(|(p, _)| String::from_utf8(p).unwrap()).collect::<Vec<_>>());
    let res = ["aa", "acbdddacbcbdbad", "bbddad", "bd", "caccb", "cba", "cbcdbccb", "dadbcdbcaaadb", "dbabbdaabc", "dbb"];
    trie.iter().zip(res).for_each(|(x, y)| assert_eq!(x.0.as_slice(), y.as_bytes()));
  }

  #[test]
  fn fair_trie_value() {
    const samples: usize = 100000;
    let mut rng = StdRng::from_seed([0; 32]);
    let btm = BytesTrieMap::from_iter([("abc", 0), ("abd", 1), ("ax", 2), ("ay", 3), ("A1", 4), ("A2", 5)].iter().map(|(s, i)| (s.as_bytes(), i)));
    let stv = FairTrieValue{ source: btm };
    let hist = Histogram::from(stv.sample_iter(rng).map(|(_, v)| v).take(6*samples));
    let achieved: Vec<usize> = hist.table().into_iter().map(|(k, c)|
      ((c as f64)/((samples/100) as f64)).round() as usize).collect();
    achieved.into_iter().for_each(|c| assert_eq!(c, 100));
  }

  #[test]
  fn descend_first_trie_value() {
    const samples: usize = 100000;
    let mut rng = StdRng::from_seed([0; 32]);
    let btm = BytesTrieMap::from_iter([("abc", 0), ("abcd", 10), ("abd", 1), ("ax", 2), ("ay", 3), ("A1", 4), ("A2", 5)].iter().map(|(s, i)| (s.as_bytes(), i)));
    let stv = DescendFirstTrieValue{ source: btm, policy: unbiased_descend_first_policy };
    let hist = Histogram::from(stv.sample_iter(rng).map(|(_, v)| *v).take(6*samples));
    // println!("{:?}", hist.table());
    let achieved: Vec<(i32, i32)> = hist.table().into_iter().map(|(k, c)|
      (*k, ((c as f64)/((samples/10) as f64)).round() as i32)).collect();
    assert_eq!(&achieved[..], &[(3, 5), (2, 5), (5, 10), (4, 10), (0, 15), (1, 15)]);
  }

  #[test]
  fn descend_last_trie_value() {
    const samples: usize = 100000;
    let mut rng = StdRng::from_seed([0; 32]);
    let btm = BytesTrieMap::from_iter([("abc", 0), ("abcd", 10), ("abd", 1), ("ax", 2), ("ay", 3), ("A1", 4), ("A2", 5)].iter().map(|(s, i)| (s.as_bytes(), i)));
    let stv = DescendTriePath{ source: btm, policy: unbiased_descend_last_policy, ph: Default::default() };
    let hist = Histogram::from(stv.sample_iter(rng).map(|(_, v)| *v).take(6*samples));
    // println!("{:?}", hist.table());
    let achieved: Vec<(i32, i32)> = hist.table().into_iter().map(|(k, c)|
        (*k, ((c as f64)/((samples/10) as f64)).round() as i32)).collect();
    assert_eq!(&achieved[..], &[(3, 5), (2, 5), (5, 10), (4, 10), (10, 15), (1, 15)]);
  }

  #[test]
  fn fair_trie_path() {
    const samples: usize = 100000;
    let mut rng = StdRng::from_seed([0; 32]);
    let btm = BytesTrieMap::from_iter([("abc", 0), ("abd", 1), ("ax", 2), ("ay", 3), ("A1", 4), ("A2", 5)].iter().map(|(s, i)| (s.as_bytes(), i)));
    let stv = FairTriePath{ source: btm };
    let hist = Histogram::from(stv.sample_iter(rng).map(|(p, _)| p).take(10*samples));
    let achieved: Vec<usize> = hist.table().into_iter().map(|(k, c)|
      ((c as f64)/((samples/100) as f64)).round() as usize).collect();
    achieved.into_iter().for_each(|c| assert_eq!(c, 100));
  }

  #[test]
  fn monte_carlo_pi() {
    const samples: usize = 100000;
    let rng = StdRng::from_seed([0; 32]);
    let sx = Uniform::new(0.0, 1.0).unwrap();
    let sy = Uniform::new(0.0, 1.0).unwrap();
    let sxy = Product2 { dx: sx, dy: sy, f: |x, y| (x, y), pd: PhantomData::default() };
    let spi = Concentrated { dx: sxy, z: (0, 0), fa: |i_o, (x, y)| {
      if x*x + y*y < 1.0 { i_o.0 += 1 } else { i_o.1 += 1 }
      if i_o.0 + i_o.1 > samples { Some(4f64*(i_o.0 as f64/(i_o.0 + i_o.1) as f64)) } else { None }
    }, pd: Default::default() };

    spi.sample_iter(rng).take(10).for_each(|api| assert!(3.13 < api && api < 3.15) );
  }

  #[test]
  fn categorical_samples() {
    const samples: usize = 1000;
    let rng = StdRng::from_seed([0; 32]);
    let expected = [('b', 2usize), ('a', 10), ('c', 29), ('d', 100)];
    let cd = ratios(expected.into_iter());
    let hist = Histogram::from(cd.sample_iter(rng).take(samples*(10+2+29+100)));
    let achieved: Vec<(char, usize)> = hist.table().into_iter().map(|(k, c)|
      (*k, ((c as f64)/(samples as f64)).round() as usize)).collect();
    assert_eq!(&expected[..], &achieved[..]);
  }
}
