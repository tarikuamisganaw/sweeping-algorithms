
use std::collections::HashMap;
use std::hash::Hash;

pub trait Lattice: Sized {
    fn join(&self, other: &Self) -> Self;
    fn join_into(&mut self, other: Self) {
        *self = self.join(&other);
    }
    fn meet(&self, other: &Self) -> Self;
    fn bottom() -> Self;
    fn join_all(xs: &[&Self]) -> Self {
        xs.iter().rfold(Self::bottom(), |x, y| x.join(y))
    }
}

pub trait DistributiveLattice: Lattice {
    fn subtract(&self, other: &Self) -> Self;
}

pub(crate) trait PartialQuantale {
    fn prestrict(&self, other: &Self) -> Option<Self> where Self: Sized;
}

pub trait PartialDistributiveLattice: Lattice {
    /// GOAT, gotta document this.  `None` means complete subtraction, leaving an empty result
    //GOAT, we are also going to want a way to communicate "perfect copy of self"
    fn psubtract(&self, other: &Self) -> Option<Self> where Self: Sized;
}


impl <V : Lattice + Clone> Lattice for Option<V> {
    fn join(&self, other: &Option<V>) -> Option<V> {
        match self {
            None => { match other {
                None => { None }
                Some(r) => { Some(r.clone()) }
            } }
            Some(l) => match other {
                None => { Some(l.clone()) }
                Some(r) => { Some(l.join(r)) }
            }
        }
    }
    fn join_into(&mut self, other: Self) {
        match self {
            None => { match other {
                None => { }
                Some(r) => { *self = Some(r) }
            } }
            Some(l) => match other {
                None => { }
                Some(r) => { l.join_into(r) }
            }
        }
    }
    fn meet(&self, other: &Option<V>) -> Option<V> {
        match self {
            None => { None }
            Some(l) => {
                match other {
                    None => { None }
                    Some(r) => Some(l.meet(r))
                }
            }
        }
    }
    fn bottom() -> Self {
        None
    }
}

impl <V : PartialDistributiveLattice + Clone> PartialDistributiveLattice for Option<V> {
    fn psubtract(&self, other: &Self) -> Option<Self> {
        match self {
            None => { None }
            Some(s) => { match other {
                None => { Some(Some(s.clone())) }
                Some(o) => { Some(s.psubtract(o)) }
            } }
        }
    }
}

impl <V: Clone + Lattice> PartialQuantale for Option<V> {
    fn prestrict(&self, other: &Self) -> Option<Self> where Self: Sized {
        panic!()
    }
}

impl <V: PartialDistributiveLattice + Clone> DistributiveLattice for Option<V> {
    fn subtract(&self, other: &Self) -> Self {
        match self {
            None => { None }
            Some(s) => { match other {
                None => { Some(s.clone()) }
                Some(o) => { s.psubtract(o) }
            } }
        }
    }
}

impl <V: Lattice> Lattice for Box<V> {
    fn join(&self, other: &Self) -> Self {
        Box::new(self.as_ref().join(other.as_ref()))
    }

    fn meet(&self, other: &Self) -> Self {
        Box::new(self.as_ref().meet(other.as_ref()))
    }

    fn bottom() -> Self {
        Box::new(V::bottom())
    }
}

//TODO: Roll a macro to impl lattice across all the primitive types without a blanket impl

impl Lattice for &str {
    fn join(&self, _other: &Self) -> Self { self }
    fn meet(&self, _other: &Self) -> Self { self }
    fn bottom() -> Self { "" }
}

impl PartialDistributiveLattice for &str {
    fn psubtract(&self, other: &Self) -> Option<Self> where Self: Sized {
        if self == other { None }
        else { Some(*self) }
    }
}

impl PartialDistributiveLattice for () {
    fn psubtract(&self, _other: &Self) -> Option<Self> where Self: Sized {
        None
    }

}

impl Lattice for () {
    fn join(&self, _other: &Self) -> Self { () }
    fn meet(&self, _other: &Self) -> Self { () }
    fn bottom() -> Self { () }
}

impl Lattice for &() {
    fn join(&self, _other: &Self) -> Self { &() }
    fn meet(&self, _other: &Self) -> Self { &() }
    fn bottom() -> Self { &() }
}

impl Lattice for usize {
    fn join(&self, _other: &usize) -> usize { *self }
    fn meet(&self, _other: &usize) -> usize { *self }
    fn bottom() -> Self { 0 }
}

impl Lattice for &usize {
    fn join(&self, _other: &Self) -> Self { self }
    fn meet(&self, _other: &Self) -> Self { self }
    fn bottom() -> Self { &0 }
}

impl Lattice for u64 {
    fn join(&self, _other: &u64) -> u64 { *self }
    fn meet(&self, _other: &u64) -> u64 { *self }
    fn bottom() -> Self { 0 }
}

impl Lattice for &u64 {
    fn join(&self, _other: &Self) -> Self { self }
    fn meet(&self, _other: &Self) -> Self { self }
    fn bottom() -> Self { &0 }
}

impl PartialDistributiveLattice for u64 {
    fn psubtract(&self, other: &Self) -> Option<Self> where Self: Sized {
        if self == other { None }
        else { Some(*self) }
    }
}

impl Lattice for u32 {
    fn join(&self, _other: &u32) -> u32 { *self }
    fn meet(&self, _other: &u32) -> u32 { *self }
    fn bottom() -> Self { 0 }
}

impl Lattice for &u32 {
    fn join(&self, _other: &Self) -> Self { self }
    fn meet(&self, _other: &Self) -> Self { self }
    fn bottom() -> Self { &0 }
}

impl Lattice for u16 {
    fn join(&self, _other: &u16) -> u16 { *self }
    fn meet(&self, other: &u16) -> u16 { *other }
    fn bottom() -> Self { 0 }
}

impl Lattice for &u16 {
    fn join(&self, _other: &Self) -> Self { self }
    fn meet(&self, other: &Self) -> Self { other }
    fn bottom() -> Self { &0 }
}

impl PartialDistributiveLattice for u16 {
    fn psubtract(&self, other: &Self) -> Option<Self> where Self: Sized {
        if self == other { None }
        else { Some(*self) }
    }
}

impl Lattice for u8 {
    fn join(&self, _other: &u8) -> u8 { *self }
    fn meet(&self, _other: &u8) -> u8 { *self }
    fn bottom() -> Self { 0 }
}

impl Lattice for &u8 {
    fn join(&self, _other: &Self) -> Self { self }
    fn meet(&self, _other: &Self) -> Self { self }
    fn bottom() -> Self { &0 }
}

impl <K: Copy + Eq + Hash, V : Copy + Lattice> Lattice for HashMap<K, V> {
    fn join(&self, other: &HashMap<K, V>) -> HashMap<K, V> {
        let mut res = HashMap::<K, V>::new();
        for (key, value) in self.iter() {
            if !other.contains_key(key) {
                res.insert(*key, *value);
            }
        }
        for (key, value) in other.iter() {
            if !self.contains_key(key) {
                res.insert(*key, *value);
            }
        }
        for (key, value) in self.iter() {
            if other.contains_key(key) {
                res.insert(*key, value.join(other.get(key).unwrap()));
            }
        }
        return res
    }

    fn meet(&self, other: &HashMap<K, V>) -> HashMap<K, V> {
        let mut res = HashMap::<K, V>::new();
        for (key, value) in self.iter() {
            if other.contains_key(key) {
                res.insert(*key, value.join(other.get(key).unwrap()));
            }
        }
        return res;
    }

    fn bottom() -> Self {
        HashMap::new()
    }
}




// impl<V: Lattice + Clone> Lattice for Box<ByteTrieNode<V>> {
//     fn join(&self, other: &Self) -> Self {
//         Box::new((&**self).join(&**other))
//     }
//     fn meet(&self, other: &Self) -> Self {
//         Box::new((&**self).meet(&**other))
//     }
//     fn bottom() -> Self {
//         unreachable!()
//     }
// }

// impl<V: PartialDistributiveLattice + Clone> PartialDistributiveLattice for Box<ByteTrieNode<V>> {
//     fn psubtract(&self, other: &Self) -> Option<Self> {
//         (&**self).psubtract(&**other).map(|btn| Box::new(btn))
//     }
// }

// impl<V : Clone + Lattice> Lattice for ShortTrieMap<V> {
//     fn join(&self, other: &Self) -> Self {
//         Self {
//             root: self.root.join(&other.root),
//         }
//     }

//     fn join_into(&mut self, other: Self) {
//         self.root.join_into(other.root)
//     }

//     fn meet(&self, other: &Self) -> Self {
//         Self {
//             root: self.root.meet(&other.root),
//         }
//     }

//     fn bottom() -> Self {
//         ShortTrieMap::new()
//     }
// }

// impl<V : Clone + PartialDistributiveLattice> DistributiveLattice for ShortTrieMap<V> {
//     fn subtract(&self, other: &Self) -> Self {
//         Self {
//             root: self.root.subtract(&other.root),
//         }
//     }
// }
