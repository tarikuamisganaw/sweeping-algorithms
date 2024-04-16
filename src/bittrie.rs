use std::{iter, mem, ptr};
use std::ops::Range;
use std::path::Iter;
use crate::bytetrie::ShortTrieMap;

fn zero(i: u64, mask: u64) -> bool { (i & mask) == 0 }

fn mask(i: u64, mask: u64) -> u64 { i & (complement(mask - 1) ^ mask) }

fn hasMatch(key: u64, prefix: u64, m: u64) -> bool { mask(key, m) == prefix }

fn unsignedCompare(i: u64, j: u64) -> bool { (i < j) ^ (i < 0) ^ (j < 0) }

fn shorter(m1: u64, m2: u64) -> bool { unsignedCompare(m2, m1) }

fn complement(i: u64) -> u64 { !i }

fn bits(num: u64) -> impl Iterator<Item=bool> { (0..=63).rev().map(move |i| (num >> i & 1) != 0) }

fn bitString(num: u64, sep: String) -> String { bits(num).map(|b| if b { "1" } else { "0" }).collect::<Vec<_>>().join(&*sep) }

fn highestOneBit(mut n: u64) -> u64 {
    if n == 0 {
        return 0;
    }
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    n |= n >> 32;
    n - (n >> 1)
}

fn branchMask(i: u64, j: u64) -> u64 { highestOneBit(i ^ j) }


fn join<T: Clone>(p1: u64, t1: Box<BitTrieMap<T>>, p2: u64, t2: Box<BitTrieMap<T>>) -> BitTrieMap<T> {
    let m = branchMask(p1, p2);
    let p = mask(p1, m);
    if zero(p1, m) { BitTrieMap::Bin { prefix: p, mask: m, left: t1, right: t2 } } else { BitTrieMap::Bin { prefix: p, mask: m, left: t2, right: t1 } }
}

fn bin<T: Clone>(prefix: u64, mask: u64, left: Box<BitTrieMap<T>>, right: Box<BitTrieMap<T>>) -> BitTrieMap<T> {
    match (*left, *right) {
        (left, BitTrieMap::Nil {}) => { left }
        (BitTrieMap::Nil {}, right) => { right }
        (left, right) => { BitTrieMap::Bin { prefix, mask, left: Box::new(left), right: Box::new(right) } }
    }
}


#[derive(Clone,PartialEq)]
pub(crate) enum BitTrieMap<T> {
    Nil {},
    Tip { key: u64, value: T },
    Bin { prefix: u64, mask: u64, left: Box<BitTrieMap<T>>, right: Box<BitTrieMap<T>> },
}

// fn tip_with_value<V: Clone + Eq>(v: &BitTrieMap<V>, s: V) -> BitTrieMap<V> {
//     match v {
//         BitTrieMap::Tip { key, value } => {
//             if ptr::eq(ptr::from_ref(v), ptr::from_ref(&s)) { v.clone() } else { BitTrieMap::Tip { key: key, value: s } }
//         }
//         _ => { unreachable!() }
//     }
// }

// fn bin_with_children<V: Clone + Eq>(v: BitTrieMap<V>, l: Box<BitTrieMap<V>>, r: Box<BitTrieMap<V>>) -> BitTrieMap<V> {
//     match v {
//         BitTrieMap::Bin{prefix, mask, left, right} => {
//         if (left == l) && (right == r) { mem::transmute(v).clone() } else { BitTrieMap::Bin { prefix: prefix, mask: mask, left: l, right: r } }
//         }
//         _ => unreachable!()
//     }
// }

impl<V: Clone+Eq> FromIterator<(u64, V)> for BitTrieMap<V> {
    fn from_iter<I: IntoIterator<Item=(u64, V)>>(iter: I) -> Self {
        let mut tm = BitTrieMap::empty();
        for (k, v) in iter { tm = tm.updated(k, v); }
        tm
    }
}

// impl<V: Clone> Clone for BitTrieMap<V> {
//     fn clone(&self) -> Self {
//         self.iter().collect()
//     }
// }

impl<T: Eq + Clone> BitTrieMap<T> {
    pub(crate) fn empty() -> BitTrieMap<T> { BitTrieMap::Nil {} }

    fn single(key: u64, value: T) -> BitTrieMap<T> { BitTrieMap::Tip { key, value } }

    fn construct(elems: &[(u64, T)]) -> BitTrieMap<T> {
        elems.iter().fold(BitTrieMap::empty(), |mut acc, (key, value)| {
            acc.updated(*key, value.clone())
        })
    }

    pub(crate) fn iter<'a>(&'a self) -> impl Iterator<Item=(u64, T)> + 'a {
        match self {
            BitTrieMap::Nil {} => { BitTrieMapIterator::empty() }
            _ => { BitTrieMapIterator::new(self) }
        }
    }

    fn updatedWith<F: Fn(Option<T>) -> Option<T>>(self, k: u64, remap: F) -> BitTrieMap<T> {
        match self.get(k) {
            None => match remap(None) {
                None => { self }
                Some(v) => { self.updated(k, v) }
            }
            Some(v) => match remap(Some(v.clone())) {
                None => { self.removed(k) }
                Some(v_) => { if v == v_ { self } else { self.updated(k, v_) } }
            }
        }
    }

    fn isEmpty(self) -> bool { self == BitTrieMap::Nil {} }
    fn filter(&self, f: fn(u64, T) -> bool) -> &BitTrieMap<T> {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => {
                let newleft = left.filter(f);
                let newright = right.filter(f);
                if ptr::eq(Box::as_ref(left), newleft) && ptr::eq(Box::as_ref(right), newright) { self } else {
                    let r = Box::new(bin(*prefix, *mask, Box::from(newleft.clone()), Box::from(newright.clone())));
                    Box::leak(r)
                }
            }
            BitTrieMap::Tip { key, value } => {
                if f(*key, value.clone()) { self } else { &BitTrieMap::Nil{} }
            }
            BitTrieMap::Nil {} => { &BitTrieMap::Nil {} }
        }
    }

    fn mapValuesNow<S: Clone + Eq>(&self, f: fn(T) -> S) -> BitTrieMap<S> {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => { BitTrieMap::Bin { prefix: *prefix, mask: *mask, left: Box::from(left.mapValuesNow(f)), right: Box::from(right.mapValuesNow(f)) } }
            BitTrieMap::Tip { key, value } => { BitTrieMap::Tip { key: *key, value: f(value.clone()) } }
            BitTrieMap::Nil {} => BitTrieMap::Nil {}
        }
    }

    fn transform<S: Clone + Eq>(&self, f: fn(u64, T) -> S) -> BitTrieMap<S> {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => { BitTrieMap::Bin { prefix: *prefix, mask: *mask, left: Box::from(left.transform(f)), right: Box::from(right.transform(f)) } }
            BitTrieMap::Tip { key, value } => { BitTrieMap::Tip { key: *key, value: f(*key, value.clone()) } }
            BitTrieMap::Nil {} => { BitTrieMap::Nil {} }
        }
    }

    fn size(&self) -> u64 {
        match self {
            BitTrieMap::Nil {} => { 0 }
            BitTrieMap::Tip { key: _, value: _ } => { 1 }
            BitTrieMap::Bin { prefix: _, mask: _, left, right } => { left.size() + right.size() }
        }
    }

    pub(crate) fn contains(&self, key: u64) -> bool {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => {
                if zero(key, *mask) { left.contains(key) } else { right.contains(key) }
            }
            BitTrieMap::Tip { key: key2, value } => { key == *key2 }
            BitTrieMap::Nil {} => { false }
        }
    }

    pub(crate) fn get(&self, key: u64) -> Option<T> {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => {
                if zero(key, *mask)
                { left.get(key) } else { right.get(key) }
            }
            BitTrieMap::Tip { key: key2, value } => {
                if key == *key2
                { Some(value.clone()) } else { None }
            }
            BitTrieMap::Nil {} => { None }
        }
    }

    fn getOrElse<F: FnOnce() -> T>(&self, key: u64, default: F) -> T {
        match self {
            BitTrieMap::Nil{} => { default() }
            BitTrieMap::Tip { key: key2, value } => if key == *key2 { value.clone() } else { default() }
            BitTrieMap::Bin { prefix, mask, left, right } => {
                if zero(key, *mask)
                { left.getOrElse(key, default) } else { right.getOrElse(key, default) }
            }
        }
    }

    fn apply(&self, key: u64) -> T {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => if zero(key, *mask) { left.apply(key) } else { right.apply(key) }
            BitTrieMap::Tip { key: key2, value } => {
                if key == *key2
                { value.clone() } else { panic!("{}", key) }
            }
            BitTrieMap::Nil {} => panic!("{}", key)
        }
    }

    pub(crate) fn updated(self, key: u64, value: T) -> BitTrieMap<T> {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => {
                if !hasMatch(key, prefix, mask) { join(key, Box::new(BitTrieMap::Tip { key, value }), prefix, Box::new(BitTrieMap::Bin { prefix, mask, left, right })) } else if zero(key, mask) { BitTrieMap::Bin { prefix, mask, left: Box::new(left.updated(key, value)), right } } else { BitTrieMap::Bin { prefix, mask, left, right: Box::new(right.updated(key, value)) } }
            }
            BitTrieMap::Tip { key: key2, value: value2 } => {
                if key == key2 { BitTrieMap::Tip { key, value } } else { join(key, Box::new(BitTrieMap::Tip { key, value }), key2, Box::new(BitTrieMap::Tip { key: key2, value: value2 })) }
            }
            BitTrieMap::Nil {} => { BitTrieMap::Tip { key, value } }
        }
    }

    /**
     * Updates the map, using the provided function to resolve conflicts if the key is already present.
     *
     * Equivalent to:
     * {{{
     *   self.get(key) match {
     *     case None => self.update(key, value)
     *     case Some(oldvalue) => self.update(key, f(oldvalue, value)
     *   }
     * }}}
     *
     * @tparam S     The supertype of values in self `u64Map`.
     * @param key    The key to update
     * @param value  The value to use if there is no conflict
     * @param f      The function used to resolve conflicts.
     * @return       The updated map.
     */
    fn updatedWithDefault<F: FnOnce() -> T, FF: FnOnce(T) -> T>(self, key: u64, value: F, f: FF) -> BitTrieMap<T> {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => {
                if !hasMatch(key, prefix, mask)
                { join(key, Box::new(BitTrieMap::Tip { key, value: value() }), prefix, Box::new(BitTrieMap::Bin { prefix, mask, left, right })) } else if zero(key, mask)
                { BitTrieMap::Bin { prefix, mask, left: Box::from(left.updatedWithDefault(key, value, f)), right } } else { BitTrieMap::Bin { prefix, mask, left, right: Box::from(right.updatedWithDefault(key, value, f)) } }
            }
            BitTrieMap::Tip { key: key2, value: value2 } =>
                {
                    if key == key2
                    { BitTrieMap::Tip { key, value: f(value2) } } else { join(key, Box::new(BitTrieMap::Tip { key, value: value() }), key2, Box::new(BitTrieMap::Tip { key: key2, value: value2 })) }
                }
            BitTrieMap::Nil {} => { BitTrieMap::Tip { key, value: value() } }
        }
    }

    pub(crate) fn removed(self, key: u64) -> BitTrieMap<T> {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } =>
                if !hasMatch(key, prefix, mask) { bin(prefix, mask, left, right) } else if zero(key, mask) { bin(prefix, mask, Box::from(left.removed(key)), right) } else { bin(prefix, mask, left, Box::from(right.removed(key))) }
            BitTrieMap::Tip { key: key2, value: _ } =>
                if key == key2 { BitTrieMap::Nil {} } else { self }
            BitTrieMap::Nil {} => BitTrieMap::Nil {}
        }
    }

    /**
     * A combined transform and filter function. Returns an `u64Map` such that
     * for each `(key, value)` mapping in self map, if `f(key, value) == None`
     * the map contains no mapping for key, and if `f(key, value)`.
     *
     * @tparam S  The type of the values in the resulting `u64Map`.
     * @param f   The transforming function.
     * @return    The modified map.
     */
    fn modifyOrRemove(self, f: fn(u64, T) -> Option<T>) -> BitTrieMap<T> {
        match self {
            BitTrieMap::Bin { prefix, mask, left, right } => {
                let newleft = Box::from(left.modifyOrRemove(f));
                let newright = Box::from(right.modifyOrRemove(f));
                // if ptr::eq(&*left, &*newleft) && ptr::eq(&*right, &*newright) { self.clone() } else { bin(prefix, mask, newleft, newright) }
                bin(prefix, mask, newleft, newright)
            }
            BitTrieMap::Tip { key, ref value } => match f(key, value.clone()) {
                None =>
                    { BitTrieMap::Nil {} }
                Some(ref value2) =>
                //hack to preserve sharing
                    if value == value2 { self.clone() } else { BitTrieMap::Tip { key, value: value2.clone() } }
            }
            BitTrieMap::Nil {} =>
                { BitTrieMap::Nil {} }
        }
    }

    /**
     * Forms a union map with that map, using the combining function to resolve conflicts.
     *
     * @tparam S      The type of values in `that`, a supertype of values in `self`.
     * @param that    The map to form a union with.
     * @param f       The function used to resolve conflicts between two mappings.
     * @return        Union of `self` and `that`, with identical key conflicts resolved using the function `f`.
     */
    pub(crate) fn union_with(self: Box<BitTrieMap<T>>, that: Box<BitTrieMap<T>>, f: fn(u64, T, T) -> T) -> BitTrieMap<T> {
        match (*self.clone(), *that.clone()) {
            (BitTrieMap::Bin { prefix: p1, mask: m1, left: l1, right: r1 }, (BitTrieMap::Bin { prefix: p2, mask: m2, left: l2, right: r2 })) => {
                if shorter(m1, m2) {
                    if !hasMatch(p2, p1, m1) { join(p1, self.clone(), p2, that.clone()) } else if zero(p2, m1) { BitTrieMap::Bin { prefix: p1, mask: m1, left: Box::from(l1.union_with(that.clone(), f)), right: r1 } } else { BitTrieMap::Bin { prefix: p1, mask: m1, left: l1, right: Box::from(r1.union_with(that.clone(), f)) } }
                } else if shorter(m2, m1) {
                    if !hasMatch(p1, p2, m2) { join(p1, self.clone(), p2, that.clone()) } else if zero(p1, m2) { BitTrieMap::Bin { prefix: p2, mask: m2, left: Box::from(self.clone().union_with(l2, f)), right: r2 } } else { BitTrieMap::Bin { prefix: p2, mask: m2, left: l2, right: Box::from(self.clone().union_with(r2, f)) } }
                } else {
                    if p1 == p2 { BitTrieMap::Bin { prefix: p1, mask: m1, left: Box::from(l1.union_with(l2, f)), right: Box::from(r1.union_with(r2, f)) } } else { join(p1, self.clone(), p2, that.clone()) }
                }
            }
            (BitTrieMap::Tip { key, value }, x) => { x.updatedWithDefault(key, || value.clone(),  |t| f(key, value.clone(), t)) }
            (x, BitTrieMap::Tip { key, value }) => { x.updatedWithDefault(key, || value.clone(), |t| f(key, t, value.clone())) }
            (BitTrieMap::Nil {}, x) => { x }
            (x, BitTrieMap::Nil {}) => { x }
        }
    }

    /**
     * Forms the intersection of these two maps with a combining function. The
     * resulting map is a map that has only keys present in both maps and has
     * values produced from the original mappings by combining them with `f`.
     *
     * @tparam S      The type of values in `that`.
     * @tparam R      The type of values in the resulting `u64Map`.
     * @param that    The map to intersect with.
     * @param f       The combining function.
     * @return        Intersection of `self` and `that`, with values for identical keys produced by function `f`.
     */
    pub(crate) fn intersection_with(self: Box<BitTrieMap<T>>, that: Box<BitTrieMap<T>>, f: fn(u64, T, T) -> T) -> BitTrieMap<T> {
        match (*self.clone(), *that.clone()) {
            (BitTrieMap::Bin { prefix: p1, mask: m1, left: l1, right: r1 }, (BitTrieMap::Bin { prefix: p2, mask: m2, left: l2, right: r2 })) => {
                if (shorter(m1, m2)) {
                    if (!hasMatch(p2, p1, m1)) { BitTrieMap::empty() } else if (zero(p2, m1)) { l1.intersection_with(that, f) } else { r1.intersection_with(that, f) }
                } else if (m1 == m2) { bin(p1, m1, Box::from(l1.intersection_with(l2, f)), Box::from(r1.intersection_with(r2, f))) } else {
                    if (!hasMatch(p1, p2, m2)) { BitTrieMap::empty() } else if (zero(p1, m2)) { self.intersection_with(l2, f) } else { self.intersection_with(r2, f) }
                }
            }
            (BitTrieMap::Tip { key, value }, x) => {
                match that.get(key) {
                    None => { BitTrieMap::empty() }
                    Some(value2) => { BitTrieMap::Tip { key, value: f(key, value, value2) } }
                }
            }
            (x, BitTrieMap::Tip { key, value }) => {
                match self.get(key) {
                    None => { BitTrieMap::empty() }
                    Some(value2) => { BitTrieMap::Tip { key, value: f(key, value2, value) } }
                }
            }
            _ => { BitTrieMap::empty() }
        }
    }
    //
    // def subtractWith[S >: T](p: (S, S) => Option<S>)(m2: BitTrieMap<S>) -> BitTrieMap<S> =
    //   var n = BitTrieMap::empty<S>
    //   if self.isEmpty then n
    //   else
    //     self.foreachEntry((k, v) =>
    //       m2.get(k) match
    //         case None => n = n.updated(k, v)
    //         case Some(v_) =>
    //           p(v, v_) match
    //             case Some(r) => n = n.updated(k, r)
    //             case None => ()
    //     )
    //     n
    //

    /**
     * Left biased intersection. Returns the map that has all the same mappings
     * as self but only for keys which are present in the other map.
     *
     * @tparam R      The type of values in `that`.
     * @param that    The map to intersect with.
     * @return        A map with all the keys both in `self` and `that`, mapped to corresponding values from `self`.
     */
    // fn intersection[R](that: BitTrieMap[R]) -> BitTrieMap<T> =
    //   self.intersection_with(that, (key: u64, value: T, value2: R) => value)
    //
    // fn union[S >: T](that: BitTrieMap<S>) -> BitTrieMap<S> =
    //   self.union_with<S>(that, (key, x, _) => x)
    //
    // fn subtract[S >: T](that: BitTrieMap<S>) -> BitTrieMap<S> =
    //   if self.isEmpty then BitTrieMap::empty
    //   else self.filter((k, _) => !that.contains(k))

    /**
     * The entry with the lowest key value considered in unsigned order.
     */
    fn firstKey(&self) -> u64 {
        match self {
            BitTrieMap::Bin { prefix: _, mask: _, left, right } => { left.firstKey() }
            BitTrieMap::Tip { key, value } => { *key }
            BitTrieMap::Nil {} => panic!("Empty set")
        }
    }

    /**
     * The entry with the highest key value considered in unsigned order.
     */
    fn lastkey(&self) -> u64 {
        match self {
            BitTrieMap::Bin { prefix: _, mask: _, left, right } => { right.lastkey() }
            BitTrieMap::Tip { key, value } => { *key }
            BitTrieMap::Nil {} => panic!("Empty set")
        }
    }


// fn fromZip[V](keys: Array[u64], values: Array[V]) -> BitTrieMap[V] =
// val sz = math.min(keys.length, values.length)
// var lm = BitTrieMap::empty[V]
// var i = 0
// while (i < sz) { lm = lm.updated(keys(i), values(i)); i += 1 }
// lm

// Important! Without self equals method in place, an infinite
// loop from Map.equals => size => pattern-match-on-Nil => equals
// develops.  Case objects and custom equality don't mix without
// careful handling.
//    def equals(that : Any) = that match {
//      case Nil => true
//      case _ => false
//    }
}

// Iterator over a non-empty u64Map.
struct BitTrieMapIterator<'a, V> where V: Clone {
    it: &'a BitTrieMap<V>,
    index: usize,
    buffer: [*const u8; 65],
}

impl<'a, V: Clone> BitTrieMapIterator<'a, V> {
    fn new(it: &'a BitTrieMap<V>) -> Self {
        let mut r = Self {
            it,
            index: 0,
            buffer: [0 as *const u8; 65],
        };
        r.push(it);
        r
    }

    fn empty() -> Self {
        Self {
            it: &BitTrieMap::Nil {},
            index: 0,
            buffer: [0 as *const u8; 65],
        }
    }

    fn pop(&mut self) -> &'a BitTrieMap<V> {
        self.index -= 1;
        return unsafe { (self.buffer[self.index] as *const BitTrieMap<V>).as_ref().unwrap() };
    }

    fn push(&mut self, x: &BitTrieMap<V>) -> () {
        self.buffer[self.index] = (x as *const BitTrieMap<V>) as *const u8;
        self.index += 1;
    }

    fn value_of(tip: BitTrieMap<V>) -> (u64, V) {
        match tip {
            BitTrieMap::Tip { key, value } => { (key, value) }
            _ => unreachable!()
        }
    }
}

impl<'a, V: Clone> Iterator for BitTrieMapIterator<'a, V> {
    type Item = (u64, V);

    fn next(&mut self) -> Option<(u64, V)> {
        if self.index == 0 { return None; } else {
            match self.pop() {
                BitTrieMap::Bin { prefix: _, mask: _, left: t, right } if matches!(**t, BitTrieMap::Tip { .. }) => {
                    self.push(right);
                    match (*t).as_ref() {
                        BitTrieMap::Tip { key, value } => { Some((*key, value.clone())) }
                        _ => { unreachable!() }
                    }
                }
                BitTrieMap::Bin { prefix: _, mask: _, left, right } => {
                    self.push(left);
                    self.push(right);
                    self.next()
                }
                t @ BitTrieMap::Tip { key, value } => { Some((*key, value.clone())) }
                BitTrieMap::Nil {} => { unreachable!() }
            }
        }
    }
}


// class BitTrieMapEntryIterator[V](it: BitTrieMap[V]) extends BitTrieMapIterator[V, (u64, V)](it) {
// fn value_of(tip: BitTrieMap::Tip[V]) = (tip.key, tip.value)
// }
//
// class BitTrieMapValueIterator[V](it: BitTrieMap[V]) extends BitTrieMapIterator[V, V](it) {
// fn value_of(tip: BitTrieMap::Tip[V]) = tip.value
// }
//
// class BitTrieMapKeyIterator[V](it: BitTrieMap[V]) extends BitTrieMapIterator[V, u64](it) {
// fn value_of(tip: BitTrieMap::Tip[V]) = tip.key
// }


// fn foreach[U](f: ((u64, T)) => U) -> Unit = self match {
// BitTrieMap::Bin(_, _, left, right) => { left.foreach(f); right.foreach(f) }
// BitTrieMap::Tip(key, value) => f((key, value))
// BitTrieMap::Nil =>
// }
//
// fn foreachEntry[U](f: (u64, T) => U) -> Unit = self match {
// BitTrieMap::Bin(_, _, left, right) => { left.foreachEntry(f); right.foreachEntry(f) }
// BitTrieMap::Tip(key, value) => f(key, value)
// BitTrieMap::Nil =>
// }
//
// fn keysIterator: Iterator[u64] = self match {
// BitTrieMap::Nil => Iterator.empty
// case _ => new BitTrieMapKeyIterator(self)
// }

// fn foreachKey[U](f: u64 => U) -> Unit = self match {
// BitTrieMap::Bin(_, _, left, right) => { left.foreachKey(f); right.foreachKey(f) }
// BitTrieMap::Tip(key, _) => f(key)
// BitTrieMap::Nil =>
// }
//
// fn valuesIterator: Iterator<T> = self match {
// BitTrieMap::Nil => Iterator.empty
// case _ => new BitTrieMapValueIterator(self)
// }

// fn foreachValue[U](f: T => U) -> Unit = self match {
// BitTrieMap::Bin(_, _, left, right) => { left.foreachValue(f); right.foreachValue(f) }
// BitTrieMap::Tip(_, value) => f(value)
// BitTrieMap::Nil =>
// }

