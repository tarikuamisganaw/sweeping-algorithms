use std::marker::PhantomData;

fn zero(i: u64, mask: u64) -> bool { (i & mask) == 0 }

fn mask(i: u64, mask: u64) -> u64 { i & (!(mask - 1) ^ mask) }

fn has_match(key: u64, prefix: u64, m: u64) -> bool { mask(key, m) == prefix }

fn unsigned_compare(i: u64, j: u64) -> bool { (i < j) ^ (i < 0) ^ (j < 0) }

fn shorter(m1: u64, m2: u64) -> bool { unsigned_compare(m2, m1) }

fn bits(num: u64) -> impl Iterator<Item=bool> { (0..=63).rev().map(move |i| (num >> i & 1) != 0) }

fn bit_string(num: u64, sep: String) -> String { bits(num).map(|b| if b { "1" } else { "0" }).collect::<Vec<_>>().join(&*sep) }

fn highest_one_bit(mut n: u64) -> u64 {
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

fn branch_mask(i: u64, j: u64) -> u64 { highest_one_bit(i ^ j) }

type Label = u32;
type Index = u32;
pub(crate) trait Value: Eq + Copy + From<u64> + Into<u64> {}

pub(crate) static mut MEM: *mut u64 = 0u64 as *mut u64;
pub(crate) static mut CNT: isize = 0;

const NIL: Label = 0;
const TIP: Label = 1;
const BIN: Label = 2;

fn alloc_bin<T : Value>(prefix: u64, mask: u64, left: BitTrieMap<T>, right: BitTrieMap<T>) -> BitTrieMap<T> {
    unsafe {
        let i = CNT;
        MEM.offset(CNT).write(prefix);
        MEM.offset(CNT + 1).write(mask);
        MEM.offset(CNT + 2).write(left.0);
        MEM.offset(CNT + 3).write(right.0);
        CNT += 4;
        return BitTrieMap::pack(BIN, i as Index);
    }
}

fn alloc_tip<T : Value>(key: u64, value: T) -> BitTrieMap<T> {
    unsafe {
        let i = CNT;
        MEM.offset(CNT).write(key);
        MEM.offset(CNT + 1).write(value.into());
        CNT += 2;
        return BitTrieMap::pack(TIP, i as Index);
    }
}

fn get_key<T : Value>(i: BitTrieMap<T>) -> u64 { unsafe { *MEM.offset(i.index() as isize) } }
fn get_value<T : Value>(i: BitTrieMap<T>) -> T { unsafe { T::from(*MEM.offset(i.index() as isize + 1)) } }
fn get_prefix<T : Value>(i: BitTrieMap<T>) -> u64 { unsafe { *MEM.offset(i.index() as isize) } }
fn get_mask<T : Value>(i: BitTrieMap<T>) -> u64 { unsafe { *MEM.offset(i.index() as isize + 1) } }
fn get_left<T : Value>(i: BitTrieMap<T>) -> BitTrieMap<T> { unsafe { BitTrieMap(*MEM.offset(i.index() as isize + 2), PhantomData) } }
fn get_right<T : Value>(i: BitTrieMap<T>) -> BitTrieMap<T> { unsafe { BitTrieMap(*MEM.offset(i.index() as isize + 3), PhantomData) } }

fn bin<T : Value>(prefix: u64, mask: u64, left: BitTrieMap<T>, right: BitTrieMap<T>) -> BitTrieMap<T> {
    match (left.label(), right.label()) {
        (_, NIL) => { left }
        (NIL, _) => { right }
        _ => { alloc_bin(prefix, mask, left, right) }
    }
}

fn join<T : Value>(p1: u64, t1: BitTrieMap<T>, p2: u64, t2: BitTrieMap<T>) -> BitTrieMap<T> {
    let m = branch_mask(p1, p2);
    let p = mask(p1, m);
    if zero(p1, m) {
        alloc_bin(p, m, t1, t2)
    } else {
        alloc_bin(p, m, t2, t1)
    }
}


#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) struct BitTrieMap<T>(u64, PhantomData<T>);

// becomes useful with mapValuesNow and transform
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
//         if (left == l) && (right == r) { MEM::transmute(v).clone() } else { BitTrieMap::Bin { prefix: prefix, mask: mask, left: l, right: r } }
//         }
//         _ => unreachable!()
//     }
// }

impl<V : Value> FromIterator<(u64, V)> for BitTrieMap<V> {
    fn from_iter<I: IntoIterator<Item=(u64, V)>>(iter: I) -> Self {
        let mut tm: BitTrieMap<V> = BitTrieMap::empty();
        for (k, v) in iter { tm = tm.updated(k, v); }
        tm
    }
}

// I don't think Clone is useful with the current allocation scheme
// impl<V: Clone> Clone for BitTrieMap<V> {
//     fn clone(&self) -> Self {
//         self.iter().collect()
//     }
// }

impl<T : Value> BitTrieMap<T> {
    fn label(self) -> Label { (self.0 >> 32) as u32 }
    fn index(self) -> Index { self.0 as u32 }
    fn pack(label: Label, index: Index) -> BitTrieMap<T> { BitTrieMap(((label as u64) << 32) | (index as u64), PhantomData) }

    pub(crate) fn empty() -> BitTrieMap<T> { BitTrieMap::pack(NIL, 0) }

    fn single(key: u64, value: T) -> BitTrieMap<T> { alloc_tip(key, value) }

    fn construct(elems: &[(u64, T)]) -> BitTrieMap<T> {
        elems.iter().fold(BitTrieMap::empty(), |mut acc, (key, value)| {
            acc.updated(*key, value.clone())
        })
    }

    pub(crate) fn iter(self) -> impl Iterator<Item=(u64, T)> {
        match self.label() {
            NIL => { BitTrieMapIterator::empty() }
            _ => { BitTrieMapIterator::new(self) }
        }
    }

    // todo
    // fn updated_with<F: Fn(Option<T>) -> Option<T>>(self, k: u64, remap: F) -> BitTrieMap<T> {
    //     match self.get(k) {
    //         None => match remap(None) {
    //             None => { self }
    //             Some(v) => { self.updated(k, v) }
    //         }
    //         Some(v) => match remap(Some(v.clone())) {
    //             None => { self.removed(k) }
    //             Some(v_) => { if v == v_ { self } else { self.updated(k, v_) } }
    //         }
    //     }
    // }

    fn is_empty(self) -> bool { self.label() == NIL }
    fn filter(self, f: fn(u64, T) -> bool) -> BitTrieMap<T> {
        match self.label() {
            BIN => {
                let newleft = get_left(self).filter(f);
                let newright = get_right(self).filter(f);
                if (get_left(self) == newleft) && (get_right(self) == newright) { self }
                else { bin(get_prefix(self), get_mask(self), newleft, newright) }
            }
            TIP => {
                if f(get_key(self), get_value(self)) { self }
                else { BitTrieMap::empty() }
            }
            NIL => { BitTrieMap::empty() }
            _ => unreachable!()
        }
    }

    // todo
    // fn mapValuesNow<S: Clone + Eq>(&self, f: fn(T) -> S) -> BitTrieMap<S> {
    //     match self {
    //         BitTrieMap::Bin { prefix, mask, left, right } => { BitTrieMap::Bin { prefix: *prefix, mask: *mask, left: Box::from(left.mapValuesNow(f)), right: Box::from(right.mapValuesNow(f)) } }
    //         BitTrieMap::Tip { key, value } => { BitTrieMap::Tip { key: *key, value: f(value.clone()) } }
    //         BitTrieMap::Nil {} => BitTrieMap::Nil {}
    //     }
    // }

    // todo
    // fn transform<S: Clone + Eq>(&self, f: fn(u64, T) -> S) -> BitTrieMap<S> {
    //     match self {
    //         BitTrieMap::Bin { prefix, mask, left, right } => { BitTrieMap::Bin { prefix: *prefix, mask: *mask, left: Box::from(left.transform(f)), right: Box::from(right.transform(f)) } }
    //         BitTrieMap::Tip { key, value } => { BitTrieMap::Tip { key: *key, value: f(*key, value.clone()) } }
    //         BitTrieMap::Nil {} => { BitTrieMap::Nil {} }
    //     }
    // }

    // todo
    // fn size(&self) -> u64 {
    //     match self {
    //         BitTrieMap::Nil {} => { 0 }
    //         BitTrieMap::Tip { key: _, value: _ } => { 1 }
    //         BitTrieMap::Bin { prefix: _, mask: _, left, right } => { left.size() + right.size() }
    //     }
    // }

    pub(crate) fn contains(self, key: u64) -> bool {
        match self.label() {
            BIN => {
                if zero(key, get_mask(self)) { get_left(self).contains(key) }
                else { get_right(self).contains(key) }
            }
            TIP => { key == get_key(self) }
            NIL => { false }
            _ => unreachable!()
        }
    }

    pub(crate) fn get(self, key: u64) -> Option<T> {
        match self.label() {
            BIN => {
                if zero(key, get_mask(self)) { get_left(self).get(key) }
                else { get_right(self).get(key) }
            }
            TIP => {
                if key == get_key(self) { Some(get_value(self)) }
                else { None }
            }
            NIL => { None }
            _ => unreachable!()
        }
    }

    // todo
    // fn getOrElse<F: FnOnce() -> T>(&self, key: u64, default: F) -> T {
    //     match self {
    //         BitTrieMap::Nil{} => { default() }
    //         BitTrieMap::Tip { key: key2, value } => if key == *key2 { value.clone() } else { default() }
    //         BitTrieMap::Bin { prefix, mask, left, right } => {
    //             if zero(key, *mask) { left.getOrElse(key, default) }
    //             else { right.getOrElse(key, default) }
    //         }
    //     }
    // }

    // todo
    // fn apply(&self, key: u64) -> T {
    //     match self {
    //         BitTrieMap::Bin { prefix, mask, left, right } => if zero(key, *mask) { left.apply(key) } else { right.apply(key) }
    //         BitTrieMap::Tip { key: key2, value } => {
    //             if key == *key2
    //             { value.clone() } else { panic!("{}", key) }
    //         }
    //         BitTrieMap::Nil {} => panic!("{}", key)
    //     }
    // }

    pub(crate) fn updated(self, key: u64, value: T) -> BitTrieMap<T> {
        match self.label() {
            BIN => {
                let (prefix, mask) = (get_prefix(self), get_mask(self));
                if !has_match(key, prefix, mask) { join(key, alloc_tip(key, value), prefix, self) }
                else if zero(key, mask) { alloc_bin(prefix, mask, get_left(self).updated(key, value), get_right(self)) }
                else { alloc_bin(prefix, mask, get_left(self), get_right(self).updated(key, value)) }
            }
            TIP => {
                if key == get_key(self) { alloc_tip(key, value) }
                else { join(key, alloc_tip(key, value), get_key(self), self) }
            }
            NIL => { alloc_tip(key, value) }
            _ => unreachable!()
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
    fn updated_with_default<F: FnOnce() -> T, FF: FnOnce(T) -> T>(self, key: u64, value: F, f: FF) -> BitTrieMap<T> {
        match self.label() {
            BIN => {
                let (prefix, mask) = (get_prefix(self), get_mask(self));
                if !has_match(key, prefix, mask) { join(key, alloc_tip(key, value()), prefix, self) }
                else if zero(key, mask) { alloc_bin(prefix, mask, get_left(self).updated_with_default(key, value, f), get_right(self)) }
                else { alloc_bin(prefix, mask, get_left(self), get_right(self).updated_with_default(key, value, f)) }
            }
            TIP => {
                if key == get_key(self) { alloc_tip(key, f(get_value(self))) }
                else { join(key, alloc_tip(key, value()), get_key(self), self) }
            }
            NIL => { alloc_tip(key, value()) }
            _ => unreachable!()
        }
    }

    pub(crate) fn removed(self, key: u64) -> BitTrieMap<T> {
        match self.label() {
            BIN => {
                let (prefix, mask) = (get_prefix(self), get_mask(self));
                if !has_match(key, prefix, mask) { self }
                else if zero(key, mask) { bin(prefix, mask, get_left(self).removed(key), get_right(self)) }
                else { bin(prefix, mask, get_left(self), get_right(self).removed(key)) }
            }
            TIP => {
                if key == get_key(self) { BitTrieMap::empty() }
                else { self }
            }
            NIL => { BitTrieMap::empty() }
            _ => unreachable!()
        }
    }

    // /**
    //  * A combined transform and filter function. Returns an `u64Map` such that
    //  * for each `(key, value)` mapping in self map, if `f(key, value) == None`
    //  * the map contains no mapping for key, and if `f(key, value)`.
    //  *
    //  * @tparam S  The type of the values in the resulting `u64Map`.
    //  * @param f   The transforming function.
    //  * @return    The modified map.
    //  */
    // todo
    // fn modifyOrRemove(self, f: fn(u64, T) -> Option<T>) -> BitTrieMap<T> {
    //     match self {
    //         BitTrieMap::Bin { prefix, mask, left, right } => {
    //             let newleft = Box::from(left.modifyOrRemove(f));
    //             let newright = Box::from(right.modifyOrRemove(f));
    //             // if ptr::eq(&*left, &*newleft) && ptr::eq(&*right, &*newright) { self.clone() } else { bin(prefix, mask, newleft, newright) }
    //             bin(prefix, mask, newleft, newright)
    //         }
    //         BitTrieMap::Tip { key, ref value } => match f(key, value.clone()) {
    //             None =>
    //                 { BitTrieMap::Nil {} }
    //             Some(ref value2) =>
    //             //hack to preserve sharing
    //                 if value == value2 { self.clone() } else { BitTrieMap::Tip { key, value: value2.clone() } }
    //         }
    //         BitTrieMap::Nil {} =>
    //             { BitTrieMap::Nil {} }
    //     }
    // }

    /**
     * Forms a union map with that map, using the combining function to resolve conflicts.
     *
     * @tparam S      The type of values in `that`, a supertype of values in `self`.
     * @param that    The map to form a union with.
     * @param f       The function used to resolve conflicts between two mappings.
     * @return        Union of `self` and `that`, with identical key conflicts resolved using the function `f`.
     */
    pub(crate) fn union_with(self: BitTrieMap<T>, other: BitTrieMap<T>, f: fn(u64, T, T) -> T) -> BitTrieMap<T> {
        match (self.label(), other.label()) {
            (BIN, BIN) => {
                let (p1, p2, m1, m2) = (get_prefix(self), get_prefix(other), get_mask(self), get_mask(other));
                if shorter(m1, m2) {
                    if !has_match(p2, p1, m1) { join(p1, self, p2, other) }
                    else if zero(p2, m1) { alloc_bin(p1, m1, get_left(self).union_with(other, f), get_right(self)) }
                    else { alloc_bin(p1, m1, get_left(self), get_right(self).union_with(other, f)) }
                } else if shorter(m2, m1) {
                    if !has_match(p1, p2, m2) { join(p1, self, p2, other) }
                    else if zero(p1, m2) { alloc_bin(p2, m2, self.union_with(get_left(other), f), get_right(other)) }
                    else { alloc_bin(p2, m2, get_left(other), self.union_with(get_right(other), f)) }
                } else {
                    if p1 == p2 { alloc_bin(p1, m1, get_left(self).union_with(get_left(other), f), get_right(self).union_with(get_right(other), f)) }
                    else { join(p1, self, p2, other) }
                }
            }
            (TIP, _) => { other.updated_with_default(get_key(self), || get_value(self), |t| f(get_key(self), get_value(self), t)) }
            (_, TIP) => { self.updated_with_default(get_key(self), || get_value(self), |t| f(get_key(self), t, get_value(self))) }
            (NIL, _) => { other }
            (_, NIL) => { self }
            _ => unreachable!()
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
    pub(crate) fn intersection_with(self: BitTrieMap<T>, other: BitTrieMap<T>, f: fn(u64, T, T) -> T) -> BitTrieMap<T> {
        match (self.label(), other.label()) {
            (BIN, BIN) => {
                let (m1, m2) = (get_mask(self), get_mask(other));
                if shorter(m1, m2) {
                    if !has_match(get_prefix(other), get_prefix(self), m1) { BitTrieMap::empty() }
                    else if zero(get_prefix(other), m1) { get_left(self).intersection_with(other, f) }
                    else { get_right(self).intersection_with(other, f) }
                }
                else if m1 == m2 { bin(get_prefix(self), m1, get_left(self).intersection_with(get_left(other), f), get_right(self).intersection_with(get_right(other), f)) }
                else {
                    if !has_match(get_prefix(self), get_prefix(other), m2) { BitTrieMap::empty() }
                    else if zero(get_prefix(self), m2) { self.intersection_with(get_left(other), f) }
                    else { self.intersection_with(get_right(other), f) }
              }
            }
            (TIP, _) => { 
                match other.get(get_key(self)) {
                    None => { BitTrieMap::empty() }
                    Some(value2) => alloc_tip(get_key(self), f(get_key(self), get_value(self), value2))
                }
            }
            (_, TIP) => {
                match self.get(get_key(other)) {
                    None => { BitTrieMap::empty() }
                    Some(value2) => alloc_tip(get_key(other), f(get_key(other), value2, get_value(other)))
                }
            }
            (NIL, _) => { BitTrieMap::empty() }
            (_, NIL) => { BitTrieMap::empty() }
            _ => unreachable!()
        }
    }

    // todo
    // def subtractWith[S >: T](p: (S, S) => Option<S>)(m2: BitTrieMap<S>) -> BitTrieMap<S> =
    //   var n = BitTrieMap::empty<S>
    //   if self.is_empty then n
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

    // /**
    //  * Left biased intersection. Returns the map that has all the same mappings
    //  * as self but only for keys which are present in the other map.
    //  *
    //  * @tparam R      The type of values in `that`.
    //  * @param that    The map to intersect with.
    //  * @return        A map with all the keys both in `self` and `that`, mapped to corresponding values from `self`.
    //  */
    // todo
    // fn intersection[R](that: BitTrieMap[R]) -> BitTrieMap<T> =
    //   self.intersection_with(that, (key: u64, value: T, value2: R) => value)
    //
    // todo
    // fn union[S >: T](that: BitTrieMap<S>) -> BitTrieMap<S> =
    //   self.union_with<S>(that, (key, x, _) => x)
    //
    // todo
    // fn subtract[S >: T](that: BitTrieMap<S>) -> BitTrieMap<S> =
    //   if self.is_empty then BitTrieMap::empty
    //   else self.filter((k, _) => !that.contains(k))

    // /**
    //  * The entry with the lowest key value considered in unsigned order.
    //  */
    // todo
    // fn firstKey(&self) -> u64 {
    //     match self {
    //         BitTrieMap::Bin { prefix: _, mask: _, left, right } => { left.firstKey() }
    //         BitTrieMap::Tip { key, value } => { *key }
    //         BitTrieMap::Nil {} => panic!("Empty set")
    //     }
    // }

    // /**
    //  * The entry with the highest key value considered in unsigned order.
    //  */
    // todo
    // fn lastkey(&self) -> u64 {
    //     match self {
    //         BitTrieMap::Bin { prefix: _, mask: _, left, right } => { right.lastkey() }
    //         BitTrieMap::Tip { key, value } => { *key }
    //         BitTrieMap::Nil {} => panic!("Empty set")
    //     }
    }


// todo
// fn fromZip[V](keys: Array[u64], values: Array[V]) -> BitTrieMap[V] =
// val sz = math.min(keys.length, values.length)
// var lm = BitTrieMap::empty[V]
// var i = 0
// while (i < sz) { lm = lm.updated(keys(i), values(i)); i += 1 }
// lm


struct BitTrieMapIterator<V> where V : Value {
    it: BitTrieMap<V>,
    index: usize,
    buffer: [u64; 65],
}

impl<V : Value> BitTrieMapIterator<V> {
    fn new(it: BitTrieMap<V>) -> Self {
        let mut r = Self {
            it,
            index: 0,
            buffer: [0; 65],
        };
        r.push(it);
        r
    }

    fn empty() -> Self {
        Self {
            it: BitTrieMap::<V>::empty(),
            index: 0,
            buffer: [0; 65],
        }
    }

    fn pop(&mut self) -> BitTrieMap<V> {
        self.index -= 1;
        return unsafe { BitTrieMap::<V>(self.buffer[self.index], PhantomData) };
    }

    fn push(&mut self, x: BitTrieMap<V>) -> () {
        self.buffer[self.index] = x.0;
        self.index += 1;
    }

    fn value_of(tip: BitTrieMap<V>) -> (u64, V) {
        match tip.label() {
            TIP => { (get_key(tip), get_value(tip)) }
            _ => unreachable!()
        }
    }
}

impl <V : Value> Iterator for BitTrieMapIterator<V> {
    type Item = (u64, V);

    fn next(&mut self) -> Option<(u64, V)> {
        if self.index == 0 { return None; }
        else {
            let x = self.pop();
            match x.label() {
                BIN => {
                    let l = get_left(x);
                    if get_left(x).label() == TIP {
                        self.push(get_right(x));
                        Some((get_key(l), get_value(l)))
                    } else {
                        self.push(get_left(x));
                        self.push(get_right(x));
                        self.next()
                    }
                }
                TIP => { Some((get_key(x), get_value(x))) }
                NIL => { None }
                _ => { unreachable!() }
            }
        }
    }
}


// todo; doesn't look like this is idiomatic in Rust
//
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


// todo
// fn foreach[U](f: ((u64, T)) => U) -> Unit = self match {
// BitTrieMap::Bin(_, _, left, right) => { left.foreach(f); right.foreach(f) }
// BitTrieMap::Tip(key, value) => f((key, value))
// BitTrieMap::Nil =>
// }
//
// todo
// fn foreachEntry[U](f: (u64, T) => U) -> Unit = self match {
// BitTrieMap::Bin(_, _, left, right) => { left.foreachEntry(f); right.foreachEntry(f) }
// BitTrieMap::Tip(key, value) => f(key, value)
// BitTrieMap::Nil =>
// }
//
// todo
// fn keysIterator: Iterator[u64] = self match {
// BitTrieMap::Nil => Iterator.empty
// case _ => new BitTrieMapKeyIterator(self)
// }

// todo
// fn foreachKey[U](f: u64 => U) -> Unit = self match {
// BitTrieMap::Bin(_, _, left, right) => { left.foreachKey(f); right.foreachKey(f) }
// BitTrieMap::Tip(key, _) => f(key)
// BitTrieMap::Nil =>
// }
//
// todo
// fn valuesIterator: Iterator<T> = self match {
// BitTrieMap::Nil => Iterator.empty
// case _ => new BitTrieMapValueIterator(self)
// }

// todo
// fn foreachValue[U](f: T => U) -> Unit = self match {
// BitTrieMap::Bin(_, _, left, right) => { left.foreachValue(f); right.foreachValue(f) }
// BitTrieMap::Tip(_, value) => f(value)
// BitTrieMap::Nil =>
// }

