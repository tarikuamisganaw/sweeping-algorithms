mod bytetrie;
mod bittrie;
mod bittrie_alloc;
// mod bytetrie_alloc;
// mod bytetrie_alloc_simd;

use std::alloc::{alloc, dealloc, Layout};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::{mem, ptr};
use std::ops::BitOr;
use std::time::Instant;
// use bbtrie_sets::BBTrieSet;
use crate::bytetrie::{ByteTrieNode, BytesTrieMap, CoFree};
use crate::bytetrie::ShortTrieMap;
// use crate::bitmap::BitTrieMap;
use crate::bittrie_alloc::{BitTrieMap, MEM, Value};
// use crate::bbtrie_vector_sets::IntTrieMap;
// use hashbrown::HashMap;
// use roaring::RoaringBitmap;
// use roaring::RoaringBitmap;


fn set6Int(value: u32) -> Vec<u8> {
    return vec![
        ((value >> 30) & 0x3F) as u8,
        ((value >> 24) & 0x3F) as u8,
        ((value >> 18) & 0x3F) as u8,
        ((value >> 12) & 0x3F) as u8,
        ((value >> 6) & 0x3F) as u8,
        (value & 0x3F) as u8];
}

fn set6Int_inplace(b: &mut Vec<u8>, value: u32) {
    b[0] = ((value >> 30) & 0x3F) as u8;
    b[1] = ((value >> 24) & 0x3F) as u8;
    b[2] = ((value >> 18) & 0x3F) as u8;
    b[3] = ((value >> 12) & 0x3F) as u8;
    b[4] = ((value >> 6) & 0x3F) as u8;
    b[5] = (value & 0x3F) as u8;
}

fn get6Int(b: &Vec<u8>) -> u32 {
    return (((b[0] & 0x3F) as u32) << 30) |
           (((b[1] & 0x3F) as u32) << 24) |
           (((b[2] & 0x3F) as u32) << 18) |
           (((b[3] & 0x3F) as u32) << 12) |
           (((b[4] & 0x3F) as u32) << 6) |
           ((b[5] & 0x3F) as u32);
}

fn to_6_bit(input: Vec<u8>) -> Vec<u8> {
    let mut output = Vec::new();
    let mut buffer = 0u32; // Buffer to accumulate the bits
    let mut available_bits = 0; // Counter for available bits in buffer

    for &byte in &input {
        buffer |= (byte as u32) << available_bits; // Shift byte to its position in the buffer
        available_bits += 8; // Update available bits

        // While we have at least 6 bits, pack them into the output
        while available_bits >= 6 {
            output.push((buffer & 0x3F) as u8); // Take the lower 6 bits
            buffer >>= 6; // Remove them from the buffer
            available_bits -= 6; // Update available bits
        }
    }

    // Handling the last few bits, if any
    if available_bits > 0 {
        output.push((buffer & 0x3F) as u8);
    }

    output
}

fn from_6_bit(input: Vec<u8>) -> Vec<u8> {
    let mut output = Vec::new();
    let mut buffer = 0u32; // Buffer to accumulate the bits
    let mut available_bits = 0; // Counter for available bits in buffer

    for &byte in &input {
        buffer |= (byte as u32) << available_bits; // Shift byte to its position in the buffer
        available_bits += 6; // Update available bits

        // While we have at least 8 bits, pack them into the output
        while available_bits >= 8 {
            output.push((buffer & 0xFF) as u8); // Take the lower 8 bits
            buffer >>= 8; // Remove them from the buffer
            available_bits -= 8; // Update available bits
        }
    }

    // No need to handle remaining bits, as there shouldn't be any leftovers for perfect inverses

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reversibility() {
        let original = vec![0u8, 1, 254, 255, 128, 64, 127, 32];
        let to_6 = to_6_bit(original.clone());
        let from_6 = from_6_bit(to_6);
        assert_eq!(original, from_6);
    }

    #[test]
    fn test_empty_vector() {
        let original = vec![];
        let to_6 = to_6_bit(original.clone());
        let from_6 = from_6_bit(to_6);
        assert_eq!(original, from_6);
    }

    #[test]
    fn test_single_element() {
        let original = vec![255];
        let to_6 = to_6_bit(original.clone());
        let from_6 = from_6_bit(to_6);
        assert_eq!(original, from_6);
    }

    #[test]
    fn test_non_multiple_of_3() {
        // Length of 5 is not a multiple of 3, which is significant for 6-bit packing
        let original = vec![0, 1, 2, 3, 4];
        let to_6 = to_6_bit(original.clone());
        let from_6 = from_6_bit(to_6);
        assert_eq!(original, from_6);
    }

    #[test]
    fn test_boundary_values() {
        let original = vec![0, 63, 64, 127, 128, 191, 192, 255];
        let to_6 = to_6_bit(original.clone());
        let from_6 = from_6_bit(to_6);
        assert_eq!(original, from_6);
    }
}

trait Lattice {
    fn join(&self, other: &Self) -> Self;
    fn meet(&self, other: &Self) -> Self;
}

trait MapRing<V> {
    fn join_with(&self, other: &Self, op: fn(&V, &V) -> V) -> Self;
    // fn meet_with<F: Copy + Fn(&V, &V) -> V>(&self, other: &Self, op: F) -> Self;
    // fn subtract_with<F: Copy + Fn(&V, &V) -> Option<V>>(&self, other: &Self, op: F) -> Self;
}

trait DistributiveLattice: Lattice {
    fn subtract(&self, other: &Self) -> Self;
}

trait PartialDistributiveLattice: Lattice {
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
}

impl <V : PartialDistributiveLattice + Clone> DistributiveLattice for Option<V> {
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

impl <V : Clone> MapRing<V> for Option<V> {
    fn join_with(&self, other: &Self, op: fn(&V, &V) -> V) -> Self {
        match self {
            None => { match other {
                None => { None }
                Some(r) => { Some(r.clone()) }
            } }
            Some(l) => match other {
                None => { Some(l.clone()) }
                Some(r) => { Some(op(l, r)) }
            }
        }
    }

    // fn meet_with<F: Copy + Fn(&V, &V) -> V>(&self, other: &Self, op: F) -> Self {
    //     match self {
    //         None => { None }
    //         Some(l) => {
    //             match other {
    //                 None => { None }
    //                 Some(r) => Some(op(l, r))
    //             }
    //         }
    //     }
    // }
    //
    // fn subtract_with<F: Copy + Fn(&V, &V) -> Option<V>>(&self, other: &Self, op: F) -> Self {
    //     match self {
    //         None => { None }
    //         Some(l) => {
    //             match other {
    //                 None => { Some(l.clone()) }
    //                 Some(r) => op(l, r)
    //             }
    //         }
    //     }
    // }
}


impl Lattice for u64 {
    fn join(&self, other: &u64) -> u64 { *self }
    fn meet(&self, other: &u64) -> u64 { *self }
}

impl Lattice for &u64 {
    fn join(&self, other: &Self) -> Self { self }
    fn meet(&self, other: &Self) -> Self { self }
}

impl PartialDistributiveLattice for u64 {
    fn psubtract(&self, other: &Self) -> Option<Self> where Self: Sized {
        if self == other { None }
        else { Some(*self) }
    }
}

impl Lattice for u32 {
    fn join(&self, other: &u32) -> u32 { *self }
    fn meet(&self, other: &u32) -> u32 { *self }
}

impl Lattice for &u32 {
    fn join(&self, other: &Self) -> Self { self }
    fn meet(&self, other: &Self) -> Self { self }
}

impl Lattice for u16 {
    fn join(&self, other: &u16) -> u16 { *self }
    fn meet(&self, other: &u16) -> u16 { *other }
}

impl Lattice for &u16 {
    fn join(&self, other: &Self) -> Self { self }
    fn meet(&self, other: &Self) -> Self { other }
}

impl PartialDistributiveLattice for u16 {
    fn psubtract(&self, other: &Self) -> Option<Self> where Self: Sized {
        if self == other { None }
        else { Some(*self) }
    }
}

impl Lattice for u8 {
    fn join(&self, other: &u8) -> u8 { *self }
    fn meet(&self, other: &u8) -> u8 { *self }
}

impl Lattice for &u8 {
    fn join(&self, other: &Self) -> Self { self }
    fn meet(&self, other: &Self) -> Self { self }
}

impl <K : Copy + Eq + Hash, V : Copy + Lattice> Lattice for HashMap<K, V> {
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
}


impl<V : Copy + Lattice> Lattice for ByteTrieNode<V> {
    // #[inline(never)]
    fn join(&self, other: &Self) -> Self {
        let jm: [u64; 4] = [self.mask[0] | other.mask[0],
                            self.mask[1] | other.mask[1],
                            self.mask[2] | other.mask[2],
                            self.mask[3] | other.mask[3]];
        let mm: [u64; 4] = [self.mask[0] & other.mask[0],
                            self.mask[1] & other.mask[1],
                            self.mask[2] & other.mask[2],
                            self.mask[3] & other.mask[3]];

        let jmc = [jm[0].count_ones(), jm[1].count_ones(), jm[2].count_ones(), jm[3].count_ones()];

        let l = (jmc[0] + jmc[1] + jmc[2] + jmc[3]) as usize;
        let mut v = Vec::with_capacity(l);
        unsafe { v.set_len(l) }

        let mut l = 0;
        let mut r = 0;
        let mut c = 0;

        for i in 0..4 {
            let mut lm = jm[i];
            while lm != 0 {
                // this body runs at most 256 times, in the case there is 100% overlap between full nodes
                let index = lm.trailing_zeros();
                // println!("{}", index);
                if ((1u64 << index) & mm[i]) != 0 {
                    let lv = unsafe { self.values.get_unchecked(l) };
                    let rv = unsafe { other.values.get_unchecked(r) };
                    let jv = lv.join(rv);
                    // println!("pushing lv rv j {:?} {:?} {:?}", lv, rv, jv);
                    unsafe { *v.get_unchecked_mut(c) = jv; }
                    l += 1;
                    r += 1;
                } else if ((1u64 << index) & self.mask[i]) != 0 {
                    let lv = unsafe { self.values.get_unchecked(l) };
                    // println!("pushing lv {:?}", lv);
                    unsafe { *v.get_unchecked_mut(c) = lv.clone(); }
                    l += 1;
                } else {
                    let rv = unsafe { other.values.get_unchecked(r) };
                    // println!("pushing rv {:?}", rv);
                    unsafe { *v.get_unchecked_mut(c) = rv.clone() };
                    r += 1;
                }
                lm ^= 1u64 << index;
                c += 1;
            }
        }

        return ByteTrieNode::<V>{ mask: jm, values: v };
    }

    fn meet(&self, other: &Self) -> Self {
        // TODO this technically doesn't need to calculate and iterate over jm
        // iterating over mm and calculating m such that the following suffices
        // c_{self,other} += popcnt(m & {self,other})
        let jm: [u64; 4] = [self.mask[0] | other.mask[0],
            self.mask[1] | other.mask[1],
            self.mask[2] | other.mask[2],
            self.mask[3] | other.mask[3]];
        let mm: [u64; 4] = [self.mask[0] & other.mask[0],
            self.mask[1] & other.mask[1],
            self.mask[2] & other.mask[2],
            self.mask[3] & other.mask[3]];

        let mmc = [mm[0].count_ones(), mm[1].count_ones(), mm[2].count_ones(), mm[3].count_ones()];

        let l = (mmc[0] + mmc[1] + mmc[2] + mmc[3]) as usize;
        let mut v = Vec::with_capacity(l);
        unsafe { v.set_len(l) }

        let mut l = 0;
        let mut r = 0;
        let mut c = 0;

        for i in 0..4 {
            let mut lm = jm[i];
            while lm != 0 {
                let index = lm.trailing_zeros();

                if ((1u64 << index) & mm[i]) != 0 {
                    let lv = unsafe { self.values.get_unchecked(l) };
                    let rv = unsafe { other.values.get_unchecked(r) };
                    let jv = lv.meet(rv);
                    unsafe { *v.get_unchecked_mut(c) = jv; }
                    l += 1;
                    r += 1;
                    c += 1;
                } else if ((1u64 << index) & self.mask[i]) != 0 {
                    l += 1;
                } else {
                    r += 1;
                }
                lm ^= 1u64 << index;
            }
        }

        return ByteTrieNode::<V>{ mask: mm, values: v };
    }
}

impl <V : Copy + PartialDistributiveLattice> DistributiveLattice for ByteTrieNode<V> {
    fn subtract(&self, other: &Self) -> Self {
        let mut btn = self.clone();

        for i in 0..4 {
            let mut lm = self.mask[i];
            while lm != 0 {
                let index = lm.trailing_zeros();

                if ((1u64 << index) & other.mask[i]) != 0 {
                    let lv = unsafe { self.get_unchecked(64*(i as u8)) };
                    let rv = unsafe { other.get_unchecked(64*(i as u8) + (index as u8)) };
                    match lv.psubtract(rv) {
                        None => { btn.remove(64*(i as u8)); }
                        Some(jv) => unsafe { *btn.get_unchecked_mut(64*(i as u8)) = jv; }
                    }
                }

                lm ^= 1u64 << index;
            }
        }

        return btn;
    }
}

impl <V : Copy + PartialDistributiveLattice> PartialDistributiveLattice for ByteTrieNode<V> {
    fn psubtract(&self, other: &Self) -> Option<Self> where Self: Sized {
        let r = self.subtract(other);
        if r.len() == 0 { return None }
        else { return Some(r) }
    }
}

impl <V : Copy + Lattice> Lattice for *mut ByteTrieNode<V> {
    fn join(&self, other: &Self) -> Self {
        unsafe {
        match self.as_ref() {
            None => { *other }
            Some(sptr) => {
                match other.as_ref() {
                    None => { ptr::null_mut() }
                    Some(optr) => {
                        let v = unsafe { sptr.join(optr) };
                        let mut vb = Box::new(v);
                        let p = vb.as_mut() as Self;
                        mem::forget(vb);
                        p
                    }
                }
            }
        }
        }
    }

    fn meet(&self, other: &Self) -> Self {
        unsafe {
            match self.as_ref() {
                None => { ptr::null_mut() }
                Some(sptr) => {
                    match other.as_ref() {
                        None => { ptr::null_mut() }
                        Some(optr) => {
                            let v = unsafe { sptr.meet(optr) };
                            let mut vb = Box::new(v);
                            let p = vb.as_mut() as Self;
                            mem::forget(vb);
                            p
                        }
                    }
                }
            }
        }
    }
}

impl<V : Copy + PartialDistributiveLattice> PartialDistributiveLattice for *mut ByteTrieNode<V> {
    fn psubtract(&self, other: &Self) -> Option<Self> {
        unsafe {
        match self.as_ref() {
            None => { None }
            Some(sr) => {
                match other.as_ref() {
                    None => { Some(*self) }
                    Some(or) => {
                        let v = sr.subtract(or);
                        if v.len() == 0 { None }
                        else {
                            let mut vb = Box::new(v);
                            let p = vb.as_mut() as Self;
                            mem::forget(vb);
                            Some(p)
                        }
                    }
                }
            }
        }
        }
    }
}

impl<V : Copy + Lattice> Lattice for ShortTrieMap<V> {
    fn join(&self, other: &Self) -> Self {
        Self {
            root: self.root.join(&other.root),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        Self {
            root: self.root.meet(&other.root),
        }
    }
}

impl<V : Copy + PartialDistributiveLattice> DistributiveLattice for ShortTrieMap<V> {
    fn subtract(&self, other: &Self) -> Self {
        Self {
            root: self.root.subtract(&other.root),
        }
    }
}

impl<V : Copy + Lattice> Lattice for CoFree<V> {
    fn join(&self, other: &Self) -> Self {
        CoFree {
            rec: self.rec.join(&other.rec),
            value: self.value.join(&other.value)
        }
    }

    fn meet(&self, other: &Self) -> Self {
        CoFree {
            rec: self.rec.meet(&other.rec),
            value: self.value.meet(&other.value)
        }
    }
}

impl<V : Copy + PartialDistributiveLattice> DistributiveLattice for CoFree<V> {
    fn subtract(&self, other: &Self) -> Self {
        CoFree {
            rec: self.rec.psubtract(&other.rec).unwrap_or(ptr::null_mut()),
            value: self.value.subtract(&other.value)
        }
    }
}

impl<V : Copy + PartialDistributiveLattice> PartialDistributiveLattice for CoFree<V> {
    fn psubtract(&self, other: &Self) -> Option<Self> where Self: Sized {
        // .unwrap_or(ptr::null_mut())
        let r = self.rec.psubtract(&other.rec);
        let v = self.value.subtract(&other.value);
        match r {
            None => { if v.is_none() { None } else { Some(CoFree{ rec: ptr::null_mut(), value: v }) } }
            Some(sr) => { Some(CoFree{ rec: sr, value: v }) }
        }
    }
}

impl<V : Copy + Lattice> Lattice for BytesTrieMap<V> {
    fn join(&self, other: &Self) -> Self {
        Self {
            root: self.root.join(&other.root),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        Self {
            root: self.root.meet(&other.root),
        }
    }
}

impl<V : Copy + PartialDistributiveLattice> DistributiveLattice for BytesTrieMap<V> {
    fn subtract(&self, other: &Self) -> Self {
        Self {
            root: self.root.subtract(&other.root),
        }
    }
}

impl<V : Copy + PartialDistributiveLattice> PartialDistributiveLattice for BytesTrieMap<V> {
    fn psubtract(&self, other: &Self) -> Option<Self> {
        let s = self.root.subtract(&other.root);
        if s.len() == 0 { None }
        else { Some(Self { root: s }) }
    }
}


impl Value for u64 {}

fn prefix_key(k: u64) -> Vec<u8> {
    // TODO
    let bs = (8 - k.leading_zeros()/8) as u8;
    match bs {
        0 => { vec![0] }
        1 => { vec![k as u8] }
        2 => { vec![(k >> 8) as u8, k as u8] }
        3 => { vec![(k >> 16) as u8, (k >> 8) as u8, k as u8] }
        5 => { vec![(k >> 24) as u8, (k >> 16) as u8, (k >> 8) as u8, k as u8] }
        _ => { unreachable!() }
    }
}

fn from_prefix_key(k: Vec<u8>) -> u64 {
    match k.len() {
        0 => { 0 }
        1 => { k[0] as u64 }
        2 => { ((k[0] as u64) << 8) | k[1] as u64 }
        3 => { ((k[0] as u64) << 16) | ((k[1] as u64) << 8) | k[2] as u64 }
        5 => { ((k[0] as u64) << 24) | ((k[1] as u64) << 16) | ((k[2] as u64) << 8) | k[3] as u64 }
        _ => { unreachable!() }
    }
}

fn main() {
    // println!("{:?}", prefix_key(30));
    // println!("{:?}", prefix_key(300));
    // println!("{:?}", prefix_key(30000));
    // println!("{:?}", prefix_key(3000000));
    // println!("{:?}", prefix_key(u32::MAX as u64 + 1));
    // println!("{:?}", prefix_key(1u64 << 48 | 1u64 << 22));
    // println!("{:?}", prefix_key(u64::MAX - 1));

    // unsafe {
    //     core::ptr::write(
    //         &mut MEM,
    //         // alloc(Layout::new::<ByteTrieNode<u64>>()) as *mut u64,
    //         alloc(Layout::from_size_align(512*1024*1024, 64).unwrap()) as *mut u64,
    //     );
    // }

    // {
    //     let mut ts = BBTrieSet::new(100);
    //     let t1 = Instant::now();
    //     let mut k = vec![0; 6];
    //     for i in 0..N {
    //         set6Int_inplace(&mut k, i);
    //         ts.set(&k);
    //         assert!(ts.get(&k));
    //         ts.clear(&k);
    //         assert!(!ts.get(&k));
    //     }
    //     println!("{}", t1.elapsed().as_nanos() as f64/N as f64);
    //
    //     let mut hs = HashSet::new();
    //     let t2 = Instant::now();
    //     for i in 0..N {
    //         hs.insert(i);
    //         assert!(hs.contains(&i));
    //         hs.remove(&i);
    //         assert!(!hs.contains(&i));
    //     }
    //     println!("{}", t2.elapsed().as_nanos() as f64/N as f64);
    // }
    // {
    //     let mut ts = BBTrieSet::new(2000);
    //     let t1 = Instant::now();
    //     for i in 0..N {
    //         // set6Int_inplace(&mut k, i);
    //         println!("{:02X?}", i.to_string().as_bytes().to_vec());
    //         println!("{:02X?}", to_6_bit(i.to_string().as_bytes().to_vec()));
    //         ts.set(&to_6_bit(i.to_string().as_bytes().to_vec()));
    //     }
    //     println!("{}", t1.elapsed().as_nanos() as f64/N as f64);
    //     let t2 = Instant::now();
    //     let mut acc = true;
    //     for i in 0..N {
    //         // assert!(ts.get(&k));
    //         println!("{:02X?}", i.to_string().as_bytes().to_vec());
    //         println!("{:02X?}", to_6_bit(i.to_string().as_bytes().to_vec()));
    //         println!("{}", ts.get(&to_6_bit(i.to_string().as_bytes().to_vec())));
    //     }
    //     println!("{} {}", t2.elapsed().as_nanos() as f64/N as f64, acc);
    //
    //     let mut hs: HashSet<Vec<u8>> = HashSet::new();
    //     let t3 = Instant::now();
    //     for i in 0..N {
    //         // hs.insert(i);
    //         hs.insert(to_6_bit(i.to_string().as_bytes().to_vec()));
    //     }
    //     println!("{}", t3.elapsed().as_nanos() as f64/N as f64);
    //     let t4 = Instant::now();
    //     for i in 0..N {
    //         // assert!(hs.contains(&i));
    //         assert!(hs.contains(&to_6_bit(i.to_string().as_bytes().to_vec())));
    //     }
    //     println!("{}", t4.elapsed().as_nanos() as f64/N as f64);
    // }

    // const N: u16 = 16000;
    // let overlap = 0.5;
    // let O = ((1. - overlap) * N as f64) as u16;
    // {
    //     let mut vnl = ShortTrieMap::new();
    //     let mut vnr = ShortTrieMap::new();
    //     for i in 0..N { vnl.insert(i, i); }
    //     let mut c: Vec<u16> = Vec::with_capacity(N as usize);
    //     vnl.items().for_each(|(k, v)| {
    //         assert!(0 <= v && v < N);
    //         assert_eq!(k, v);
    //         c.push(k);
    //     });
    //     c.sort();
    //     assert_eq!(c, (0..N).collect::<Vec<u16>>());
    //     for i in O..(N+O) { vnr.insert(i, i); }
    //
    //     let t0 = Instant::now();
    //     let j = vnl.join(&vnr);
    //     // 32, 21, 14, 8, 6
    //     println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
    //     let m = vnl.meet(&vnr);
    //     let mut l_no_r = vnl.subtract(&vnr);
    //     for i in 0..N { assert_eq!(l_no_r.get(i), vnl.get(i)); }
    //     for i in N..(2*N) { assert!(!l_no_r.contains(i)); }
    //
    //     for i in O..N { assert!(vnl.contains(i) && vnr.contains(i)); }
    //     for i in 0..O { assert!(vnl.contains(i) && !vnr.contains(i)); }
    //     for i in N..(N+O) { assert!(!vnl.contains(i) && vnr.contains(i)); }
    //     for i in 0..(2*N) { assert_eq!(j.contains(i), (vnl.contains(i) || vnr.contains(i))); }
    //     for i in 0..(2*N) { assert_eq!(m.contains(i), (vnl.contains(i) && vnr.contains(i))); }
    //     for i in 0..(N+O) { assert_eq!(j.get(i), vnl.get(i).join(&vnr.get(i))); }
    //     for i in O..N { assert_eq!(m.get(i), vnl.get(i).meet(&vnr.get(i))); }
    //     // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains(i), vnl.contains(i), vnr.contains(i)); } // assert!(r.contains(i));
    // }

    const N: u64 = 1000;
    let overlap = 0.5;
    let O = ((1. - overlap) * N as f64) as u64;
    {
        let mut vnl = BytesTrieMap::new();
        let mut vnr = BytesTrieMap::new();
        for i in 0..N { vnl.insert(prefix_key(i), i); }
        // println!("{:?}", vnl.root);
        for i in 0..N { assert_eq!(vnl.get(prefix_key(i)), Some(i).as_ref()); }
        for i in N..2*N { assert_eq!(vnl.get(prefix_key(i)), None); }
        let mut c: Vec<u64> = Vec::with_capacity(N as usize);
        vnl.items().for_each(|(k, v)| {
            assert!(0 <= v && v < N);
            assert_eq!(k, prefix_key(v));
            c.push(from_prefix_key(k));
        });
        c.sort();
        assert_eq!(c, (0..N).collect::<Vec<u64>>());
        for i in O..(N+O) { vnr.insert(prefix_key(i), i); }

        let t0 = Instant::now();
        let j = vnl.join(&vnr);
        // 8, 7, 5, 5, 4
        println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
        let m = vnl.meet(&vnr);
        let mut l_no_r = vnl.subtract(&vnr);
        for i in 0..N { assert_eq!(l_no_r.get(prefix_key(i)), vnl.get(prefix_key(i))); }
        for i in N..(2*N) { assert!(!l_no_r.contains(prefix_key(i))); }

        for i in O..N { assert!(vnl.contains(prefix_key(i)) && vnr.contains(prefix_key(i))); }
        for i in 0..O { assert!(vnl.contains(prefix_key(i)) && !vnr.contains(prefix_key(i))); }
        for i in N..(N+O) { assert!(!vnl.contains(prefix_key(i)) && vnr.contains(prefix_key(i))); }
        for i in 0..(2*N) { assert_eq!(j.contains(prefix_key(i)), (vnl.contains(prefix_key(i)) || vnr.contains(prefix_key(i)))); }
        for i in 0..(2*N) { assert_eq!(m.contains(prefix_key(i)), (vnl.contains(prefix_key(i)) && vnr.contains(prefix_key(i)))); }
        for i in 0..(N+O) { assert_eq!(j.get(prefix_key(i)), vnl.get(prefix_key(i)).join(&vnr.get(prefix_key(i)))); }
        for i in O..N { assert_eq!(m.get(prefix_key(i)), vnl.get(prefix_key(i)).meet(&vnr.get(prefix_key(i)))); }
        // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains(i), vnl.contains(i), vnr.contains(i)); } // assert!(r.contains(i));
    }
    // {
    //     let mut vnl = BitTrieMap::empty();
    //     let mut vnr = BitTrieMap::empty();
    //     for i in 0..N { vnl = vnl.updated(i, i); }
    //     let mut c: Vec<u64> = Vec::with_capacity(N as usize);
    //     vnl.iter().for_each(|(k, v)| {
    //         assert!(0 <= v && v < N);
    //         assert_eq!(k, v);
    //         c.push(k);
    //     });
    //     c.sort();
    //     assert_eq!(c, (0..N).collect::<Vec<u64>>());
    //     for i in O..(N+O) { vnr = vnr.updated(i, i); }
    //
    //     let t0 = Instant::now();
    //     let j = Box::new(vnl.clone()).union_with(Box::new(vnr.clone()), |_, l, r| { r });
    //     println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
    //     let m = Box::new(vnl.clone()).intersection_with(Box::new(vnr.clone()), |_, l, r| { r });
    //     let mut r_no_l = Box::new(vnl.clone()).union_with(Box::new(vnr.clone()), |_, l, r| { r });
    //     for i in 0..(2*N) { assert_eq!(r_no_l.get(i), j.get(i)); }
    //     for i in 0..O { assert!(r_no_l.contains(i)); r_no_l = r_no_l.removed(i); assert!(!r_no_l.contains(i)); }
    //     // for i in O..(N + O) { assert_eq!(r_no_l.get(i), vnr.get(i)); }
    //     // let mut r_no_l_ = vnr.subtract(&vnl);
    //     // for i in 0..(2*N) { println!("{}", i); assert_eq!(r_no_l.get(i), r_no_l_.get(i)); }
    //
    //     for i in O..N { assert!(vnl.contains(i) && vnr.contains(i)); }
    //     for i in 0..O { assert!(vnl.contains(i) && !vnr.contains(i)); }
    //     for i in N..(N+O) { assert!(!vnl.contains(i) && vnr.contains(i)); }
    //     for i in 0..(2*N) { assert_eq!(j.contains(i), (vnl.contains(i) || vnr.contains(i))); }
    //     for i in 0..(2*N) { assert_eq!(m.contains(i), (vnl.contains(i) && vnr.contains(i))); }
    //     for i in 0..(N+O) { assert_eq!(j.get(i), vnl.get(i).join(&vnr.get(i))); }
    //     for i in O..N { assert_eq!(m.get(i), vnl.get(i).meet(&vnr.get(i))); }
    //     // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains(i), vnl.contains(i), vnr.contains(i)); } // assert!(r.contains(i));
    // }
    // {
    //     let mut vnl = BitTrieMap::empty();
    //     let mut vnr = BitTrieMap::empty();
    //     for i in 0..N { vnl = vnl.updated(i, i); }
    //     let mut c: Vec<u64> = Vec::with_capacity(N as usize);
    //     vnl.iter().for_each(|(k, v)| {
    //         assert!(0 <= v && v < N);
    //         assert_eq!(k, v);
    //         c.push(k);
    //     });
    //     c.sort();
    //     assert_eq!(c, (0..N).collect::<Vec<u64>>());
    //     for i in O..(N+O) { vnr = vnr.updated(i, i); }
    //
    //     let t0 = Instant::now();
    //     let j = vnl.union_with(vnr, |_, l, r| { r });
    //     // 31, 36, 36, 37, 48
    //     println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
    //     let m = vnl.intersection_with(vnr, |_, l, r| { r });
    //     let mut r_no_l = vnl.union_with(vnr, |_, l, r| { r });
    //     for i in 0..(2*N) { assert_eq!(r_no_l.get(i), j.get(i)); }
    //     for i in 0..O { assert!(r_no_l.contains(i)); r_no_l = r_no_l.removed(i); assert!(!r_no_l.contains(i)); }
    //     // for i in O..(N + O) { assert_eq!(r_no_l.get(i), vnr.get(i)); }
    //     // let mut r_no_l_ = vnr.subtract(&vnl);
    //     // for i in 0..(2*N) { println!("{}", i); assert_eq!(r_no_l.get(i), r_no_l_.get(i)); }
    //
    //     for i in O..N { assert!(vnl.contains(i) && vnr.contains(i)); }
    //     for i in 0..O { assert!(vnl.contains(i) && !vnr.contains(i)); }
    //     for i in N..(N+O) { assert!(!vnl.contains(i) && vnr.contains(i)); }
    //     for i in 0..(2*N) { assert_eq!(j.contains(i), (vnl.contains(i) || vnr.contains(i))); }
    //     for i in 0..(2*N) { assert_eq!(m.contains(i), (vnl.contains(i) && vnr.contains(i))); }
    //     for i in 0..(N+O) { assert_eq!(j.get(i), vnl.get(i).join(&vnr.get(i))); }
    //     for i in O..N { assert_eq!(m.get(i), vnl.get(i).meet(&vnr.get(i))); }
    //     // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains(i), vnl.contains(i), vnr.contains(i)); } // assert!(r.contains(i));
    // }

    // unsafe { dealloc(MEM as *mut u8, Layout::from_size_align(64 * 1024 * 1024, 64).unwrap()); }

    // {
    //     let mut vnl = HashMap::new();
    //     let mut vnr = HashMap::new();
    //     for i in 0..N { vnl.insert(i, i); }
    //     let mut c = Vec::with_capacity(N as usize);
    //     vnl.clone().into_iter().for_each(|(k, v)| {
    //         assert!(0 <= v && v < N);
    //         assert_eq!(k, v);
    //         c.push(k);
    //     });
    //     c.sort();
    //     assert_eq!(c, (0..N).collect::<Vec<_>>());
    //     for i in O..(N+O) { vnr.insert(i, i); }
    //
    //     let t0 = Instant::now();
    //     let j = vnl.join(&vnr);
    //     // 183, 178, 175, 152, 157  built in
    //     // 122, 118, 116, 154, 118  hashbrown
    //     println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
    //     let m = vnl.meet(&vnr);
    //     let mut r_no_l = j.clone();
    //     for i in 0..O { assert!(r_no_l.contains_key(&i)); r_no_l.remove(&i); assert!(!r_no_l.contains_key(&i)); }
    //
    //     for i in O..N { assert!(vnl.contains_key(&i) && vnr.contains_key(&i)); }
    //     for i in 0..O { assert!(vnl.contains_key(&i) && !vnr.contains_key(&i)); }
    //     for i in N..(N+O) { assert!(!vnl.contains_key(&i) && vnr.contains_key(&i)); }
    //     for i in 0..(2*N) { assert_eq!(j.contains_key(&i), (vnl.contains_key(&i) || vnr.contains_key(&i))); }
    //     for i in 0..(2*N) { assert_eq!(m.contains_key(&i), (vnl.contains_key(&i) && vnr.contains_key(&i))); }
    //     for i in 0..(N+O) { assert_eq!(j.get(&i), vnl.get(&i).join(&vnr.get(&i))); }
    //     for i in O..N { assert_eq!(m.get(&i), vnl.get(&i).meet(&vnr.get(&i))); }
    //     // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains_key(&i), vnl.contains_key(&i), vnr.contains_key(&i)); } // assert!(r.contains_key(&i));
    // }

    // {
    //     let mut vnl = RoaringBitmap::new();
    //     let mut vnr = RoaringBitmap::new();
    //     for i in 0..N { vnl.insert(13*i); }
    //     let mut c = Vec::with_capacity(N as usize);
    //     vnl.clone().into_iter().for_each(|k| {
    //         // assert!(0 <= k && k < N);
    //         c.push(k);
    //     });
    //     c.sort();
    //     // assert_eq!(c, (0..N).collect::<Vec<_>>());
    //     for i in O..(N+O) { vnr.insert(13*i); }
    //
    //     let t0 = Instant::now();
    //     let j = vnl.bitor(&vnr);
    //     // 6, 4, 7, 2, 1
    //     println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
    //     // let m = vnl.meet(&vnr);
    //     // let mut r_no_l = j.clone();
    //     // for i in 0..O { assert!(r_no_l.contains_key(&i)); r_no_l.remove(&i); assert!(!r_no_l.contains_key(&i)); }
    //     //
    //     // for i in O..N { assert!(vnl.contains_key(&i) && vnr.contains_key(&i)); }
    //     // for i in 0..O { assert!(vnl.contains_key(&i) && !vnr.contains_key(&i)); }
    //     // for i in N..(N+O) { assert!(!vnl.contains_key(&i) && vnr.contains_key(&i)); }
    //     // for i in 0..(2*N) { assert_eq!(j.contains_key(&i), (vnl.contains_key(&i) || vnr.contains_key(&i))); }
    //     // for i in 0..(2*N) { assert_eq!(m.contains_key(&i), (vnl.contains_key(&i) && vnr.contains_key(&i))); }
    //     // for i in 0..(N+O) { assert_eq!(j.get(&i), vnl.get(&i).join(&vnr.get(&i))); }
    //     // for i in O..N { assert_eq!(m.get(&i), vnl.get(&i).meet(&vnr.get(&i))); }
    //     // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains_key(&i), vnl.contains_key(&i), vnr.contains_key(&i)); } // assert!(r.contains_key(&i));
    // }

    // {
    //     let mut vn = IntTrieMap::empty();
    //     let t0 = Instant::now();
    //     for i in 0..N {
    //         vn.add(i, i);
    //         // println!("{} {}", i, vn.left(i as u8))
    //     }
    //     for i in N..2_000_000 {
    //         // assert!(!vn.contains(i));
    //         // assert_eq!(*vn.get(i), i);
    //         assert!(vn.get(i).is_none());
    //     }
    //     println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
    // }
    // {
    //     let mut vn = HashMap::new();
    //     let t0 = Instant::now();
    //     for i in 0..N {
    //         vn.insert(i, i);
    //     }
    //     for i in N..2_000_000 {
    //         // assert!(!vn.contains_key(&i));
    //         // assert_eq!(*vn.get(&i).unwrap(), i);
    //         assert!(vn.get(&i).is_none());
    //     }
    //     println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
    // }
}
