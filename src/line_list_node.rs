use core::mem::{ManuallyDrop, MaybeUninit};

use local_or_heap::LocalOrHeap;

use crate::bytetrie::*;
use crate::ring::*;
use crate::dense_byte_node::DenseByteNode;


/// A LineListNode stores up to 2 children in a single cache line
pub struct LineListNode<V> {
    /// bit 15 = slot_0_used
    /// bit 14 = slot_1_used
    /// bit 13 = slot_0_is_child (child ptr vs value)
    /// bit 12 = slot_1_is_child (child ptr vs value).  If bit 14 is 0, but bit 12 is 1, it means slot_0 consumed all the key space, so nothing can go in slot_1
    /// bits 11 & 10 = unused
    /// bit 9 to bit 5 = slot_0_key_len
    /// bit 4 to bit 0 = slot_1_key_len
    header: u16,
    key_bytes: [MaybeUninit<u8>; KEY_BYTES_CNT],
    val_or_child0: ValOrChild<V>,
    val_or_child1: ValOrChild<V>,
}
const KEY_BYTES_CNT: usize = 30;

union ValOrChild<V> {
    child: ManuallyDrop<TrieNodeODRc<V>>,
    val: ManuallyDrop<LocalOrHeap<V>>,
    _unused: ()
}

impl<V> Drop for LineListNode<V> {
    fn drop(&mut self) {
        if self.is_used_0() {
            if self.is_child_ptr_0() {
                unsafe{ ManuallyDrop::drop(&mut self.val_or_child0.child) }
            } else {
                unsafe{ ManuallyDrop::drop(&mut self.val_or_child0.val) }
            }
        }
        if self.is_used_1() {
            if self.is_child_ptr_1() {
                unsafe{ ManuallyDrop::drop(&mut self.val_or_child1.child) }
            } else {
                unsafe{ ManuallyDrop::drop(&mut self.val_or_child1.val) }
            }
        }
    }
}

impl<V: Clone> Clone for LineListNode<V> {
    fn clone(&self) -> Self {
        let val_or_child0 = if self.is_used_0() {
            if self.is_child_ptr_0() {
                let child = unsafe{ &self.val_or_child0.child }.clone();
                ValOrChild{ child }
            } else {
                let val = unsafe{ &self.val_or_child0.val }.clone();
                ValOrChild{ val }
            }
        } else {
            ValOrChild{ _unused: () }
        };
        let val_or_child1 = if self.is_used_1() {
            if self.is_child_ptr_1() {
                let child = unsafe{ &self.val_or_child1.child }.clone();
                ValOrChild{ child }
            } else {
                let val = unsafe{ &self.val_or_child1.val }.clone();
                ValOrChild{ val }
            }
        } else {
            ValOrChild{ _unused: () }
        };
        Self {
            header: self.header,
            key_bytes: self.key_bytes,
            val_or_child0,
            val_or_child1,
        }
    }
}

impl<V> Default for LineListNode<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl <V : core::fmt::Debug> core::fmt::Debug for LineListNode<V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> std::fmt::Result {
        //Recursively printing a whole tree will get pretty unwieldy.  Should do something
        // like serialization for inspection using standard tools.
        write!(f,
               "LineListNode (slot0: occupied={} is_child={}, slot1: occupied={} is_child={})",
               self.is_used_0(), self.is_child_ptr_0(), self.is_used_1(), self.is_child_ptr_1())
    }
}

impl<V> LineListNode<V> {

    #[inline]
    pub fn new() -> Self {
        Self {
            header: 0,
            key_bytes: [MaybeUninit::uninit(); KEY_BYTES_CNT],
            val_or_child0: ValOrChild{ _unused: () },
            val_or_child1: ValOrChild{ _unused: () },
        }
    }
    #[inline]
    pub fn is_used_0(&self) -> bool {
        self.header & (1 << 15) > 0
    }
    #[inline]
    pub fn is_used_1(&self) -> bool {
        self.header & (1 << 14) > 0
    }
    /// Returns `true` if slot_1 is available to be filled with an entry, otherwise `false`.  The reason
    /// `!is_used_1()` is insufficient is because `slot_1` may be empty but the key storage may be fully
    /// consumed by slot_0's key
    #[inline]
    pub fn is_available_1(&self) -> bool {
        self.header & ((1 << 14) | (1 << 12)) != (1 << 12)
    }
    #[inline]
    pub fn is_child_ptr_0(&self) -> bool {
        self.header & (1 << 13) > 0
    }
    #[inline]
    pub fn is_child_ptr_1(&self) -> bool {
        self.header & (1 << 12) > 0
    }
    /// Conceptually identical to is_used_0 && is_child_ptr_0, but with a compound operation
    #[inline]
    pub fn is_used_child_0(&self) -> bool {
        self.header & ((1 << 15) | (1 << 13)) > 0
    }
    #[inline]
    pub fn is_used_child_1(&self) -> bool {
        self.header & ((1 << 14) | (1 << 12)) > 0
    }
    /// Conceptually identical to is_used_0 && !is_child_ptr_0, but with a compound operation
    #[inline]
    pub fn is_used_value_0(&self) -> bool {
        self.header & ((1 << 15) | (1 << 13)) == (1 << 15)
    }
    #[inline]
    pub fn is_used_value_1(&self) -> bool {
        self.header & ((1 << 14) | (1 << 12)) == (1 << 14)
    }
    #[inline]
    pub fn key_len_0(&self) -> usize {
        const MASK: u16 = 0x3e0; //bits 9 to 5, inclusive
        ((self.header & MASK) >> 5) as usize
    }
    #[inline]
    pub fn key_len_1(&self) -> usize {
        const MASK: u16 = 0x1f; //bits 4 to 0, inclusive
        (self.header & MASK) as usize
    }
    //NOTE: max_key_len_0 == KEY_BYTES_CNT, because LineListNodes are append-only
    // #[inline]
    // pub fn max_key_len_1(&self) -> usize {
    //     KEY_BYTES_CNT - self.key_len_0()
    // }
    //GOAT, Easier to construct the ranges as we need them
    // #[inline]
    // pub fn key_range_0(&self) -> core::ops::RangeTo<usize> {
    //     core::ops::RangeTo{ end: self.key_len_0() }
    // }
    // #[inline]
    // pub fn key_range_1(&self) -> core::ops::Range<usize> {
    //     core::ops::Range{ start: self.key_len_0(), end: self.key_len_1() }
    // }
    #[inline]
    unsafe fn key_unchecked_0(&self) -> &[u8] {
        core::slice::from_raw_parts(self.key_bytes.as_ptr().cast(), self.key_len_0())
    }
    #[inline]
    unsafe fn key_unchecked_1(&self) -> &[u8] {
        let base_ptr = self.key_bytes.get_unchecked(self.key_len_0());
        core::slice::from_raw_parts(base_ptr.as_ptr().cast(), self.key_len_1())
    }
    #[inline]
    unsafe fn set_val_0(&mut self, key: &[u8], val: V) {
        debug_assert!(key.len() <= KEY_BYTES_CNT);
        core::ptr::copy_nonoverlapping(key.as_ptr(), self.key_bytes.as_mut_ptr().cast(), key.len());
        let node_val = unsafe{ &mut self.val_or_child0.val };
        *node_val = ManuallyDrop::new(LocalOrHeap::new(val));
        let mask = 0x8000 | (key.len() << 5);
        self.header |= mask as u16;
        if key.len() == KEY_BYTES_CNT {
            self.header |= 1 << 12; //Set the flag state so slot_1 is unavailable
        }
    }
    #[inline]
    unsafe fn set_val_1(&mut self, key: &[u8], val: V) {
        let key_0_used_cnt = self.key_len_0();
        debug_assert!(key.len() <= KEY_BYTES_CNT - key_0_used_cnt);
        let base_ptr = self.key_bytes.get_unchecked_mut(key_0_used_cnt);
        core::ptr::copy_nonoverlapping(key.as_ptr(), base_ptr.as_mut_ptr().cast(), key.len());
        let node_val = unsafe{ &mut self.val_or_child1.val };
        *node_val = ManuallyDrop::new(LocalOrHeap::new(val));
        let mask = 0x4000 | key.len();
        self.header |= mask as u16;
    }
    #[inline]
    unsafe fn set_child_0(&mut self, key: &[u8], child: TrieNodeODRc<V>) {
        debug_assert!(key.len() <= KEY_BYTES_CNT);
        core::ptr::copy_nonoverlapping(key.as_ptr(), self.key_bytes.as_mut_ptr().cast(), key.len());
        let node_child = unsafe{ &mut self.val_or_child0.child };
        *node_child = ManuallyDrop::new(child);
        let mask = 	0xa000 | (key.len() << 5);
        self.header |= mask as u16;
        if key.len() == KEY_BYTES_CNT {
            self.header |= 1 << 12; //Set the flag state so slot_1 is unavailable
        }
    }
    #[inline]
    unsafe fn set_child_1(&mut self, key: &[u8], child: TrieNodeODRc<V>) {
        let key_0_used_cnt = self.key_len_0();
        debug_assert!(key.len() <= KEY_BYTES_CNT - key_0_used_cnt);
        let base_ptr = self.key_bytes.get_unchecked_mut(key_0_used_cnt);
        core::ptr::copy_nonoverlapping(key.as_ptr(), base_ptr.as_mut_ptr().cast(), key.len());
        let node_child = unsafe{ &mut self.val_or_child1.child };
        *node_child = ManuallyDrop::new(child);
        let mask = 	0x5000 | key.len();
        self.header |= mask as u16;
    }
    #[inline]
    fn contains_val(&self, key: &[u8]) -> bool {
        if self.is_used_value_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            if node_key_0 == key {
                return true;
            }
        }
        if self.is_used_value_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            if node_key_1 == key {
                return true;
            }
        }
        false
    }
    #[inline]
    fn get_val(&self, key: &[u8]) -> Option<&V> {
        if self.is_used_value_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            if node_key_0 == key {
                let val = unsafe{ &**self.val_or_child0.val };
                return Some(val);
            }
        }
        if self.is_used_value_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            if node_key_1 == key {
                let val = unsafe{ &**self.val_or_child1.val };
                return Some(val);
            }
        }
        None
    }
    #[inline]
    fn get_val_mut(&mut self, key: &[u8]) -> Option<&mut V> {
        if self.is_used_value_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            if node_key_0 == key {
                let val = unsafe{ &mut **self.val_or_child0.val };
                return Some(val);
            }
        }
        if self.is_used_value_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            if node_key_1 == key {
                let val = unsafe{ &mut **self.val_or_child1.val };
                return Some(val);
            }
        }
        None
    }


}

impl<V: Clone> TrieNode<V> for LineListNode<V> {
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)> {
        if self.is_used_child_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            if node_key_0 == &key[..self.key_len_0()] {
                let child = unsafe{ self.val_or_child0.child.borrow() };
                return Some((self.key_len_0(), child))
            }
        }
        if self.is_used_child_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            if node_key_1 == &key[..self.key_len_1()] {
                let child = unsafe{ self.val_or_child1.child.borrow() };
                return Some((self.key_len_1(), child))
            }
        }
        None
    }
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut dyn TrieNode<V>)> {
        if self.is_used_child_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            let key_len = self.key_len_0();
            if node_key_0 == &key[..key_len] {
                let child = unsafe{ &mut *self.val_or_child0.child }.make_mut();
                return Some((key_len, child))
            }
        }
        if self.is_used_child_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            let key_len = self.key_len_1();
            if node_key_1 == &key[..key_len] {
                let child = unsafe{ &mut *self.val_or_child1.child }.make_mut();
                return Some((key_len, child))
            }
        }
        None
    }
    fn node_contains_val(&self, key: &[u8]) -> bool {
        self.contains_val(key)
    }
    fn node_get_val(&self, key: &[u8]) -> Option<&V> {
        self.get_val(key)
    }
    fn node_get_val_mut(&mut self, key: &[u8]) -> Option<&mut V> {
        self.get_val_mut(key)
    }
    fn node_set_val(&mut self, key: &[u8], mut val: V) -> Result<Option<V>, Box<dyn TrieNode<V>>> {
        if self.contains_val(key) {
            let node_val = self.get_val_mut(key).unwrap();
            core::mem::swap(&mut val, node_val);
            return Ok(Some(val));
        }
        if !self.is_used_0() {
            if key.len() <= KEY_BYTES_CNT {
                //The entire key fits within the node
                unsafe{ self.set_val_0(key, val); }
                return Ok(None)
            } else {
                //We need to recursively create a new node to hold the remaining part of the key
                let mut child_node = Self::new();
                child_node.node_set_val(&key[KEY_BYTES_CNT..], val).unwrap_or_else(|_| panic!()); //If a newly created node can't accept the value then it's a bug
                unsafe{ self.set_child_0(&key[..KEY_BYTES_CNT], TrieNodeODRc::new(child_node)); }
                return Ok(None)
            }
        }
        if self.is_available_1() {
            let remaining_key_bytes = KEY_BYTES_CNT - self.key_len_0();
            if key.len() <= remaining_key_bytes {
                //The entire key fits within the node
                unsafe{ self.set_val_1(key, val); }
                return Ok(None)
            } else {
                //We need to recursively create a new node to hold the remaining part of the key
                let mut child_node = Self::new();
                child_node.node_set_val(&key[remaining_key_bytes..], val).unwrap_or_else(|_| panic!("Internal error: Why can't a newly created node accept the value???"));
                unsafe{ self.set_child_1(&key[..remaining_key_bytes], TrieNodeODRc::new(child_node)); }
                return Ok(None)
            }
        }
        //We couldn't store the value in either of the slots, so upgrade the node
        //GOAT.
        //1. If there is a single value, chop the key in half
        //2. If there is a pair, check to see if there is a common prefix between the existing nodes, or the node we're adding
        //3. If there is a pair and no common prefix, upgrade to a node with a higher branching factor
        panic!();
    }

    fn node_update_val(&mut self, key: &[u8], default_f: Box<dyn FnOnce()->V + '_>) -> Result<&mut V, Box<dyn TrieNode<V>>> {
        panic!()
    }

    fn node_is_empty(&self) -> bool {
        panic!()
    }

    fn boxed_node_iter<'a>(&'a self) -> Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a> {
        panic!()
    }

    fn node_subtree_len(&self) -> usize {
        panic!()
    }

    fn item_count(&self) -> usize {
        panic!()
    }

    fn nth_child(&self, n: usize, forward: bool) -> Option<(&[u8], &dyn TrieNode<V>)> {
        panic!()
    }

    fn get_sibling_of_child(&self, key: &[u8], next: bool) -> Option<(&[u8], &dyn TrieNode<V>)> {
        panic!()
    }

    fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice {
        panic!()
    }

    fn join_into_dyn(&mut self, other: TrieNodeODRc<V>) where V: Lattice {
        panic!()
    }

    fn meet_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice {
        panic!()
    }

    fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: PartialDistributiveLattice {
        panic!();
    }

    fn as_dense(&self) -> Option<&DenseByteNode<V>> {
        None
    }

    fn as_dense_mut(&mut self) -> Option<&mut DenseByteNode<V>> {
        None
    }
}

#[test]
fn test_line_list_node() {
    assert_eq!(core::mem::size_of::<LineListNode<[u8; 1024]>>(), 64);

    //A simple test with a V that fits inside 16 bytes, only testing slot_0
    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&42));
    *new_node.node_get_val_mut("hello".as_bytes()).unwrap() = 123;
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&123));
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(Some(123)));
    assert_eq!(new_node.node_contains_val("test".as_bytes()), false);

    //A simple test with a V that exceeds 16 bytes, only testing slot_0
    let mut new_node = LineListNode::<[u128; 4]>::new();
    assert_eq!(new_node.node_set_val("hello".as_bytes(), [0, 1, 2, 3]).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&[0, 1, 2, 3]));
    *new_node.node_get_val_mut("hello".as_bytes()).unwrap() = [3, 2, 1, 0];
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&[3, 2, 1, 0]));
    assert_eq!(new_node.node_contains_val("test".as_bytes()), false);

    //A test using both slots for values, where the keys are different, but both fit inside the key space
    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val("goodbye".as_bytes(), 24).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&42));
    assert_eq!(new_node.node_get_val("goodbye".as_bytes()), Some(&24));

    //A test using both slots, where the second key exceeds the available space.  Make sure recursive nodes
    // are created
    const LONG_KEY: &[u8] = "Pack my box with five dozen liquor jugs".as_bytes();
    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val(LONG_KEY, 24).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&42));
    let (bytes_used, child_node) = new_node.node_get_child(LONG_KEY).unwrap();
    let remaining_key = &LONG_KEY[bytes_used..];
    assert_eq!(child_node.node_get_val(remaining_key), Some(&24));

    //A test using only one slot, where the key exceeds the available space, make sure recursive nodes
    // are created
    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val(LONG_KEY, 24).map_err(|_| 0), Ok(None));
    let (bytes_used, child_node) = new_node.node_get_child(LONG_KEY).unwrap();
    let remaining_key = &LONG_KEY[bytes_used..];
    assert_eq!(child_node.node_get_val(remaining_key), Some(&24));

    //Now make sure that trying to add a second key upgrades the node
    let result = new_node.node_set_val("hello".as_bytes(), 42);
    let replacement_node = result.unwrap_err();


    //A test where the first key exactly fills the available key space.  Make sure the node is upgraded
    // when adding a second key
    //GOAT

    //A test using both slots, where the key ends up being the same for both a value and a child link
    //GOAT

}
