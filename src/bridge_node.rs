
use core::mem::{MaybeUninit, ManuallyDrop};
use core::fmt::{Debug, Formatter};
use std::collections::HashMap;

use crate::trie_node::*;
use crate::ring::*;
use crate::line_list_node::{LineListNode, ValOrChildUnion, find_prefix_overlap};
use crate::dense_byte_node::DenseByteNode;
use crate::tiny_node::TinyRefNode;

/// A node type that only has a single value or onward link
pub struct BridgeNode<V> {
    key_bytes: [MaybeUninit<u8>; KEY_BYTES_CNT],
    /// bit 7 = used
    /// bit 6 = is_child
    /// bit 5 to bit 0 = key_len
    header: u8,
    payload: ValOrChildUnion<V>
}

const KEY_BYTES_CNT: usize = 31;

impl<V> Drop for BridgeNode<V> {
    fn drop(&mut self) {
        if self.is_used_child() {
            unsafe{ ManuallyDrop::drop(&mut self.payload.child) }
        }
        if self.is_used_val() {
            unsafe{ ManuallyDrop::drop(&mut self.payload.val) }
        }
    }
}

impl<V: Clone> Clone for BridgeNode<V> {
    fn clone(&self) -> Self {
        let is_used_child = self.is_used_child();
        let is_used_val = self.is_used_val();
        let payload = if is_used_child || is_used_val {
            if is_used_child {
                let child = unsafe{ &self.payload.child }.clone();
                ValOrChildUnion{ child }
            } else {
                let val = unsafe{ &self.payload.val }.clone();
                ValOrChildUnion{ val }
            }
        } else {
            ValOrChildUnion{ _unused: () }
        };
        Self {
            header: self.header,
            key_bytes: self.key_bytes,
            payload,
        }
    }
}

impl<V> Debug for BridgeNode<V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let key = if !self.is_empty() {
            let key = self.key();
            match std::str::from_utf8(key) {
                Ok(str) => str.to_string(),
                Err(_) => format!("{key:?}")
            }
        } else {
            "".to_string()
        };
        write!(f, "BridgeNode (occupied={} is_child={} key={:?})", !self.is_empty(), self.is_child_ptr(), key)
    }
}

impl<V> BridgeNode<V> {
    fn header(is_child: bool, key_len: usize) -> u8 {
        debug_assert!(key_len <= KEY_BYTES_CNT);
        if is_child {
            ((1 << 7) | (1 << 6) | key_len) as u8
        } else {
            ((1 << 7) | key_len) as u8
        }
    }
    fn is_empty(&self) -> bool {
        self.header & (1 << 7) == 0
    }
    fn is_child_ptr(&self) -> bool {
        self.header & (1 << 6) > 0
    }
    fn is_used_child(&self) -> bool {
        self.header & ((1 << 7) | (1 << 6)) == ((1 << 7) | (1 << 6))
    }
    fn is_used_val(&self) -> bool {
        self.header & ((1 << 7) | (1 << 6)) == (1 << 7)
    }
    fn key_len(&self) -> usize {
        (self.header & 0x3f) as usize
    }
    fn key(&self) -> &[u8] {
        unsafe{ core::slice::from_raw_parts(self.key_bytes.as_ptr().cast(), self.key_len()) }
    }
}

impl<V: Clone> BridgeNode<V> {
    pub fn new(key: &[u8], is_child: bool, payload: ValOrChildUnion<V>) -> Self {
        debug_assert!(key.len() > 0);
        if key.len() <= KEY_BYTES_CNT {
            let mut new_node = Self {
                header: Self::header(is_child, key.len()),
                key_bytes: [MaybeUninit::uninit(); KEY_BYTES_CNT],
                payload
            };
            unsafe{ core::ptr::copy_nonoverlapping(key.as_ptr(), new_node.key_bytes.as_mut_ptr().cast(), key.len()); }
            new_node
        } else {
            let child_node = Self::new(&key[KEY_BYTES_CNT..], is_child, payload);
            let mut new_node = Self {
                header: Self::header(true, KEY_BYTES_CNT),
                key_bytes: [MaybeUninit::uninit(); KEY_BYTES_CNT],
                payload: TrieNodeODRc::new(child_node).into(),
            };
            unsafe{ core::ptr::copy_nonoverlapping(key.as_ptr(), new_node.key_bytes.as_mut_ptr().cast(), KEY_BYTES_CNT); }
            new_node
        }
    }
    fn set_payload(&mut self, key: &[u8], is_child: bool, payload: ValOrChildUnion<V>) {
        debug_assert!(key.len() > 0);
        debug_assert!(key.len() < KEY_BYTES_CNT);
        debug_assert!(self.is_empty());
        self.header = Self::header(is_child, key.len());
        self.payload = payload;
        unsafe{ core::ptr::copy_nonoverlapping(key.as_ptr(), self.key_bytes.as_mut_ptr().cast(), key.len()); }
    }
    /// Clones the payload from self
    fn clone_payload(&self) -> Option<ValOrChild<V>> {
        if self.is_empty() {
            return None;
        } else {
            match self.is_child_ptr() {
                true => {
                    let child = unsafe{ &*self.payload.child }.clone();
                    Some(ValOrChild::Child(child))
                },
                false => {
                    let val = unsafe{ &**self.payload.val }.clone();
                    Some(ValOrChild::Val(val))
                }
            }
        }
    }
    /// Takes the payload from self, leaving self empty, but with `key()`` and `is_child_ptr()` continuing
    /// to return the old information
    fn take_payload(&mut self) -> ValOrChildUnion<V> {
        debug_assert_eq!(self.is_empty(), false);
        self.header &= !(1 << 7);
        core::mem::take(&mut self.payload)
    }
}

impl<V: Clone> TrieNode<V> for BridgeNode<V> {
    fn node_contains_partial_key(&self, key: &[u8]) -> bool {
        debug_assert!(!self.is_empty());
        if self.key().starts_with(key) {
            true
        } else {
            false
        }
    }
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)> {
        if self.is_used_child() {
            let node_key = self.key();
            let key_len = node_key.len();
            if key.len() >= key_len {
                if node_key == &key[..key_len] {
                    let child = unsafe{ &*self.payload.child }.borrow();
                    return Some((key_len, child))
                }
            }
        }
        None
    }
    fn node_get_child_and_val_mut(&mut self, _key: &[u8]) -> Option<(usize, Option<&mut V>, Option<&mut TrieNodeODRc<V>>)> { unreachable!() }
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>)> {
        if self.is_used_child() {
            let node_key = self.key();
            let key_len = node_key.len();
            if key.len() >= key_len {
                if node_key == &key[..key_len] {
                    let child = unsafe{ &mut *self.payload.child };
                    return Some((key_len, child))
                }
            }
        }
        None
    }
    fn node_replace_child(&mut self, _key: &[u8], _new_node: TrieNodeODRc<V>) -> &mut dyn TrieNode<V> { unreachable!() }
    fn node_contains_val(&self, key: &[u8]) -> bool {
        if self.is_used_val() {
            let node_key = self.key();
            if node_key == key {
                return true;
            }
        }
        false
    }
    fn node_get_val(&self, key: &[u8]) -> Option<&V> {
        if self.is_used_val() {
            let node_key = self.key();
            if node_key == key {
                let val = unsafe{ &**self.payload.val };
                return Some(val);
            }
        }
        None
    }
    fn node_remove_val(&mut self, _key: &[u8]) -> Option<V> { unreachable!() }
    fn node_get_val_mut(&mut self, _key: &[u8]) -> Option<&mut V> { unreachable!() }
    fn node_set_val(&mut self, key: &[u8], val: V) -> Result<(Option<V>, bool), TrieNodeODRc<V>> {
        const IS_CHILD: bool = false; //GOAT, in anticipation of refactoring
        debug_assert_eq!(self.is_empty(), false);
        let node_key = self.key();
        let mut overlap = find_prefix_overlap(key, node_key);
        if overlap > 0 {
            //If the keys are an exact match and the payload is the same type, replace the payload
            if overlap == node_key.len() && overlap == key.len() && IS_CHILD == self.is_child_ptr() {
                let mut return_val = ValOrChildUnion::from(val);
                core::mem::swap(&mut return_val, &mut self.payload);
                return Ok((Some(unsafe{ return_val.into_val() }), false))
            }

            //Make sure we have some key to work with, for the new split node
            if overlap == node_key.len() || overlap == key.len() {
                overlap -= 1;
            }

            //Make a new node containing what's left of self and the newly added payload
            let mut replacement_node = DenseByteNode::<V>::with_capacity(2);
            let self_payload = self.take_payload();
            replacement_node.add_payload(&self.key()[overlap..], self.is_child_ptr(), self_payload);
            replacement_node.add_payload(&key[overlap..], false, val.into());

            //If we still have some overlap, split this node's key, If not, replace this node entirely
            if overlap > 0 {
                self.set_payload(&key[..overlap], true, TrieNodeODRc::new(replacement_node).into());
                Ok((None, true))
            } else {
                Err(TrieNodeODRc::new(replacement_node))
            }
        } else {
            //We have no overlap, so we should replace this node
            let mut replacement_node = DenseByteNode::<V>::with_capacity(2);
            let self_payload = self.take_payload();
            replacement_node.add_payload(self.key(), self.is_child_ptr(), self_payload);
            replacement_node.add_payload(key, false, val.into());
            Err(TrieNodeODRc::new(replacement_node))
        }
    }
    fn node_set_branch(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> Result<bool, TrieNodeODRc<V>> {
        //GOAT, factor this with node_set_val
        panic!()
        // let mut replacement_node = self.into_full().unwrap();
        // replacement_node.node_set_branch(key, new_node).unwrap_or_else(|_| panic!());
        // Err(TrieNodeODRc::new(replacement_node))
    }
    fn node_remove_all_branches(&mut self, _key: &[u8]) -> bool { unreachable!() }
    fn node_remove_unmasked_branches(&mut self, _key: &[u8], _mask: [u64; 4]) { unreachable!() }
    fn node_is_empty(&self) -> bool {
        self.is_empty()
    }
    fn boxed_node_iter<'n>(&'n self) -> Box<dyn Iterator<Item=(&'n[u8], ValOrChildRef<'n, V>)> + 'n> { unreachable!() }
    fn node_val_count(&self, _cache: &mut HashMap<*const dyn TrieNode<V>, usize>) -> usize {
        panic!();
    }
    #[cfg(feature = "counters")]
    fn item_count(&self) -> usize {
        if self.is_empty() {
            0
        } else {
            1
        }
    }
    fn node_first_val_depth_along_key(&self, key: &[u8]) -> Option<usize> {
        debug_assert!(key.len() > 0);
        debug_assert!(!self.is_empty());
        let node_key = self.key();
        if self.is_used_val() && key.starts_with(node_key) {
            Some(node_key.len() - 1)
        } else {
            None
        }
    }
    fn nth_child_from_key(&self, _key: &[u8], _n: usize) -> (Option<u8>, Option<&dyn TrieNode<V>>) {
        panic!();
    }
    fn first_child_from_key(&self, _key: &[u8]) -> (Option<&[u8]>, Option<&dyn TrieNode<V>>) {
        panic!();
    }
    fn count_branches(&self, _key: &[u8]) -> usize {
        panic!();
    }
    fn node_branches_mask(&self, _key: &[u8]) -> [u64; 4] {
        panic!();
    }
    fn is_leaf(&self, _key: &[u8]) -> bool {
        panic!();
    }
    fn prior_branch_key(&self, _key: &[u8]) -> &[u8] {
        panic!();
    }
    fn get_sibling_of_child(&self, _key: &[u8], _next: bool) -> (Option<u8>, Option<&dyn TrieNode<V>>) {
        panic!();
    }
    fn get_node_at_key(&self, key: &[u8]) -> AbstractNodeRef<V> {
        debug_assert!(!self.is_empty());

        //Zero-length key means borrow this node
        if key.len() == 0 {
            return AbstractNodeRef::BorrowedDyn(self)
        }

        //Exact match with a path to a child node means return that node
        let node_key = self.key();
        if self.is_used_child() && node_key == key {
            return AbstractNodeRef::BorrowedRc(unsafe{ &*self.payload.child })
        }

        //Otherwise check to see if we need to make a sub-node
        if node_key.len() > key.len() && node_key.starts_with(key) {
            let new_key = &node_key[key.len()..];
            let ref_node = TinyRefNode::new(self.is_child_ptr(), new_key, &self.payload);
            return AbstractNodeRef::BorrowedTiny(ref_node)
        }

        //The key fails to specify a path contained within the node
        AbstractNodeRef::None
    }
    fn take_node_at_key(&mut self, _key: &[u8]) -> Option<TrieNodeODRc<V>> { unreachable!() }
    fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice {
        panic!();
    }
    fn join_into_dyn(&mut self, mut _other: TrieNodeODRc<V>) where V: Lattice { unreachable!() }
    fn drop_head_dyn(&mut self, _byte_cnt: usize) -> Option<TrieNodeODRc<V>> where V: Lattice { unreachable!() }
    fn meet_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: Lattice {
        panic!();
    }
    fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> (bool, Option<TrieNodeODRc<V>>) where V: PartialDistributiveLattice {
        panic!();
    }
    fn prestrict_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> {
        panic!();
    }
    fn as_dense(&self) -> Option<&DenseByteNode<V>> {
        None
    }
    fn as_dense_mut(&mut self) -> Option<&mut DenseByteNode<V>> {
        None
    }
    fn as_list(&self) -> Option<&LineListNode<V>> {
        None
    }
    fn as_list_mut(&mut self) -> Option<&mut LineListNode<V>> {
        None
    }
    fn clone_self(&self) -> TrieNodeODRc<V> {
        TrieNodeODRc::new(self.clone())
    }
}

#[test]
fn test_bridge_node() {
    //First confirm LineListNode is 48 bytes
    assert_eq!(std::mem::size_of::<LineListNode::<()>>(), 48);

    //Test recursive BridgeNode creation
    let payload: ValOrChildUnion<usize> = 42.into();
    let new_node = BridgeNode::<usize>::new(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz", false, payload);
    assert_eq!(new_node.key(), b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcde");
    assert_eq!(new_node.is_child_ptr(), true);
    let (consumed_bytes, child_node) = new_node.node_get_child(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz").unwrap();
    assert_eq!(consumed_bytes, KEY_BYTES_CNT);
    let check_val = child_node.node_get_val(b"fghijklmnopqrstuvwxyz").unwrap();
    assert_eq!(*check_val, 42);

    //Pathological case where the key.len() is exactly KEY_BYTES_CNT
    let payload: ValOrChildUnion<usize> = 42.into();
    let new_node = BridgeNode::<usize>::new(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcde", false, payload);
    assert_eq!(new_node.key().len(), KEY_BYTES_CNT); //To make sure the test remains valid, if KEY_BYTES_CNT is changed
    assert_eq!(new_node.key(), b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcde");
    assert_eq!(new_node.is_child_ptr(), false);
    let check_val = new_node.node_get_val(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcde").unwrap();
    assert_eq!(*check_val, 42);
}
