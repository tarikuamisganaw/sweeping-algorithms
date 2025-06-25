
use core::fmt::Debug;
use std::collections::HashMap;

use crate::Allocator;
use crate::trie_node::*;
use crate::ring::*;
use crate::utils::ByteMask;
use crate::dense_byte_node::{DenseByteNode, CellByteNode};
use crate::line_list_node::LineListNode;

pub(crate) static EMPTY_NODE: EmptyNode = EmptyNode;

#[derive(Clone, Copy, Default, Debug)]
pub struct EmptyNode;

impl<V: Clone + Send + Sync, A: Allocator> TrieNode<V, A> for EmptyNode {
    fn node_key_overlap(&self, _key: &[u8]) -> usize {
        0
    }
    fn node_contains_partial_key(&self, _key: &[u8]) -> bool {
        false
    }
    fn node_get_child(&self, _key: &[u8]) -> Option<(usize, &TrieNodeODRc<V, A>)> {
        None
    }
    //GOAT, Deprecated node_get_child_and_val_mut
    // fn node_get_child_and_val_mut(&mut self, _key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>, &mut Option<V>)> {
    //     None
    // }
    fn node_get_child_mut(&mut self, _key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V, A>)> {
        None
    }
    //GOAT, we probably don't need this interface, although it is fully implemented and working
    // fn node_contains_children_exclusive(&self, _keys: &[&[u8]]) -> bool {
    //     true
    // }
    fn node_replace_child(&mut self, _key: &[u8], _new_node: TrieNodeODRc<V, A>) -> &mut dyn TrieNode<V, A> {
        unreachable!() //Should not be called unless it's known that the node being replaced exists
    }
    fn node_get_payloads<'node, 'res>(&'node self, _keys: &[(&[u8], bool)], _results: &'res mut [(usize, PayloadRef<'node, V, A>)]) -> bool {
        true
    }
    fn node_contains_val(&self, _key: &[u8]) -> bool {
        false
    }
    //GOAT, we probably don't need this interface, although it is fully implemented and working
    // fn node_contains_vals_exclusive(&self, _keys: &[&[u8]]) -> bool {
    //     true
    // }
    fn node_get_val(&self, _key: &[u8]) -> Option<&V> {
        None
    }
    fn node_remove_val(&mut self, _key: &[u8]) -> Option<V> {
        None
    }
    fn node_get_val_mut(&mut self, _key: &[u8]) -> Option<&mut V> {
        None
    }
    fn node_set_val(&mut self, _key: &[u8], _val: V) -> Result<(Option<V>, bool), TrieNodeODRc<V, A>> {
        unreachable!() //we should head this off upstream

        //GOAT, dead code
        // #[allow(unused_mut)]
        // let mut replacement_node;
        // #[cfg(all(not(feature = "all_dense_nodes"), not(feature = "bridge_nodes")))]
        // {
        //     replacement_node = crate::line_list_node::LineListNode::new();
        //     replacement_node.node_set_val(key, val).unwrap_or_else(|_| panic!());
        // }
        // #[cfg(all(feature = "bridge_nodes", not(feature = "all_dense_nodes")))]
        // {
        //     replacement_node = crate::bridge_node::BridgeNode::new(key, false, val.into());
        // }
        // #[cfg(feature = "all_dense_nodes")]
        // {
        //     replacement_node = crate::dense_byte_node::DenseByteNode::new();
        //     replacement_node.node_set_val(key, val).unwrap_or_else(|_| panic!());
        // }
        // Err(TrieNodeODRc::new(replacement_node))
    }
    fn node_set_branch(&mut self, _key: &[u8], _new_node: TrieNodeODRc<V, A>) -> Result<bool, TrieNodeODRc<V, A>> {
        unreachable!() //we should head this off upstream

        //GOAT dead code
        // #[allow(unused_mut)]
        // let mut replacement_node;
        // #[cfg(all(not(feature = "all_dense_nodes"), not(feature = "bridge_nodes")))]
        // {
        //     replacement_node = crate::line_list_node::LineListNode::new();
        //     replacement_node.node_set_branch(key, new_node).unwrap_or_else(|_| panic!());
        // }
        // #[cfg(all(feature = "bridge_nodes", not(feature = "all_dense_nodes")))]
        // {
        //     replacement_node = crate::bridge_node::BridgeNode::new(key, true, new_node.into());
        // }
        // #[cfg(feature = "all_dense_nodes")]
        // {
        //     replacement_node = crate::dense_byte_node::DenseByteNode::new();
        //     replacement_node.node_set_branch(key, new_node).unwrap_or_else(|_| panic!());
        // }
        // Err(TrieNodeODRc::new(replacement_node))
    }
    fn node_remove_all_branches(&mut self, _key: &[u8]) -> bool {
        false
    }
    fn node_remove_unmasked_branches(&mut self, _key: &[u8], _mask: ByteMask) {}
    fn node_is_empty(&self) -> bool { true }
    fn new_iter_token(&self) -> u128 {
        0
    }
    fn iter_token_for_path(&self, _key: &[u8]) -> u128 {
        0
    }
    fn next_items(&self, _token: u128) -> (u128, &[u8], Option<&TrieNodeODRc<V, A>>, Option<&V>) {
        (NODE_ITER_FINISHED, &[], None, None)
    }
    fn node_val_count(&self, _cache: &mut HashMap<*const dyn TrieNode<V, A>, usize>) -> usize {
        0
    }
    #[cfg(feature = "counters")]
    fn item_count(&self) -> usize {
        0
    }
    fn node_first_val_depth_along_key(&self, _key: &[u8]) -> Option<usize> {
        None
    }
    fn nth_child_from_key(&self, _key: &[u8], _n: usize) -> (Option<u8>, Option<&dyn TrieNode<V, A>>) {
        (None, None)
    }
    fn first_child_from_key(&self, _key: &[u8]) -> (Option<&[u8]>, Option<&dyn TrieNode<V, A>>) {
        (None, None)
    }
    fn count_branches(&self, _key: &[u8]) -> usize {
        0
    }
    fn node_branches_mask(&self, _key: &[u8]) -> ByteMask {
        ByteMask::EMPTY
    }
    fn is_leaf(&self, _key: &[u8]) -> bool {
        true
    }

    fn prior_branch_key(&self, _key: &[u8]) -> &[u8] {
        &[]
    }

    fn get_sibling_of_child(&self, _key: &[u8], _next: bool) -> (Option<u8>, Option<&dyn TrieNode<V, A>>) {
        (None, None)
    }
    fn get_node_at_key(&self, _key: &[u8]) -> AbstractNodeRef<'_, V, A> {
        AbstractNodeRef::None
    }
    fn take_node_at_key(&mut self, _key: &[u8]) -> Option<TrieNodeODRc<V, A>> {
        None
    }
    fn pjoin_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: Lattice {
        if other.node_is_empty() {
            AlgebraicResult::None
        } else {
            AlgebraicResult::Identity(COUNTER_IDENT)
        }
    }
    fn join_into_dyn(&mut self, other: TrieNodeODRc<V, A>) -> (AlgebraicStatus, Result<(), TrieNodeODRc<V, A>>) where V: Lattice {
        if other.borrow().node_is_empty() {
            (AlgebraicStatus::None, Ok(()))
        } else {
            (AlgebraicStatus::Element, Err(other.clone()))
        }
    }
    fn drop_head_dyn(&mut self, _byte_cnt: usize) -> Option<TrieNodeODRc<V, A>> where V: Lattice {
        None
    }
    fn pmeet_dyn(&self, _other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: Lattice {
        AlgebraicResult::None
    }
    fn psubtract_dyn(&self, _other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: DistributiveLattice {
        AlgebraicResult::None
    }
    fn prestrict_dyn(&self, _other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> {
        AlgebraicResult::None
    }
    fn clone_self(&self) -> TrieNodeODRc<V, A> {
        unreachable!() //If we end up hitting this, we should change it at the call site
    }
}

impl<V: Clone + Send + Sync, A: Allocator> TrieNodeDowncast<V, A> for EmptyNode {
    #[inline]
    fn tag(&self) -> usize {
        EMPTY_NODE_TAG
    }
    fn as_tagged(&self) -> TaggedNodeRef<'_, V, A> {
        TaggedNodeRef::empty_node()
    }
    fn as_tagged_mut(&mut self) -> TaggedNodeRefMut<'_, V, A> {
        TaggedNodeRefMut::Unsupported
    }
    fn convert_to_cell_node(&mut self) -> TrieNodeODRc<V, A> {
        unreachable!() //If we end up hitting this, we should change it at the call site
    }
    unsafe fn as_dense_unchecked(&self) -> &DenseByteNode<V, A> {
        unreachable!()
    }
    unsafe fn as_list_unchecked(&self) -> &LineListNode<V, A> {
        unreachable!()
    }
    unsafe fn as_cell_unchecked(&self) -> &CellByteNode<V, A> {
        unreachable!()
    }
}
