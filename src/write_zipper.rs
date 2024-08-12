
use mutcursor::MutCursorRootedVec;

use crate::trie_node::{TrieNode, TrieNodeODRc, AbstractNodeRef};
use crate::trie_map::BytesTrieMap;
use crate::empty_node::EmptyNode;
use crate::zipper::*;
use crate::zipper::zipper_priv::*;
use crate::ring::{Lattice, PartialDistributiveLattice};
#[cfg(feature = "all_dense_nodes")]
use crate::dense_byte_node::DenseByteNode;
#[cfg(not(feature = "all_dense_nodes"))]
use crate::line_list_node::LineListNode;

/// A [Zipper] for editing and adding paths and values in the trie
pub struct WriteZipper<'a, 'k, V> {
    key: KeyFields<'k>,
    /// The stack of node references.  We need a "rooted" Vec in case we need to upgrade the node at the root of the zipper
    focus_stack: MutCursorRootedVec<'a, TrieNodeODRc<V>, dyn TrieNode<V>>,
}

/// The part of the [WriteZipper] that contains the key-related fields.  So it can be borrowed separately
struct KeyFields<'k> {
    /// A reference to the part of the key within the root node that represents the zipper root
    root_key: &'k [u8],
    /// Stores the entire path from the root node, including the bytes from root_key
    prefix_buf: Vec<u8>,
    /// Stores the lengths for each successive node's key
    prefix_idx: Vec<usize>,
}

impl<'a, 'k, V: Clone> Zipper<'a> for WriteZipper<'a, 'k, V> {

    fn at_root(&self) -> bool {
        self.key.prefix_buf.len() <= self.key.root_key.len()
    }

    fn reset(&mut self) {
        self.focus_stack.to_root();
        self.focus_stack.advance_from_root(|root| Some(root.make_mut()));
        self.key.prefix_buf.truncate(self.key.root_key.len());
        self.key.prefix_idx.clear();
    }

    fn path(&self) -> &[u8] {
        if self.key.prefix_buf.len() > 0 {
            &self.key.prefix_buf[self.key.root_key.len()..]
        } else {
            &[]
        }
    }

    fn path_exists(&self) -> bool {
        let key = self.key.node_key();
        if key.len() > 0 {
            self.focus_stack.top().unwrap().node_contains_partial_key(key)
        } else {
            true
        }
    }

    fn is_value(&self) -> bool {
        self.focus_stack.top().unwrap().node_contains_val(self.key.node_key())
    }

    fn val_count(&self) -> usize {
        let focus = self.get_focus();
        if focus.is_none() {
            0
        } else {
            focus.borrow().node_subtree_len() + (self.is_value() as usize)
        }
    }

    fn child_count(&self) -> usize {
        let focus_node = self.focus_stack.top().unwrap();
        let node_key = self.key.node_key();

        //Special case for the root
        if node_key.len() == 0 {
            return focus_node.child_count_at_key(b"");
        }

        match focus_node.node_get_child(node_key) {
            Some((consumed_bytes, child_node)) => {
                if node_key.len() >= consumed_bytes {
                    child_node.child_count_at_key(&node_key[consumed_bytes..])
                } else {
                    0
                }
            },
            None => focus_node.child_count_at_key(node_key)
        }
    }

    fn child_mask(&self) -> [u64; 4] {
        let focus_node = self.focus_stack.top().unwrap();
        let node_key = self.key.node_key();
        match focus_node.node_get_child(node_key) {
            Some((consumed_bytes, child_node)) => {
                if node_key.len() >= consumed_bytes {
                    child_node.child_mask_at_key(&node_key[consumed_bytes..])
                } else {
                    [0; 4]
                }
            },
            None => focus_node.child_mask_at_key(node_key)
        }
    }

    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) -> bool {
        let key = k.as_ref();
        self.key.prepare_buffers();
        self.key.prefix_buf.extend(key);
        self.descend_to_internal();
        self.focus_stack.top().unwrap().node_contains_partial_key(self.key.node_key())
    }

    fn descend_indexed_child(&mut self, child_idx: usize) -> bool {
        panic!()
    }

    fn descend_until(&mut self) -> bool {
        panic!()
    }

    fn to_sibling(&mut self, next: bool) -> bool {
        panic!()
    }

    fn ascend(&mut self, mut steps: usize) -> bool {
        while steps > 0 {
            if self.key.excess_key_len() == 0 {
                if self.at_root() {
                    return false;
                }
                self.ascend_across_nodes();
            }
            debug_assert!(self.key.node_key().len() > 0);
            let cur_jump = steps.min(self.key.excess_key_len());
            self.key.prefix_buf.truncate(self.key.prefix_buf.len() - cur_jump);
            steps -= cur_jump;
        }
        true
    }

    fn ascend_until(&mut self) -> bool {
        if self.at_root() {
            return false;
        }
        loop {
            self.ascend_within_node();
            if self.at_root() {
                return true;
            }
            if self.key.node_key().len() == 0 {
                self.ascend_across_nodes();
            }
            if self.child_count() > 1 {
                break;
            }
        }
        debug_assert!(self.key.node_key().len() > 0); //We should never finish with a zero-length node-key
        true
    }

    fn fork_zipper(&self) -> ReadZipper<V> {
        let new_root_val = self.get_value();
        ReadZipper::new_with_node_and_path_internal(self.focus_stack.top().unwrap(), &self.key.root_key, None, new_root_val)
    }

    fn make_map(&self) -> Option<BytesTrieMap<Self::V>> {
        self.get_focus().into_option().map(|node| BytesTrieMap::new_with_root(node))
    }
}

impl<'a, 'k, V : Clone> zipper_priv::ZipperPriv for WriteZipper<'a, 'k, V> {
    type V = V;

    fn get_focus(&self) -> AbstractNodeRef<Self::V> {
        self.focus_stack.top().unwrap().get_node_at_key(self.key.node_key())
    }
}

impl <'a, 'k, V : Clone> WriteZipper<'a, 'k, V> {
    /// Creates a new zipper, with a path relative to a node
    pub(crate) fn new_with_node_and_path(root_node: &'a mut TrieNodeODRc<V>, path: &'k [u8]) -> Self {
        let (key, node) = node_along_path_mut(root_node, path);
        Self::new_with_node_and_path_internal(node, key)
    }
    /// Creates a new zipper, with a path relative to a node, assuming the path is fully-contained within
    /// the node
    ///
    /// NOTE: This method currently doesn't descend subnodes.  Use [Self::new_with_node_and_path] if you can't
    /// guarantee the path is within the supplied node.
    pub(crate) fn new_with_node_and_path_internal(root_node: &'a mut TrieNodeODRc<V>, path: &'k [u8]) -> Self {
        let mut focus_stack = MutCursorRootedVec::new(root_node);
        focus_stack.advance_from_root(|root| Some(root.make_mut()));
        Self {
            key: KeyFields::new(path),
            focus_stack,
        }
    }
    /// Returns a refernce to the value at the zipper's focus, or `None` if there is no value
    pub fn get_value(&self) -> Option<&V> {
        self.focus_stack.top().unwrap().node_get_val(self.key.node_key())
    }
    /// Returns a mutable reference to a value at the zipper's focus, or None if no value exists
    pub fn get_value_mut(&mut self) -> Option<&mut V> {
        self.focus_stack.top_mut().unwrap().node_get_val_mut(self.key.node_key())
    }
    /// Returns a mutable reference to the value at the zipper's focus, inserting `default` if no value exists
    pub fn get_value_or_insert(&mut self, default: V) -> &mut V {
        let created_subnode = self.in_zipper_mut_static_result(
            |node, key| {
                if !node.node_contains_val(key) {
                    node.node_set_val(key, default).map(|(_old_val, created_subnode)| created_subnode)
                } else {
                    Ok(false)
                }
            },
            |_, _| true);
        if created_subnode {
            self.mend_root();
            self.descend_to_internal();
        }
        self.get_value_mut().unwrap()
    }
    /// Returns a mutable reference to the value at the zipper's focus, inserting the result of `func` if no
    /// value exists
    pub fn get_value_or_insert_with<F>(&mut self, func: F) -> &mut V
        where F: FnOnce() -> V
    {
        let created_subnode = self.in_zipper_mut_static_result(
            |node, key| {
                if !node.node_contains_val(key) {
                    node.node_set_val(key, func()).map(|(_old_val, created_subnode)| created_subnode)
                } else {
                    Ok(false)
                }
            },
            |_, _| true);
        if created_subnode {
            self.mend_root();
            self.descend_to_internal();
        }
        self.get_value_mut().unwrap()
    }

    /// Sets the value at the zipper's focus
    ///
    /// Returns `Some(replaced_val)` if an existing value was replaced, otherwise returns `None` if
    /// the value was added without replacing anything.
    ///
    /// Panics if the zipper's focus is unable to hold a value
    pub fn set_value(&mut self, val: V) -> Option<V> {
        let (old_val, created_subnode) = self.in_zipper_mut_static_result(
            |node, remaining_key| node.node_set_val(remaining_key, val),
            |_new_leaf_node, _remaining_key| (None, false));
        if created_subnode {
            self.mend_root();
            self.descend_to_internal();
        }
        old_val
    }

    /// Removes the value at the zipper's focus.  Does not affect any onward branches.  Returns `Some(val)`
    /// with the value that was removed, otherwise returns `None`
    ///
    /// WARNING: This method may cause the trie to be pruned above the zipper's focus, and may result in
    /// [Self::path_exists] returning `false`, where it previously returned `true`
    pub fn remove_value(&mut self) -> Option<V> {
        let focus_node = self.focus_stack.top_mut().unwrap();
        if let Some(result) = focus_node.node_remove_val(self.key.node_key()) {
            if focus_node.node_is_empty() {
                self.prune_path();
            }
            Some(result)
        } else {
            None
        }
    }

    /// Replaces the trie below the zipper's focus with the subtrie downstream from the focus of `read_zipper`
    ///
    /// If there is a value at the zipper's focus, it will not be affected.
    ///
    /// WARNING: If the `read_zipper` is not on an existing path (according to [Zipper::path_exists]) then the
    /// effect will be the same as [Self::remove_branch] causing the trie to be pruned below the graft location.
    /// Since dangling paths aren't allowed, This method may cause the trie to be pruned above the zipper's focus,
    /// and may lead to [Self::path_exists] returning `false`, where it previously returned `true`
    pub fn graft<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) {
        self.graft_internal(read_zipper.get_focus().into_option())
    }

    /// Replaces the trie below the zipper's focus with the contents of a [BytesTrieMap], consuming the map
    ///
    /// If there is a value at the zipper's focus, it will not be affected.
    ///
    /// WARNING: If the `map` is empty then the effect will be the same as [Self::remove_branch] causing the
    /// trie to be pruned below the graft location.  Since dangling paths aren't allowed, This method may cause
    /// the trie to be pruned above the zipper's focus, and may lead to [Self::path_exists] returning `false`,
    /// where it previously returned `true`
    pub fn graft_map(&mut self, map: BytesTrieMap<V>) {
        self.graft_internal(map.into_root());
    }

    /// Joins (union of) the subtrie below the zipper's focus with the subtrie downstream from the focus of
    /// `read_zipper`
    ///
    /// Returns `true` if the join was sucessful, or `false` if `read_zipper` was at a nonexistent path.
    ///
    /// If the &self zipper is at a path that does not exist, this method behaves like graft.
    pub fn join<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) -> bool where V: Lattice {
        let src = read_zipper.get_focus();
        if src.is_none() {
            return false
        }
        match self.get_focus().borrow_option() {
            Some(self_node) => {
                let joined = self_node.join_dyn(src.borrow());
                self.graft_internal(Some(joined));
                true
            },
            None => { self.graft_internal(src.into_option()); true }
        }
    }

    /// Joins (union of) the trie below the zipper's focus with the contents of a [BytesTrieMap],
    /// consuming the map
    ///
    /// Returns `true` if the join was sucessful, or `false` if `map` was empty.
    pub fn join_map(&mut self, map: BytesTrieMap<V>) -> bool where V: Lattice {
        let src = match map.into_root() {
            Some(src) => src,
            None => return false
        };
        match self.get_focus().borrow_option() {
            Some(self_node) => {
                let joined = self_node.join_dyn(src.borrow());
                self.graft_internal(Some(joined));
                true
            },
            None => { self.graft_internal(Some(src)); true }
        }
    }

    /// GOAT!! This method needs to take a WriteZipper.  Taking a ReadZipper should not be allowed...
    /// The ReadZipper should not have the ability to modify the paths its reading from.
    /// This ends up being safe in a Rust sense (memory integrity is preserved), because exclusivity on
    /// the node is checked at runtime, but I think it violates the expectation that ReadZippers don't
    /// modify the trie, and also it could lead to a panic if one ReadZipper ends up editing a tree that
    /// another ReadZipper is traversing.
    pub fn join_into<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) -> bool where V: Lattice {
        let src = read_zipper.get_focus();
        if src.is_none() {
            return false
        }
        match self.get_focus().into_option() {
            Some(mut self_node) => {
                self_node.make_mut().join_into_dyn(src.into_option().unwrap());
                true 
            },
            None => { self.graft_internal(src.into_option()); true }
        }
        //GOAT!!!!!  We should prune the path at the source zipper, since we're effectively leaving behind an empty node
    }

    /// Collapses all the paths below the zipper's focus by removing the leading `byte_cnt` bytes from
    /// each path and joining together all of the downstream sub-paths
    ///
    /// Returns `true` if the focus has at least one downstream continuation, otherwise returns `false`.
    ///
    /// NOTE: This method may prune the path upstream of the focus of the operation resulted in removing all
    /// downstream paths.  This means that [Zipper::path_exists] may return `false` after this operation.
    pub fn drop_head(&mut self, byte_cnt: usize) -> bool where V: Lattice {
        match self.get_focus().into_option() {
            Some(mut self_node) => {
                match self_node.make_mut().drop_head_dyn(byte_cnt) {
                    Some(new_node) => {
                        self.graft_internal(Some(new_node));
                        true
                    },
                    None => { false }
                }
            },
            None => { false }
        }
        //GOAT!!!!!  We should prune the path upstream, if we ended up removing all downstream paths
    }

// GOAT, should we rename `drop_head` to `drop_prefix`?  Or rename `insert_prefix` to `insert_head`?
// GOAT QUESTION: Do we want to change the behavior to move the value as well?  Or do we want a variant
//  of this method that moves the value?  The main guiding idea behind not shifting the value was the desire
//  to preserve the property of being the inverse of drop_head.
    /// Inserts `prefix` in front of every downstream path at the focus
    ///
    /// This method does not affect a value at the focus.
    ///
    /// NOTE: This is the inverse of [Self::drop_head], although it cannot perfectly undo `drop_head` because
    /// `drop_head` loses information about the prior nested structure.  However, `drop_head` will undo this
    /// operation.
    pub fn insert_prefix<K: AsRef<[u8]>>(&mut self, prefix: K) -> bool {
        let prefix = prefix.as_ref();
        match self.get_focus().into_option() {
            Some(mut focus_node) => {
                let focus_node = core::mem::take(&mut focus_node);
                let prefixed = make_parents(prefix, focus_node);
                self.graft_internal(Some(prefixed));
                true
            },
            None => { false }
        }
    }

    /// Meets (retains the intersection of) the subtrie below the zipper's focus with the subtrie downstream
    /// from the focus of `read_zipper`
    ///
    /// Returns `true` if the meet was sucessful, or `false` if either `self` of `read_zipper` is at a
    /// nonexistent path.
    pub fn meet<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) -> bool where V: Lattice {
        let src = read_zipper.get_focus();
        if src.is_none() {
            return false
        }
        match self.get_focus().borrow_option() {
            Some(self_node) => {
                let joined = self_node.meet_dyn(src.borrow());
                self.graft_internal(Some(joined));
                true
            },
            None => false
        }
    }

    /// Experiment.  GOAT, document this
    pub fn meet_2<'z, ZA: Zipper<'z, V=V>, ZB: Zipper<'z, V=V>>(&mut self, rz_a: &ZA, rz_b: &ZB) -> bool where V: Lattice {
        let a_focus = rz_a.get_focus();
        let a = match a_focus.borrow_option() {
            Some(src) => src,
            None => return false
        };
        let b_focus = rz_b.get_focus();
        let b = match b_focus.borrow_option() {
            Some(src) => src,
            None => return false
        };
        let joined = a.meet_dyn(b);
        self.graft_internal(Some(joined));
        true
    }

    /// Subtracts the subtrie downstream of the focus of `read_zipper` from the subtrie below the zipper's
    /// focus
    ///
    /// Returns `true` if the subtraction was sucessful, or `false` if either `self` of `read_zipper` is at a
    /// nonexistent path.
    pub fn subtract<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) -> bool where V: PartialDistributiveLattice {
        let src = read_zipper.get_focus();
        if src.is_none() {
            return false
        }
        match self.get_focus().borrow_option() {
            Some(self_node) => {
                let joined = self_node.psubtract_dyn(src.borrow());
                self.graft_internal(joined);
                true
            },
            None => false
        }
    }

    /// Restricts paths in the subtrie downstream of the `self` focus to paths prefixed by a path to a value in
    /// `read_zipper`
    ///
    /// Returns `true` if the restriction was sucessful, or `false` if either `self` of `read_zipper` is at a
    /// nonexistent path.
    pub fn restrict<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) -> bool where V: PartialDistributiveLattice {
        let src = read_zipper.get_focus();
        if src.is_none() {
            return false
        }
        match self.get_focus().borrow_option() {
            Some(self_node) => {
                let restricted = self_node.prestrict_dyn(src.borrow());
                self.graft_internal(restricted);
                true
            },
            None => false
        }
    }

    /// Populates the "stem" paths in `self` with the corresponding subtries in `read_zipper`
    ///
    /// NOTE: Any stem path without a corresponding path in `read_zipper` will be removed from `self`.
    ///
    /// GOAT, I feel like `restricting` might not be a very evocative name here.  The way I think of this
    /// operation is as a bunch of "stems" in the WriteZipper, that get their downstream contents populated
    /// by the corresponding paths in the ReadZipper.  Ideas for names are: "blossom", "fill_in", "expound",
    /// "populate", etc.  I avoided "bloom" and "expand" because those both have other connotations.
    pub fn restricting<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) -> bool where V: PartialDistributiveLattice {
        let src = read_zipper.get_focus();
        if src.is_none() {
            return false
        }
        match self.get_focus().borrow_option() {
            Some(self_node) => {
                let restricted = src.borrow().prestrict_dyn(self_node);
                self.graft_internal(restricted);
                true
            },
            None => false
        }
    }

    /// Removes the branch below the zipper's focus.  Does not affect the value if there is one.  Returns `true`
    /// if a branch was removed, otherwise returns `false`
    ///
    /// WARNING: This method may cause the trie to be pruned above the zipper's focus, and may result in
    /// [Self::path_exists] returning `false`, where it previously returned `true`
    pub fn remove_branch(&mut self) -> bool {
        let focus_node = self.focus_stack.top_mut().unwrap();
        if focus_node.node_remove_branch(self.key.node_key()) {
            if focus_node.node_is_empty() {
                self.prune_path();
            }
            true
        } else {
            false
        }
    }

    /// Creates a new [BytesTrieMap] from the zipper's focus, removing all downstream branches from the zipper
    pub fn take_map(&mut self) -> Option<BytesTrieMap<V>> {
        self.take_focus().map(|node| BytesTrieMap::new_with_root(node))
    }

    /// Internal method, Removes and returns the node at the zipper's focus
    #[inline]
    fn take_focus(&mut self) -> Option<TrieNodeODRc<V>> {
        let focus_node = self.focus_stack.top_mut().unwrap();
        let node_key = self.key.node_key();
        if node_key.len() == 0 {
            debug_assert!(self.at_root());
            let mut replacement_node = TrieNodeODRc::new(EmptyNode::new());
            self.focus_stack.backtrack();
            core::mem::swap(self.focus_stack.root_mut().unwrap(), &mut replacement_node);
            self.focus_stack.advance_from_root(|root| Some(root.make_mut()));
            if !replacement_node.borrow().node_is_empty() {
                Some(replacement_node)
            } else {
                None
            }
        } else {
            debug_assert!(node_key.len() > 0);
            if let Some(new_node) = focus_node.take_node_at_key(node_key) {
                if focus_node.node_is_empty() {
                    self.prune_path();
                }
                Some(new_node)
            } else {
                None
            }
        }
    }

    /// Internal implementation of graft, and other methods that do the same thing
    #[inline]
    fn graft_internal(&mut self, src: Option<TrieNodeODRc<V>>) {
        match src {
            Some(src) => {
                debug_assert!(!src.borrow().node_is_empty());
                let node_key = self.key.node_key();
                if node_key.len() > 0 {
                    let sub_branch_added = match self.focus_stack.top_mut().unwrap().node_set_branch(node_key, src) {
                        Ok(sub_branch_added) => sub_branch_added,
                        Err(_replacement_node) => {
                            panic!(); //TODO
                        }
                    };
                    if sub_branch_added {
                        self.mend_root();
                        self.descend_to_internal();
                    }
                } else {
                    debug_assert_eq!(self.focus_stack.depth(), 1);
                    self.focus_stack.to_root();
                    *self.focus_stack.root_mut().unwrap() = src;
                    self.focus_stack.advance_from_root(|root| Some(root.make_mut()));
                }
            },
            None => { self.remove_branch(); }
        }
    }

    /// An internal function to attempt a mutable operation on a node, and replace the node if the node needed
    /// to be upgraded
    #[inline]
    fn in_zipper_mut_static_result<NodeF, RetryF, R>(&mut self, node_f: NodeF, retry_f: RetryF) -> R
        where
        NodeF: FnOnce(&mut dyn TrieNode<V>, &[u8]) -> Result<R, TrieNodeODRc<V>>,
        RetryF: FnOnce(&mut dyn TrieNode<V>, &[u8]) -> R,
    {
        let key = self.key.node_key();
        match node_f(self.focus_stack.top_mut().unwrap(), key) {
            Ok(result) => result,
            Err(replacement_node) => {
                self.focus_stack.backtrack();
                match self.focus_stack.top_mut() {
                    Some(parent_node) => {
                        let parent_key = self.key.parent_key();
                        parent_node.node_replace_child(parent_key, replacement_node);
                        self.focus_stack.advance(|node| node.node_get_child_mut(parent_key).map(|(_, child_node)| child_node.make_mut()));
                    },
                    None => {
                        *self.focus_stack.root_mut().unwrap() = replacement_node;
                        self.focus_stack.advance_from_root(|root| Some(root.make_mut()));
                    }
                }
                retry_f(self.focus_stack.top_mut().unwrap(), key)
            },
        }
    }

    // //Ugh... GOAT.  The safety thesis for the MutCursor depends on being able to consume the zipper... Which isn't very convenient here.
    // #[inline]
    // fn in_zipper_mut_borrowed_result<NodeF, RetryF, R>(&mut self, node_f: NodeF, retry_f: RetryF) -> &mut R
    //     where
    //     NodeF: for<'f> FnOnce(&'f mut dyn TrieNode<V>, &[u8]) -> Result<&'f mut R, TrieNodeODRc<V>>,
    //     RetryF: for<'f> FnOnce(&'f mut dyn TrieNode<V>, &[u8]) -> &'f mut R,
    // {
    //     let key = self.key.node_key();
    //     match self.focus_stack.try_map_into_mut(|top_ref| {
    //         node_f(top_ref, key)
    //     }) {
    //         Ok(result) => result,
    //         Err((mut node, replacement_node)) => {
    //             match self.focus_stack.top_mut() {
    //                 Some(parent_node) => {
    //                     let parent_key = self.key.parent_key();
    //                     parent_node.node_replace_child(parent_key, replacement_node);
    //                     self.focus_stack.advance(|node| node.node_get_child_mut(parent_key).map(|(_, child_node)| child_node.make_mut()));
    //                 },
    //                 None => {
    //                     *self.focus_stack.root_mut().unwrap() = replacement_node;
    //                     self.focus_stack.advance_from_root(|root| Some(root.make_mut()));
    //                 }
    //             }
    //             retry_f(self.focus_stack.top_mut().unwrap(), key)
    //         }
    //     }
    // }

    /// Internal method to recursively prune empty nodes from the trie, starting at the focus, and working
    /// upward until a value or branch is encountered.
    ///
    /// This method does not move the zipper, but may cause [Self::path_exists] to return `false`
    ///
    /// WARNING: this is one of the few zipper methods that allocs a temp buffer and doesn't try and uphold
    /// the "constant-time" property, but it should still be cheaper, on average, compared with other methods
    /// to do the same thing.
    #[inline]
    fn prune_path(&mut self) {
        debug_assert!(self.focus_stack.top().unwrap().node_is_empty());
        if self.at_root() {
            return
        }

        let old_path = self.key.prefix_buf.clone();
        self.ascend_until();

        let onward_path = &old_path[self.key.prefix_buf.len()..];
        self.descend_to(&onward_path[0..1]);
        self.remove_branch();

        //Move back to the original location, although it will now be non-existent
        self.key.prefix_buf = old_path;
    }

    /// Internal method that regularizes the `focus_stack` if nodes were created above the root
    #[inline]
    fn mend_root(&mut self) {
        if self.key.prefix_idx.len() == 0 && self.key.root_key.len() > 1 {
            debug_assert_eq!(self.focus_stack.depth(), 1);
            let (key, node) = node_along_path_mut(self.focus_stack.take_root().unwrap(), &self.key.root_key);
            self.key.root_key = key;
            self.key.prefix_buf.clear();
            self.key.prefix_buf.extend(self.key.root_key);
            self.focus_stack.replace_root(node);
            self.focus_stack.advance_from_root(|root| Some(root.make_mut()));
        }
    }

    /// Internal method to perform the part of `descend_to` that moves the focus node
    fn descend_to_internal(&mut self) {

        let mut key_start = self.key.node_key_start();
        //NOTE: this is a copy of the self.key.node_key() function, but we can't borrow the whole key structure in this code
        let mut key = if self.key.prefix_buf.len() > 0 {
            &self.key.prefix_buf[key_start..]
        } else {
            &self.key.root_key
        };
        if key.len() < 2 {
            return;
        }

        //Step until we get to the end of the key or find a leaf node
        while self.focus_stack.advance(|node| {
            if let Some((consumed_byte_cnt, next_node)) = node.node_get_child_mut(key) {
                if consumed_byte_cnt < key.len() {
                    key_start += consumed_byte_cnt;
                    self.key.prefix_idx.push(key_start);
                    key = &key[consumed_byte_cnt..];
                    Some(next_node.make_mut())
                } else {
                    None
                }
            } else {
                None
            }
        }) { }
    }
    /// Internal method which doesn't actually move the zipper, but ensures `self.node_key().len() > 0`
    /// WARNING, must never be called if `self.node_key().len() != 0`
    #[inline]
    fn ascend_across_nodes(&mut self) {
        debug_assert!(self.key.node_key().len() == 0);
        self.focus_stack.backtrack();
        self.key.prefix_idx.pop();
    }
    /// Internal method used to impement `ascend_until` when ascending within a node
    #[inline]
    fn ascend_within_node(&mut self) {
        let branch_key = self.focus_stack.top().unwrap().prior_branch_key(self.key.node_key());
        let new_len = self.key.root_key.len().max(self.key.node_key_start() + branch_key.len());
        self.key.prefix_buf.truncate(new_len);
    }

}

/// Internal function to walk a mut TrieNodeODRc<V> ref along a path
fn node_along_path_mut<'a, 'k, V>(start_node: &'a mut TrieNodeODRc<V>, path: &'k [u8]) -> (&'k [u8], &'a mut TrieNodeODRc<V>) {
    let mut key = path;
    let mut node = start_node;

    //Step until we get to the end of the key or find a leaf node
    let mut node_ptr: *mut TrieNodeODRc<V> = node; //Work-around for lack of polonius
    if key.len() > 0 {
        while let Some((consumed_byte_cnt, next_node)) = node.make_mut().node_get_child_mut(key) {
            if consumed_byte_cnt < key.len() {
                node = next_node;
                node_ptr = node;
                key = &key[consumed_byte_cnt..];
                //NOTE: we could early-out here, except, at most, it saves one step, but introduces a pipeline stall
                // at every step.  It's a win when the number of steps is about 6 or fewer, but otherwise a cost.
                // We won't shorten the key anymore, so we can finish here.
                // if key.len() == 1 {
                //     break;
                // }
            } else {
                break;
            };
        }
    }

    //SAFETY: Polonius is ok with this code.  All mutable borrows of the current version of the
    //  `node` &mut ref have ended by this point
    node = unsafe{ &mut *node_ptr };
    (key, node)
}

/// Internal function to create a parent path leading up to the supplied `child_node`
#[inline]
fn make_parents<V: Clone>(path: &[u8], child_node: TrieNodeODRc<V>) -> TrieNodeODRc<V> {

    #[cfg(not(feature = "all_dense_nodes"))]
    {
        let mut new_node = LineListNode::new();
        new_node.node_set_branch(path, child_node).unwrap_or_else(|_| panic!());
        TrieNodeODRc::new(new_node)
    }

    #[cfg(feature = "all_dense_nodes")]
    {
        let mut end = child_node;
        for i in (0..path.len()).rev() {
            let mut new_node = DenseByteNode::new();
            new_node.set_child(path[i], end);
            end = TrieNodeODRc::new(new_node);
        }
        end
    }
}

impl<'k> KeyFields<'k> {
    #[inline]
    fn new(path: &'k [u8]) -> Self {
        Self {
            root_key: path,
            prefix_buf: vec![],
            prefix_idx: vec![],
        }
    }
    /// Internal method to ensure buffers to facilitate movement of zipper are allocated and initialized
    #[inline]
    fn prepare_buffers(&mut self) {
        if self.prefix_buf.capacity() == 0 {
            self.prefix_buf = Vec::with_capacity(EXPECTED_PATH_LEN);
            self.prefix_idx = Vec::with_capacity(EXPECTED_DEPTH);
            self.prefix_buf.extend(self.root_key);
        }
    }
    /// Internal method returning the index to the key char beyond the path to the `self.focus_node`
    #[inline]
    fn node_key_start(&self) -> usize {
        self.prefix_idx.last().map(|i| *i).unwrap_or(0)
    }
    /// Internal method returning the key within the focus node
    #[inline]
    fn node_key(&self) -> &[u8] {
        if self.prefix_buf.len() > 0 {
            let key_start = self.node_key_start();
            &self.prefix_buf[key_start..]
        } else {
            self.root_key
        }
    }
    /// Internal method similar to `self.node_key().len()`, but returns the number of chars that can be
    /// legally ascended within the node, taking into account the root_key
    #[inline]
    fn excess_key_len(&self) -> usize {
        self.prefix_buf.len() - self.prefix_idx.last().map(|i| *i).unwrap_or(self.root_key.len())
    }
    /// Internal method returning the key that leads to `self.focus_node` within the parent
    #[inline]
    fn parent_key(&self) -> &[u8] {
        if self.prefix_buf.len() > 0 {
            let key_start = if self.prefix_idx.len() > 1 {
                unsafe{ *self.prefix_idx.get_unchecked(self.prefix_idx.len()-2) }
            } else {
                0
            };
            &self.prefix_buf[key_start..self.node_key_start()]
        } else {
            unreachable!()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::trie_map::*;
    use crate::zipper::*;

    #[test]
    fn write_zipper_get_or_insert_value_test() {
        let mut map = BytesTrieMap::<u64>::new();
        map.write_zipper_at_path(b"Drenths").get_value_or_insert(42);
        assert_eq!(map.get(b"Drenths"), Some(&42));

        *map.write_zipper_at_path(b"Drenths").get_value_or_insert(42) = 24;
        assert_eq!(map.get(b"Drenths"), Some(&24));

        let mut zipper = map.write_zipper_at_path(b"Drenths");
        *zipper.get_value_or_insert(42) = 0;
        assert_eq!(zipper.get_value(), Some(&0))
    }

    #[test]
    fn write_zipper_graft_test() {
        let a_keys = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let mut a: BytesTrieMap<i32> = a_keys.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();

        let b_keys = ["ad", "d", "ll", "of", "om", "ot", "ugh", "und"];
        let b: BytesTrieMap<i32> = b_keys.iter().enumerate().map(|(i, k)| (k, (i + 1000) as i32)).collect();

        let mut wz = a.write_zipper_at_path(b"ro");
        let rz = b.read_zipper();
        wz.graft(&rz);

        //Test that the original keys were left alone, above the graft point
        assert_eq!(a.get(b"arrow").unwrap(), &0);
        assert_eq!(a.get(b"bow").unwrap(), &1);
        assert_eq!(a.get(b"cannon").unwrap(), &2);

        //Test that the pruned keys are gone
        assert_eq!(a.get(b"roman"), None);
        assert_eq!(a.get(b"romulus"), None);
        assert_eq!(a.get(b"rom'i"), None);

        //More keys after but above the graft point weren't harmed
        assert_eq!(a.get(b"rubens").unwrap(), &7);
        assert_eq!(a.get(b"ruber").unwrap(), &8);
        assert_eq!(a.get(b"rubicundus").unwrap(), &10);

        //And test that the new keys were grafted into place
        assert_eq!(a.get(b"road").unwrap(), &1000);
        assert_eq!(a.get(b"rod").unwrap(), &1001);
        assert_eq!(a.get(b"roll").unwrap(), &1002);
        assert_eq!(a.get(b"roof").unwrap(), &1003);
        assert_eq!(a.get(b"room").unwrap(), &1004);
        assert_eq!(a.get(b"root").unwrap(), &1005);
        assert_eq!(a.get(b"rough").unwrap(), &1006);
        assert_eq!(a.get(b"round").unwrap(), &1007);
    }

    #[test]
    fn write_zipper_join_test() {
        let a_keys = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let mut a: BytesTrieMap<u64> = a_keys.iter().enumerate().map(|(i, k)| (k, i as u64)).collect();
        assert_eq!(a.val_count(), 12);

        let b_keys = ["road", "rod", "roll", "roof", "room", "root", "rough", "round"];
        let b: BytesTrieMap<u64> = b_keys.iter().enumerate().map(|(i, k)| (k, (i + 1000) as u64)).collect();
        assert_eq!(b.val_count(), 8);

        let mut wz = a.write_zipper_at_path(b"ro");
        let mut rz = b.read_zipper();
        rz.descend_to(b"ro");
        wz.join(&rz);

        //Test that the original keys were left alone, above the graft point
        assert_eq!(a.val_count(), 20);
        assert_eq!(a.get(b"arrow").unwrap(), &0);
        assert_eq!(a.get(b"bow").unwrap(), &1);
        assert_eq!(a.get(b"cannon").unwrap(), &2);

        //Test that the blended downstream keys are still there
        assert_eq!(a.get(b"roman").unwrap(), &3);
        assert_eq!(a.get(b"romulus").unwrap(), &6);
        assert_eq!(a.get(b"rom'i").unwrap(), &11);

        //More keys after but above the graft point weren't harmed
        assert_eq!(a.get(b"rubens").unwrap(), &7);
        assert_eq!(a.get(b"ruber").unwrap(), &8);
        assert_eq!(a.get(b"rubicundus").unwrap(), &10);

        //And test that the new keys were grafted into place
        assert_eq!(a.get(b"road").unwrap(), &1000);
        assert_eq!(a.get(b"rod").unwrap(), &1001);
        assert_eq!(a.get(b"roll").unwrap(), &1002);
        assert_eq!(a.get(b"roof").unwrap(), &1003);
        assert_eq!(a.get(b"room").unwrap(), &1004);
        assert_eq!(a.get(b"root").unwrap(), &1005);
        assert_eq!(a.get(b"rough").unwrap(), &1006);
        assert_eq!(a.get(b"round").unwrap(), &1007);
    }

    #[test]
    fn write_zipper_movement_test() {
        let keys = ["romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let mut map: BytesTrieMap<u64> = keys.iter().enumerate().map(|(i, k)| (k, i as u64)).collect();

        let mut wz = map.write_zipper_at_path(b"ro");
        assert_eq!(wz.child_count(), 1);
        assert!(wz.descend_to(b"manus"));
        assert_eq!(wz.path(), b"manus");
        assert_eq!(wz.child_count(), 0);
        wz.reset();
        assert_eq!(wz.path(), b"");
        assert_eq!(wz.child_count(), 1);
        assert!(wz.descend_to(b"mulus"));
        assert_eq!(wz.path(), b"mulus");
        assert_eq!(wz.child_count(), 0);
        assert!(wz.ascend_until());
        assert_eq!(wz.path(), b"m");
        assert_eq!(wz.child_count(), 3);

        //Make sure we can't ascend above the zipper's root with ascend_until
        assert!(wz.ascend_until());
        assert_eq!(wz.path(), b"");
        assert!(!wz.ascend_until());

        //Test step-wise `ascend`
        wz.descend_to(b"manus");
        assert_eq!(wz.path(), b"manus");
        assert_eq!(wz.ascend(1), true);
        assert_eq!(wz.path(), b"manu");
        assert_eq!(wz.ascend(5), false);
        assert_eq!(wz.path(), b"");
        assert_eq!(wz.at_root(), true);
        wz.descend_to(b"mane");
        assert_eq!(wz.path(), b"mane");
        assert_eq!(wz.ascend(3), true);
        assert_eq!(wz.path(), b"m");
        assert_eq!(wz.child_count(), 3);
    }

    #[test]
    fn write_zipper_compound_join_test() {
        let mut map = BytesTrieMap::<u64>::new();

        let b_keys = ["alligator", "goat", "gadfly"];
        let b: BytesTrieMap<u64> = b_keys.iter().enumerate().map(|(i, k)| (k, i as u64)).collect();

        let mut wz = map.write_zipper();
        let mut rz = b.read_zipper();
        rz.descend_to(b"alli");
        wz.graft(&rz);
        rz.reset();
        wz.join(&rz);

        assert_eq!(map.val_count(), 4);
    }

    #[test]
    fn write_zipper_remove_branch_test() {
        let keys = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i",
            "abcdefghijklmnopqrstuvwxyz"];
        let mut map: BytesTrieMap<i32> = keys.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();

        let mut wz = map.write_zipper_at_path(b"roman");
        wz.remove_branch();

        //Test that the original keys were left alone, above the graft point
        assert_eq!(map.get(b"arrow").unwrap(), &0);
        assert_eq!(map.get(b"bow").unwrap(), &1);
        assert_eq!(map.get(b"cannon").unwrap(), &2);
        assert_eq!(map.get(b"rom'i").unwrap(), &11);

        //Test that the value is ok
        assert_eq!(map.get(b"roman").unwrap(), &3);

        //Test that the pruned keys are gone
        assert_eq!(map.get(b"romane"), None);
        assert_eq!(map.get(b"romanus"), None);

        let mut wz = map.write_zipper();
        wz.descend_to(b"ro");
        assert!(wz.path_exists());
        wz.remove_branch();
        assert!(!wz.path_exists());

        let mut wz = map.write_zipper();
        wz.descend_to(b"abcdefghijklmnopq");
        assert!(wz.path_exists());
        assert_eq!(wz.path(), b"abcdefghijklmnopq");
        wz.remove_branch();
        assert!(!wz.path_exists());
        assert_eq!(wz.path(), b"abcdefghijklmnopq");
        assert!(!map.contains_path(b"abcdefghijklmnopq"));
        assert!(!map.contains_path(b"abc"));
    }

    #[test]
    fn write_zipper_drop_head_test() {
        let keys = [
            "123:abc:Bob",
            "123:def:Jim",
            "123:ghi:Pam",
            "123:jkl:Sue",
            "123:dog:Bob:Fido",
            "123:cat:Jim:Felix",
            "123:dog:Pam:Bandit",
            "123:owl:Sue:Cornelius"];
        let mut map: BytesTrieMap<u64> = keys.iter().enumerate().map(|(i, k)| (k, i as u64)).collect();
        let mut wz = map.write_zipper_at_path(b"123:");

        wz.drop_head(4);

        let ref_keys: Vec<&[u8]> = vec![
            b"123:Bob",
            b"123:Bob:Fido",
            b"123:Jim",
            b"123:Jim:Felix",
            b"123:Pam",
            b"123:Pam:Bandit",
            b"123:Sue",
            b"123:Sue:Cornelius"];
        assert_eq!(map.iter().map(|(k, _v)| k).collect::<Vec<Vec<u8>>>(), ref_keys);
    }

    #[test]
    fn write_zipper_insert_prefix_test() {
        let keys = [
            "123:Bob:Fido",
            "123:Jim:Felix",
            "123:Pam:Bandit",
            "123:Sue:Cornelius"];
        let mut map: BytesTrieMap<u64> = keys.iter().enumerate().map(|(i, k)| (k, i as u64)).collect();
        let mut wz = map.write_zipper_at_path(b"123:");

        wz.insert_prefix(b"pet:");
        // let paths: Vec<String> = map.iter().map(|(k, _)| String::from_utf8_lossy(&k[..]).to_string()).collect();
        let ref_keys: Vec<&[u8]> = vec![
            b"123:pet:Bob:Fido",
            b"123:pet:Jim:Felix",
            b"123:pet:Pam:Bandit",
            b"123:pet:Sue:Cornelius"];
        assert_eq!(map.iter().map(|(k, _v)| k).collect::<Vec<Vec<u8>>>(), ref_keys);

        // Test that drop_head undoes insert_prefix
        let mut wz = map.write_zipper();
        wz.insert_prefix(b"people:");
        //let paths: Vec<String> = map.iter().map(|(k, _)| String::from_utf8_lossy(&k[..]).to_string()).collect();
        wz.drop_head(b"people:".len());
        assert_eq!(map.iter().map(|(k, _v)| k).collect::<Vec<Vec<u8>>>(), ref_keys);
    }

    #[test]
    fn write_zipper_map_test() {
        let keys = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let mut map: BytesTrieMap<u64> = keys.iter().enumerate().map(|(i, k)| (k, i as u64)).collect();

        let mut wr = map.write_zipper();
        wr.descend_to(b"rom");
        let sub_map = wr.take_map().unwrap();
        let sub_map_keys: Vec<String> = sub_map.iter().map(|(k, _v)| String::from_utf8_lossy(&k).to_string()).collect();
        assert_eq!(sub_map_keys, ["'i", "an", "ane", "anus", "ulus"]);
        let map_keys: Vec<String> = map.iter().map(|(k, _v)| String::from_utf8_lossy(&k).to_string()).collect();
        assert_eq!(map_keys, ["arrow", "bow", "cannon", "rubens", "ruber", "rubicon", "rubicundus"]);

        let mut wr = map.write_zipper();
        wr.descend_to(b"c");
        wr.join_map(sub_map);
        let map_keys: Vec<String> = map.iter().map(|(k, _v)| String::from_utf8_lossy(&k).to_string()).collect();
        assert_eq!(map_keys, ["arrow", "bow", "c'i", "can", "cane", "cannon", "canus", "culus", "rubens", "ruber", "rubicon", "rubicundus"]);
    }
}