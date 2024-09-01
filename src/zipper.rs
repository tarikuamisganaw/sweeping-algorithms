
//! # Zipper Usage
//!
//! A zipper represents a cursor in a trie, and has a location called the focus.  A zipper can be moved
//! within the trie in order to access the trie for reading and/or writing.  A zipper's focus may not be
//! moved above the zipper's root.
//!
//! ## Move by Absolute Distance or by Trie Features
//!
//! Zippers may be moved either by stepping an absolute number of elements, or by jumping to features
//! such as branches and values.  In general, moving by jumping will be faster.
//!
//! The stepping methods are:
//! - [descend_indexed_child](zipper::Zipper::descend_indexed_child)
//! - [ascend](zipper::Zipper::ascend)
//! - [to_sibling](zipper::Zipper::to_sibling)
//!
//! The jumping methods are:
//! - [descend_to](zipper::Zipper::descend_to)
//! - [descend_until](zipper::Zipper::descend_until)
//! - [ascend_until](zipper::Zipper::ascend_until)
//!

use crate::trie_node::{TrieNode, AbstractNodeRef};
use crate::trie_map::BytesTrieMap;

pub use crate::write_zipper::*;

//==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--
//GOAT, Adam's experiments.  Avoiding deletion in case they're still needed
//==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--

// // CZ2 uses a stack machine
// // Store({a: 1}) // push

// // CZ3 (incomplete) uses register machine

// // Store({a: 1}, yym0)

// // Content addressed abstract machine

// // Store({a: 1}) // "you know what to do with this"

// // ZAM (Warren Abstract Machine for triemaps)

// // Store({a: 1}, [b, c])


// enum Instruction {
//     // == DESCEND ==
//     Exact(u8),  // jumps to specific child
//     Tail(u8),  // jumps to specific child and don't include

//     Set([u64; 4]),  // jump to all children in mask
//     Tails([u64; 4]),  // jump to all children in mask and don't include

//     All(),  // jump to all
//     Ignore(),  // jump to all and don't include

//     Max(),  // Any
//     Min(),  // Any

//     // == ASCEND ==
//     Head(u8),  // prefixes all with const

//     // == SET OPS ==
//     Union(),
//     Intersection(),
//     Subtraction(),

//     // == CZ 2 OPS ==
//     Restrict()
// }

//==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--
//GOAT, End of Adam's experiments
//==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--

/// An interface common to all zippers, to support moving the zipper, reading elements, iterating across
/// the trie
pub trait Zipper<'a>: zipper_priv::ZipperPriv {

    /// Returns `true` if the zipper cannot ascend further, otherwise returns `false`
    fn at_root(&self) -> bool;

    /// Resets the zipper's focus back to the root
    fn reset(&mut self);

    /// Returns the path from the zipper's root to the current focus
    fn path(&self) -> &[u8];

    /// Returns `true` if the zipper's focus is on a path within the trie, otherwise `false`
    fn path_exists(&self) -> bool;

    /// Returns `true` if there is a value at the zipper's focus, otherwise `false`
    fn is_value(&self) -> bool;

    /// Returns the total number of values contained at and below the zipper's focus, including the focus itself
    ///
    /// WARNING: This is not a cheap method. It may have an order-N cost
    fn val_count(&self) -> usize;

    /// Returns the number of child branches from the focus node
    ///
    /// Returns 0 if the focus is on a leaf
    fn child_count(&self) -> usize;

    /// Returns 256-bit mask indicating which children exist from the branch at the zipper's focus
    ///
    /// Returns an empty mask if the focus is on a leaf or non-existent path
    fn child_mask(&self) -> [u64; 4];

    /// Moves the zipper deeper into the tree, to the `key` specified relative to the current zipper focus
    ///
    /// Returns `true` if the zipper points to an existing path within the tree, otherwise `false`.  The
    /// zipper's location will be updated, regardless of whether or not the path exists within the tree.
    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) -> bool;

    /// Descends the zipper's focus one step into a child branch uniquely identified by `child_idx`
    ///
    /// `child_idx` must within the range `0..child_count()` or this method will do nothing and return `false`
    ///
    /// WARNING: The branch represented by a given index is not guaranteed to be stable across modifications
    /// to the trie.  This method should only be used as part of a directed traversal operation, but
    /// index-based paths may not be stored as locations within the trie.
    fn descend_indexed_branch(&mut self, idx: usize) -> bool;

    /// Descends the zipper's focus until a branch or a value is encountered.  Returns `true` if the focus
    /// moved otherwise returns `false`
    fn descend_until(&mut self) -> bool;

    /// Ascends the zipper `steps` steps.  Returns `true` if the zipper sucessfully moved `steps`
    ///
    /// If the root is fewer than `n` steps from the zipper's position, then this method will stop at
    /// the root and return `false`
    fn ascend(&mut self, steps: usize) -> bool;

    /// Ascends the zipper to the nearest upstream branch point or value.  Returns `true` if the zipper
    /// focus moved upwards, otherwise returns `false` if the zipper was already at the root
    fn ascend_until(&mut self) -> bool;

    /// Moves the zipper's focus to a sibling at the same level.  Returns `true` if the focus was changed,
    /// otherwise returns `false`
    ///
    /// This method is equivalent to calling [Self::ascend] with `1`, followed by [Self::descend_indexed_branch]
    /// where the index passed is 1 more or less than the index of the current focus position.
    ///
    /// If `next` is `true` then the zipper will be advanced otherwise it will be moved backwards.
    fn to_sibling(&mut self, next: bool) -> bool;

    /// Returns a new read-only Zipper, with the new zipper's root being at the zipper's current focus
    fn fork_zipper(&self) -> ReadZipper<Self::V>;

    /// Returns a new [BytesTrieMap] containing everything below the zipper's focus
    fn make_map(&self) -> Option<BytesTrieMap<Self::V>>;

}

pub(crate) mod zipper_priv {
    use crate::trie_node::*;

    pub trait ZipperPriv {
        type V;

        fn get_focus(&self) -> AbstractNodeRef<Self::V>;
    }
}
use zipper_priv::*;

/// Size of node stack to preallocate in the zipper
pub(crate) const EXPECTED_DEPTH: usize = 16;

/// Size in bytes to preallocate path storage in the zipper
pub(crate) const EXPECTED_PATH_LEN: usize = 64;

/// A [Zipper] that is unable to modify the trie
#[derive(Clone)]
pub struct ReadZipper<'a, 'k, V> {
    /// A reference to the entire origin path, of which `root_key` is the final subset, or None for a relative zipper
    origin_path: &'k [u8],
    /// The byte offset in `origin_path` from the root node to the zipper's root.
    /// `root_key = origin_path[root_key_offset..]`
    root_key_offset: Option<usize>,
    /// A special-case to access a value at the root node, because that value would be otherwise inaccessible
    root_val: Option<&'a V>,
    /// A reference to the root node
    focus_node: &'a dyn TrieNode<V>,
    /// Stores the entire path from the root node, including the bytes from `root_key`
    prefix_buf: Vec<u8>,
    /// Stores the lengths for each successive node's key
    prefix_idx: Vec<usize>,
    /// Stores a stack of parent node references.  Does not include the focus_node
    ancestors: Vec<&'a dyn TrieNode<V>>,
}

impl<'a, 'k, V: Clone> Zipper<'a> for ReadZipper<'a, 'k, V> {

    fn at_root(&self) -> bool {
        self.prefix_buf.len() <= self.origin_path.len()
    }

    fn reset(&mut self) {
        self.ancestors.truncate(1);
        match self.ancestors.pop() {
            Some(node) => self.focus_node = node,
            None => {}
        }
        self.prefix_buf.truncate(self.origin_path.len());
        self.prefix_idx.clear();
    }

    fn path(&self) -> &[u8] {
        if self.prefix_buf.len() > 0 {
            &self.prefix_buf[self.origin_path.len()..]
        } else {
            &[]
        }
    }

    fn path_exists(&self) -> bool {
        let key = self.node_key();
        if key.len() > 0 {
            self.focus_node.node_contains_partial_key(key)
        } else {
            true
        }
    }

    fn is_value(&self) -> bool {
        self.is_value_internal()
    }

    fn val_count(&self) -> usize {
        if self.node_key().len() == 0 {
            self.focus_node.node_subtree_len() + (self.is_value() as usize)
        } else {
            let focus = self.get_focus();
            if focus.is_none() {
                0
            } else {
                focus.borrow().node_subtree_len() + (self.is_value() as usize)
            }
        }
    }

    fn child_count(&self) -> usize {
        self.focus_node.count_branches(self.node_key())
    }

    fn child_mask(&self) -> [u64; 4] {
        self.focus_node.node_branches_mask(self.node_key())
    }

    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) -> bool {
        self.prepare_buffers();

        self.prefix_buf.extend(k.as_ref());
        let mut key_start = self.node_key_start();
        let mut key = &self.prefix_buf[key_start..];

        //Step until we get to the end of the key or find a leaf node
        while let Some((consumed_byte_cnt, next_node)) = self.focus_node.node_get_child(key) {
            key_start += consumed_byte_cnt;
            self.prefix_idx.push(key_start);
            self.ancestors.push(self.focus_node);
            self.focus_node = next_node;
            if consumed_byte_cnt < key.len() {
                key = &key[consumed_byte_cnt..]
            } else {
                return true;
            };
        }
        self.focus_node.node_contains_partial_key(key)
    }

    fn descend_indexed_branch(&mut self, child_idx: usize) -> bool {
        self.prepare_buffers();

        match self.focus_node.nth_child_from_key(self.node_key(), child_idx) {
            (Some(prefix), Some(child_node)) => {
                self.prefix_buf.push(prefix);
                self.prefix_idx.push(self.prefix_buf.len());
                self.ancestors.push(self.focus_node);
                self.focus_node = child_node;
                true
            },
            (Some(prefix), None) => {
                self.prefix_buf.push(prefix);
                true
            },
            (None, _) => false
        }
    }

    fn descend_until(&mut self) -> bool {
        let mut moved = false;
        self.prepare_buffers();

        while self.child_count() == 1 {
            moved = true;
            self.descend_first();
            if self.is_value_internal() {
                break;
            }
        }
        moved
    }

    fn to_sibling(&mut self, next: bool) -> bool {
        if self.node_key().len() != 0 {
            match self.focus_node.get_sibling_of_child(self.node_key(), next) {
                (Some(prefix), Some(child_node)) => {
                    *self.prefix_buf.last_mut().unwrap() = prefix;
                    self.prefix_idx.push(self.prefix_buf.len());
                    self.ancestors.push(self.focus_node);
                    self.focus_node = child_node;
                    true
                },
                (Some(prefix), None) => {
                    *self.prefix_buf.last_mut().unwrap() = prefix;
                    true
                },
                (None, _) => false
            }
        } else {
            let mut should_pop = false;
            let result = match self.ancestors.last() {
                None => { false }
                Some(parent) => {
                    match parent.get_sibling_of_child(self.parent_key(), next) {
                        (Some(prefix), Some(child_node)) => {
                            *self.prefix_buf.last_mut().unwrap() = prefix;
                            self.focus_node = child_node;
                            true
                        },
                        (Some(prefix), None) => {
                            *self.prefix_buf.last_mut().unwrap() = prefix;
                            should_pop = true;
                            true
                        },
                        (None, _) => {
                            false
                        }
                    }
                }
            };
            if should_pop {
                self.focus_node = self.ancestors.pop().unwrap();
                self.prefix_idx.pop();
            }
            result
        }
    }

    fn ascend(&mut self, mut steps: usize) -> bool {
        while steps > 0 {
            if self.excess_key_len() == 0 {
                self.focus_node = match self.ancestors.pop() {
                    Some(node) => node,
                    None => return false
                };
                self.prefix_idx.pop();
            }
            let cur_jump = steps.min(self.excess_key_len());
            self.prefix_buf.truncate(self.prefix_buf.len() - cur_jump);
            steps -= cur_jump;
        }
        true
    }

    fn ascend_until(&mut self) -> bool {
        if self.at_root() {
            return false;
        }

        //See if the branch point is in the parent node
        if self.node_key().len() == 0 {
            self.ascend_across_nodes();
        }
        self.ascend_within_node();
        if self.child_count() == 1 {
            self.ascend_until();
        }
        true
    }

    fn fork_zipper(&self) -> ReadZipper<V> {
        let new_root_val = self.get_value();
        let (new_root_path, new_root_key_offset) = match &self.root_key_offset {
            Some(_) => {
                let new_root_path = self.origin_path().unwrap();
                let new_root_key_offset = new_root_path.len() - self.node_key().len();
                (new_root_path, Some(new_root_key_offset))
            },
            None => (self.origin_path, None)
        };
        ReadZipper::new_with_node_and_path_internal(self.focus_node, new_root_path, new_root_key_offset, new_root_val)
    }

    fn make_map(&self) -> Option<BytesTrieMap<Self::V>> {
        self.get_focus().into_option().map(|node| BytesTrieMap::new_with_root(node))
    }
}

impl<'a, 'k, V : Clone> zipper_priv::ZipperPriv for ReadZipper<'a, 'k, V> {
    type V = V;

    fn get_focus(&self) -> AbstractNodeRef<Self::V> {
        self.focus_node.get_node_at_key(self.node_key())
    }
}

impl<'a, 'k, V : Clone> ReadZipper<'a, 'k, V> {

    /// Creates a new zipper, with a path relative to a node
    pub(crate) fn new_with_node_and_path(root_node: &'a dyn TrieNode<V>, path: &'k [u8], mut root_key_offset: Option<usize>) -> Self {
        let mut key = path;
        let mut node = root_node;
        let mut val = None;

        //Step until we get to the end of the key or find a leaf node
        if key.len() > 0 {
            while let Some((consumed_byte_cnt, next_node)) = node.node_get_child(key) {
                if consumed_byte_cnt < key.len() {
                    node = next_node;
                    key = &key[consumed_byte_cnt..];
                } else {
                    val = node.node_get_val(key);
                    node = next_node;
                    key = &[];
                    break;
                };
            }
        }

        let zipper_path = match root_key_offset.as_mut() {
            Some(root_key_offset) => {
                *root_key_offset -= key.len();
                path
            },
            None => key
        };

        Self::new_with_node_and_path_internal(node, zipper_path, root_key_offset, val)
    }
    /// Creates a new zipper, with a path relative to a node, assuming the path is fully-contained within
    /// the node
    ///
    /// NOTE: This method currently doesn't descend subnodes.  Use [Self::new_with_node_and_path] if you can't
    /// guarantee the path is within the supplied node.
    pub(crate) fn new_with_node_and_path_internal(root_node: &'a dyn TrieNode<V>, path: &'k [u8], root_key_offset: Option<usize>, root_val: Option<&'a V>) -> Self {
        Self {
            origin_path: path,
            root_key_offset,
            root_val,
            focus_node: root_node,
            prefix_buf: vec![],
            prefix_idx: vec![],
            ancestors: vec![],
        }
    }

    /// Returns a refernce to the value at the zipper's focus, or `None` if there is no value
    pub fn get_value(&self) -> Option<&'a V> {
        let key = self.node_key();
        if key.len() > 0 {
            self.focus_node.node_get_val(key)
        } else {
            if let Some(parent) = self.ancestors.last() {
                parent.node_get_val(self.parent_key())
            } else {
                self.root_val.clone() //Just clone the ref, not the value itself
            }
        }
    }

    /// Returns the path beginning from the origin to the current focus.  Returns `None` if the zipper
    /// is relative and does not have an origin path
    pub fn origin_path(&self) -> Option<&[u8]> {
        if self.root_key_offset.is_some() {
            if self.prefix_buf.len() > 0 {
                Some(&self.prefix_buf)
            } else {
                Some(&self.origin_path)
            }
        } else {
            None
        }
    }

    /// Systematically advances to the next value accessible from the zipper, traversing in a depth-first
    /// order.  Returns a reference to the value
    pub fn to_next_val(&mut self) -> Option<&'a V> {
        self.prepare_buffers();
        loop {
            //If we're at a leaf ascend and jump to the next sibling
            if self.focus_node.is_leaf(self.node_key()) {
                //We can stop ascending when we succeed in moving to a sibling
                while !self.to_sibling(true) {
                    if !self.ascend_jump(None) {
                        return None;
                    }
                }
            } else {
                //We're at a branch, so descend
                self.descend_first();
            }

            //If there is a value here, return it
            //UGH! Polonius!! We need you!!!  We know this is safe because we either return the result,
            // and hence no future use, or `get_value()` returns None, so we drop the borrow
            let self_ptr: *const Self = self;
            if let Some(val) = unsafe{ &*self_ptr }.get_value() {
                return Some(val);
            }
        }
    }

    //GOAT, this might be useful... But not sure.
    // /// Systematically advances the zipper to the next position where the path contains `pattern` as a
    // /// substring
    // ///
    // /// Traversal proceeds in a depth-first order.  When a match is encountered, the zipper will stop at the
    // /// end of the matched substring.  The zipper will not descend past a path length of `depth_limit` bytes,
    // /// from the zipper's root.
    // ///
    // /// Returns `true` if the zipper has arrived at a valid match, and `false` if no further matches could be
    // /// found.
    // pub fn to_next_match<K: AsRef<[u8]>>(&mut self, pattern: K, depth_limit: usize) -> bool {


    /// Descends the zipper's focus 'k' bytes, following the first child at each branch, and continuing with
    /// depth-first exploration until a path that is `k` bytes from the focus has been found
    ///
    /// Returns `true` if the zipper has sucessfully descended `k` steps, or `false` otherwise.  If this method
    /// returns `false` then the zipper will be in its original position.
    ///
    /// WARNING: This is not a constant-time operation, and may be as bad as `order n` with respect to the paths
    /// below the zipper's focus.  Although a typical cost is `order log n` or better.
    ///
    /// See: [Self::to_k_path_next]
    pub fn descend_first_k_path(&mut self, k: usize) -> bool {
        self.prepare_buffers();
        self.k_path_internal(k, self.path().len())
    }

    /// Moves the zipper's focus to the next location with the same path length as the current focus, following
    /// a depth-first exploration from a common root `k` steps above the current focus
    ///
    /// Returns `true` if the zipper has sucessfully moved to a new location at the same level, or `false` if
    /// no further locations exist.  If this method returns `false` then the zipper will be ascended `k` stept
    /// to the common root.
    ///
    /// WARNING: This is not a constant-time operation, and may be as bad as `order n` with respect to the paths
    /// below the zipper's focus.  Although a typical cost is `order log n` or better.
    ///
    /// See: [Self::descend_k_path_first]
    pub fn to_next_k_path(&mut self, k: usize) -> bool {
        self.prepare_buffers();
        let base_idx = if self.path().len() > k {
            self.path().len() - k
        } else {
            0
        };
        self.k_path_internal(k, base_idx)
    }

    /// Internal method that implements both `k_path...` methods above
    #[inline]
    fn k_path_internal(&mut self, k: usize, base_idx: usize) -> bool {
        let depth = |z: &Self| z.path().len() - base_idx;
        loop {
            //If we're at a leaf or `k` depth, then ascend and jump to the next sibling
            if self.focus_node.is_leaf(self.node_key()) || depth(self) >= k {
                //We can stop ascending when we succeed in moving to a sibling
                while !self.to_sibling(true) {
                    if !self.ascend_jump(Some(depth(self))) {
                        return false;
                    }
                }
            } else {
                //We're at a branch, so descend
                self.descend_first();
            }

            //Truncate the path if we over-shot
            if depth(self) > k {
                if self.node_key().len() == 0 {
                    self.ascend_across_nodes();
                }

                let overshoot = depth(self) - k;
                self.prefix_buf.truncate(self.prefix_buf.len() - overshoot);
            }

            if depth(self) == k {
                return true;
            }
        }
    }

    /// Internal method that implements [Self::is_value], but so it can be inlined elsewhere
    #[inline]
    fn is_value_internal(&self) -> bool {
        let key = self.node_key();
        if key.len() > 0 {
            self.focus_node.node_contains_val(key)
        } else {
            if let Some(parent) = self.ancestors.last() {
                parent.node_contains_val(self.parent_key())
            } else {
                self.root_val.is_some()
            }
        }
    }

    /// Internal method implementing part of [Self::descend_until], but doesn't pay attention to to [Self::child_count]
    #[inline]
    fn descend_first(&mut self) {
        match self.focus_node.first_child_from_key(self.node_key()) {
            (Some(prefix), Some(child_node)) => {
                //Step to a new node
                self.prefix_buf.extend(prefix);
                self.prefix_idx.push(self.prefix_buf.len());
                self.ancestors.push(self.focus_node);
                self.focus_node = child_node;

                //If we're at the root of the new node, descend to the first child
                if prefix.len() == 0 {
                    self.descend_first()
                }
            },
            (Some(prefix), None) => {
                //Stay within the same node
                self.prefix_buf.extend(prefix);
            },
            (None, _) => unreachable!()
        }
    }

    /// Internal method to ensure buffers to facilitate movement of zipper are allocated and initialized
    #[inline]
    fn prepare_buffers(&mut self) {
        if self.prefix_buf.capacity() == 0 {
            self.prefix_buf = Vec::with_capacity(EXPECTED_PATH_LEN);
            self.prefix_idx = Vec::with_capacity(EXPECTED_DEPTH);
            self.ancestors = Vec::with_capacity(EXPECTED_DEPTH);
            self.prefix_buf.extend(self.origin_path);
        }
    }

//GOAT, Unnecessary method.  It "feels" like a complete API needs a function to map from a key-based path
// to an integer-based path but I can't actually come up with a real-world use case for this method
//     /// Returns the index of the focus path, among its siblings at the nearest upstream branch point
//     ///
//     /// This method will return the `n` value that matches the argument that could have been passed to
//     /// [Self::descend_nth_child] to arrive at or pass through the current focus.
//     ///
//     /// The zipper's root will always have return 0, even if it has siblings within a larger tree.
//     ///
//     /// WARNING: This value is not guaranteed to be stable across modifications of the tree.  This value
//     /// should only be used as part of a directed traversal operation.
//     pub fn sibling_idx(&self) -> usize {
// //GOAT, this is idiotic.  What we really want is a way to ascend all the way up to the nearest branch point,
// // and this method should just give the sibling_idx with 1 ascent.
// //GOAT, no that would be annoying to use because it's the index at the last meaningful branch point you'd
// // want anyway...  Come to think of it, why would you ever want the index at all?
//         let key = self.node_key();
//         if key.len() > 0 {
//             let upstream = self.focus_node.prior_branch_key(key);
//         }

//         panic!()
//     }

    //GOAT, unnecessary function.  See comments around `sibling_count_at_key``
    // /// Returns the number of sibling branches of the focus_node
    // ///
    // /// Returns 0 if the focus is on a leaf.  Returns 1 if the focus is on the root, regardless of the number
    // /// of siblings the focus has within a larger tree
    // pub fn sibling_count(&self) -> usize {
    //     //GOAT, handle backing out to parent
    //     self.focus_node.sibling_count_at_key(self.node_key())
    // }

    /// Consumes the zipper and returns a Iterator over the downstream child bytes from the focus branch
    ///
    /// NOTE: This is mainly a convenience to allow the use of `collect` and `for` loops, as the other
    /// zipper methods can do the same thing without consuming the iterator
    pub fn into_child_iter(mut self) -> ReadZipperChildIter<'a, 'k, V> {
        self.descend_indexed_branch(0);
        ReadZipperChildIter::<'a, 'k, V>(Some(self))
    }

    /// Internal method returning the index to the key char beyond the path to the `self.focus_node`
    #[inline]
    fn node_key_start(&self) -> usize {
        self.prefix_idx.last().map(|i| *i)
            .unwrap_or_else(|| self.root_key_offset.unwrap_or(0))
    }
    /// Internal method returning the key within the focus node
    #[inline]
    fn node_key(&self) -> &[u8] {
        let key_start = self.node_key_start();
        if self.prefix_buf.len() > 0 {
            &self.prefix_buf[key_start..]
        } else {
            &self.origin_path[key_start..]
        }
    }
    /// Internal method returning the key that leads to `self.focus_node` within the parent
    /// NOTE: This method also returns the trailing parts of the key so it will only be useful when
    /// [self::node_key] returns `&[]`
    #[inline]
    fn parent_key(&self) -> &[u8] {
        if self.prefix_buf.len() > 0 {
            let key_start = if self.prefix_idx.len() > 1 {
                unsafe{ *self.prefix_idx.get_unchecked(self.prefix_idx.len()-2) }
            } else {
                self.root_key_offset.unwrap_or(0)
            };
            &self.prefix_buf[key_start..]
        } else {
            unreachable!()
        }
    }
    /// Internal method similar to `self.node_key().len()`, but returns the number of chars that can be
    /// legally ascended within the node, taking into account the root_key
    #[inline]
    fn excess_key_len(&self) -> usize {
        self.prefix_buf.len() - self.prefix_idx.last().map(|i| *i).unwrap_or(self.origin_path.len())
    }
    /// Internal method which doesn't actually move the zipper, but ensures `self.node_key().len() > 0`
    /// WARNING, must never be called if `self.node_key().len() != 0`
    #[inline]
    fn ascend_across_nodes(&mut self) {
        debug_assert!(self.node_key().len() == 0);
        self.focus_node = self.ancestors.pop().unwrap();
        self.prefix_idx.pop();
    }
    /// Internal method used to impement `ascend_until` when ascending within a node
    #[inline]
    fn ascend_within_node(&mut self) {
        let branch_key = self.focus_node.prior_branch_key(self.node_key());
        let new_len = self.origin_path.len().max(self.node_key_start() + branch_key.len());
        self.prefix_buf.truncate(new_len);
    }

    /// Internal method to ascend in one contiguous step, but unlike [Self::ascend_until], this method
    /// will stop one byte below the branch point, and also will not ascend recursively across multiple
    /// node boundaries.  Mainly this is useful in the implementation of [Self::to_next_val]
    #[inline]
    fn ascend_jump(&mut self, max_jump: Option<usize>) -> bool {
        if self.at_root() || max_jump == Some(0) {
            return false;
        }
        if self.node_key().len() == 0 {
            self.ascend_across_nodes();
        }
        if self.node_key().len() == 1 {
            let new_len = self.origin_path.len().max(self.node_key_start());
            self.prefix_buf.truncate(new_len);
            if self.at_root() || max_jump == Some(1) {
                return false;
            }
            self.ascend_across_nodes();
        }
        let branch_key = self.focus_node.prior_branch_key(self.node_key());
        let mut new_len = self.origin_path.len().max(self.node_key_start() + branch_key.len().max(1));
        if let Some(max_jump) = max_jump {
            new_len = new_len.max(self.prefix_buf.len() - max_jump);
        }
        self.prefix_buf.truncate(new_len);
        true
    }
}

impl<'a, 'k, V: Clone> std::iter::IntoIterator for ReadZipper<'a, 'k, V> {
    type Item = (Vec<u8>, &'a V);
    type IntoIter = ReadZipperIter<'a, 'k, V>;

    fn into_iter(self) -> Self::IntoIter {
        ReadZipperIter {
            started: false,
            zipper: Some(self)
        }
    }
}

/// An iterator for depth-first traversal of a [ReadZipper], returned from [into_iter](std::iter::IntoIterator::into_iter)
///
/// NOTE: This is a convenience to allow access to syntactic sugar like `for` loops, [collect](std::iter::Iterator::collect),
///  etc.  It will always be faster to use the zipper itself for iteration and traversal.
pub struct ReadZipperIter<'a, 'k, V>{
    started: bool,
    zipper: Option<ReadZipper<'a, 'k, V>>,
}

impl<'a, 'k, V: Clone> Iterator for ReadZipperIter<'a, 'k, V> {
    type Item = (Vec<u8>, &'a V);

    fn next(&mut self) -> Option<(Vec<u8>, &'a V)> {
        if !self.started {
            self.started = true;
            if let Some(zipper) = &mut self.zipper {
                if let Some(val) = zipper.get_value() {
                    return Some((zipper.path().to_vec(), val))
                }
            }
        }
        if let Some(zipper) = &mut self.zipper {
            match zipper.to_next_val() {
                Some(val) => return Some((zipper.path().to_vec(), val)),
                None => self.zipper = None
            }
        }
        None
    }
}

/// An Iterator returned by [into_child_iter](ReadZipper::into_child_iter) to iterate over the children from
/// a branch of the trie
///
/// NOTE: This type is a convenience to allow access to syntactic sugar like `for` loops,
/// [collect](std::iter::Iterator::collect), etc.
///
/// NOTE: Does not descend recursively.  Use [into_iter](std::iter::IntoIterator::into_iter) for a depth-first
/// traversal, or just use the [Zipper] methods directly.
pub struct ReadZipperChildIter<'a, 'k, V>(Option<ReadZipper<'a, 'k, V>>);

impl<'a, 'k, V: Clone> Iterator for ReadZipperChildIter<'a, 'k, V> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        if let Some(zipper) = &mut self.0 {
            let result = zipper.path().last().cloned();
            if !zipper.to_sibling(true) {
                self.0 = None;
            }
            result
        } else {
            None
        }
    }
}

//==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--
//GOAT, more of Adam's experiments
//==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--

// // pub struct WriteZipper<'a, V> {
// //     pub root: *mut BytesTrieMap<V>,
// //     pub focus: *mut ByteTrieNode<CoFree<V>>,
// //     pub path: Vec<u8>,
// //     pub ancestors: Vec<*mut ByteTrieNode<CoFree<V>>>,
// // }
// //
// // impl <'a, V : Clone + Debug> WriteZipper<'a, V> {
// //     pub fn remove_children(m: [u64; 4]) {}
// //
// //     pub fn remove_child(k: u8) {}
// //     pub fn remove_nth_child(n: u8) {}
// //
// //     pub fn remove_value(k: u8) {}
// //     pub fn remove_nth_value(n: u8) {}
// //
// //     pub fn add_child(k: u8) {}
// //     pub fn add_nth_child(n: u8) {}
// //
// //     pub fn add_value(k: u8) {}
// //     pub fn add_nth_value(n: u8) {}
// // }

// trait Engine {
//     // fn execute<V>(inp: &BytesTrieMap<V>, k: &[Instruction]) -> BytesTrieMap<V> {
//     //     let mut out = BytesTrieMap::new();
//     //     let mut inp_loc = &inp.root;
//     //     let mut out_loc = &out.root;
//     //
//     //     match k[0] {
//     //         Instruction::Exact(k) => {
//     //             node.get()
//     //         }
//     //         Instruction::Set(_) => {}
//     //         Instruction::Ignore() => {}
//     //         Instruction::Any() => {}
//     //     }
//     //     if k.len() > 1 {
//     //         for i in 0..k.len() - 1 {
//     //             match node.get(k[i]) {
//     //                 Some(cf) => {
//     //                     match unsafe { cf.rec.as_ref() } {
//     //                         Some(r) => { node = r }
//     //                         None => { return None }
//     //                     }
//     //                 }
//     //                 None => { return None }
//     //             }
//     //         }
//     //     }
//     //
//     //     out
//     // }
// }

//==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--
//GOAT, End of Adam's experiments
//==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--==--

#[cfg(test)]
mod tests {
    use crate::trie_map::*;
    use super::*;

    #[test]
    fn zipper_basic_test() {
        // from https://en.wikipedia.org/wiki/Radix_tree#/media/File:Patricia_trie.svg
        let mut btm = BytesTrieMap::new();
        let rs = ["romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });
    //GOAT, fix this, "at_path"
        // assert_eq!(btm.at("rom".as_bytes()).map(|m| m.items().collect::<HashSet<_>>()),
        //            Some(HashSet::from([("ane".as_bytes().to_vec(), &0), ("anus".as_bytes().to_vec(), &1), ("ulus".as_bytes().to_vec(), &2), ("'i".as_bytes().to_vec(), &7)])));

        fn assert_in_list(val: &[u8], list: &[&[u8]]) {
            for test_val in list {
                if *test_val == val {
                    return;
                }
            }
            panic!("val not found in list: {}", std::str::from_utf8(val).unwrap_or(""))
        }

        let mut rz = btm.read_zipper();
        rz.descend_to(&[b'r']); rz.descend_to(&[b'o']); rz.descend_to(&[b'm']); // focus = rom
        assert!(rz.descend_to(&[b'\''])); // focus = rom'  (' is the lowest byte)
        assert!(rz.to_sibling(true)); // focus = roma  (a is the second byte), but we can't actually guarantee whether we land on 'a' or 'u'
        assert_in_list(rz.path(), &[b"roma", b"romu"]);
        assert_eq!(rz.fork_zipper().into_child_iter().collect::<Vec<_>>(), vec![b'n']); // both follow-ups romane and romanus have n following a
        assert!(rz.to_sibling(true)); // focus = romu  (u is the third byte)
        assert_in_list(rz.path(), &[b"roma", b"romu"]);
        assert_eq!(rz.fork_zipper().into_child_iter().collect::<Vec<_>>(), vec![b'l']); // and romu is followed by lus
        assert!(!rz.to_sibling(true)); // fails because there were only 3 children ['\'', 'a', 'u']
        assert!(rz.to_sibling(false)); // focus = roma or romu (we stepped back)
        assert_in_list(rz.path(), &[b"roma", b"romu"]);
        assert!(rz.to_sibling(false)); // focus = rom' (we stepped back to where we began)
        assert_eq!(rz.path(), b"rom'");
        assert_eq!(rz.fork_zipper().into_child_iter().collect::<Vec<_>>(), vec![b'i']);
        assert!(rz.ascend(1)); // focus = rom
        assert_eq!(rz.fork_zipper().into_child_iter().collect::<Vec<_>>(), vec![b'\'', b'a', b'u']); // all three options we visited
        assert!(rz.descend_indexed_branch(0)); // focus = rom'
        assert_eq!(rz.fork_zipper().into_child_iter().collect::<Vec<_>>(), vec![b'i']);
        assert!(rz.ascend(1)); // focus = rom
        assert!(rz.descend_indexed_branch(1)); // focus = roma
        assert_eq!(rz.fork_zipper().into_child_iter().collect::<Vec<_>>(), vec![b'n']);
        assert!(rz.ascend(1));
        assert!(rz.descend_indexed_branch(2)); // focus = romu
        assert_eq!(rz.fork_zipper().into_child_iter().collect::<Vec<_>>(), vec![b'l']);
        assert!(rz.ascend(1));
        assert!(rz.descend_indexed_branch(1)); // focus = roma
        assert_eq!(rz.fork_zipper().into_child_iter().collect::<Vec<_>>(), vec![b'n']);
        assert!(rz.ascend(1));
        // ' < a < u
        // 39 105 117
    }

    #[test]
    fn zipper_with_starting_key() {
        let mut btm = BytesTrieMap::new();
        let rs = ["romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        //Test `descend_to` and `ascend_until`
        let root_key = b"ro";
        let mut zipper = ReadZipper::new_with_node_and_path(btm.root().borrow(), root_key, Some(root_key.len()));
        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.child_count(), 1);
        zipper.descend_to(b"m");
        assert_eq!(zipper.path(), b"m");
        assert_eq!(zipper.child_count(), 3);
        zipper.descend_to(b"an");
        assert_eq!(zipper.path(), b"man");
        assert_eq!(zipper.child_count(), 2);
        zipper.descend_to(b"e");
        assert_eq!(zipper.path(), b"mane");
        assert_eq!(zipper.child_count(), 0);
        assert_eq!(zipper.ascend_until(), true);
        zipper.descend_to(b"us");
        assert_eq!(zipper.path(), b"manus");
        assert_eq!(zipper.child_count(), 0);
        assert_eq!(zipper.ascend_until(), true);
        assert_eq!(zipper.path(), b"man");
        assert_eq!(zipper.child_count(), 2);
        assert_eq!(zipper.ascend_until(), true);
        assert_eq!(zipper.path(), b"m");
        assert_eq!(zipper.child_count(), 3);
        assert_eq!(zipper.ascend_until(), true);
        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.child_count(), 1);
        assert_eq!(zipper.at_root(), true);
        assert_eq!(zipper.ascend_until(), false);

        //Test `ascend`
        zipper.descend_to(b"manus");
        assert_eq!(zipper.path(), b"manus");
        assert_eq!(zipper.ascend(1), true);
        assert_eq!(zipper.path(), b"manu");
        assert_eq!(zipper.ascend(5), false);
        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.at_root(), true);
        zipper.descend_to(b"mane");
        assert_eq!(zipper.path(), b"mane");
        assert_eq!(zipper.ascend(3), true);
        assert_eq!(zipper.path(), b"m");
        assert_eq!(zipper.child_count(), 3);
    }

    #[test]
    fn indexed_zipper_movement() {
        let mut btm = BytesTrieMap::new();
        let rs = ["arrow", "bow", "cannon", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });
        let mut zipper = btm.read_zipper();

        //descends a single specific byte using `descend_indexed_child`. Just for testing. A real user would use `descend_towards`
        fn descend_byte(zipper: &mut ReadZipper<usize>, byte: u8) {
            for i in 0..zipper.child_count() {
                assert_eq!(zipper.descend_indexed_branch(i), true);
                if *zipper.path().last().unwrap() == byte {
                    break
                } else {
                    assert_eq!(zipper.ascend(1), true);
                }
            }
        }

        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.child_count(), 4);
        descend_byte(&mut zipper, b'r');
        assert_eq!(zipper.path(), b"r");
        assert_eq!(zipper.child_count(), 2);
        assert_eq!(zipper.descend_until(), false);
        descend_byte(&mut zipper, b'o');
        assert_eq!(zipper.path(), b"ro");
        assert_eq!(zipper.child_count(), 1);
        assert_eq!(zipper.descend_until(), true);
        assert_eq!(zipper.path(), b"rom");
        assert_eq!(zipper.child_count(), 3);

        zipper.reset();
        assert_eq!(zipper.descend_until(), false);
        descend_byte(&mut zipper, b'a');
        assert_eq!(zipper.path(), b"a");
        assert_eq!(zipper.child_count(), 1);
        assert_eq!(zipper.descend_until(), true);
        assert_eq!(zipper.path(), b"arrow");
        assert_eq!(zipper.child_count(), 0);

        assert_eq!(zipper.ascend(3), true);
        assert_eq!(zipper.path(), b"ar");
        assert_eq!(zipper.child_count(), 1);

    }

    #[test]
    fn zipper_value_access() {
        let mut btm = BytesTrieMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().for_each(|r| { btm.insert(r.as_bytes(), *r); });

        let root_key = b"ro";
        let mut zipper = ReadZipper::new_with_node_and_path(btm.root().borrow(), root_key, Some(root_key.len()));
        assert_eq!(zipper.is_value(), false);
        zipper.descend_to(b"mulus");
        assert_eq!(zipper.is_value(), true);
        assert_eq!(zipper.get_value(), Some(&"romulus"));

        let root_key = b"roman";
        let mut zipper = ReadZipper::new_with_node_and_path(btm.root().borrow(), root_key, Some(root_key.len()));
        assert_eq!(zipper.is_value(), true);
        assert_eq!(zipper.get_value(), Some(&"roman"));
        zipper.descend_to(b"e");
        assert_eq!(zipper.is_value(), true);
        assert_eq!(zipper.get_value(), Some(&"romane"));
        assert_eq!(zipper.ascend(1), true);
        zipper.descend_to(b"u");
        assert_eq!(zipper.is_value(), false);
        assert_eq!(zipper.get_value(), None);
        zipper.descend_until();
        assert_eq!(zipper.is_value(), true);
        assert_eq!(zipper.get_value(), Some(&"romanus"));
    }

    #[test]
    fn zipper_iter() {
        let mut btm = BytesTrieMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });
        let mut zipper = btm.read_zipper();

        //Test iteration of the whole tree
        let mut count = 0;
        assert_eq!(zipper.is_value(), false);
        while let Some(&val) = zipper.to_next_val() {
            // println!("{val}  {} = {}", std::str::from_utf8(zipper.path()).unwrap(), zipper.get_value().unwrap());
            assert_eq!(rs[val].as_bytes(), zipper.path());
            count += 1;
        }
        assert_eq!(count, rs.len());

        //Fork a sub-zipper, and test iteration of that subtree
        zipper.reset();
        zipper.descend_to(b"rub");
        let mut sub_zipper = zipper.fork_zipper();
        while let Some(&val) = sub_zipper.to_next_val() {
            // println!("{val}  {} = {}", std::str::from_utf8(sub_zipper.path()).unwrap(), std::str::from_utf8(&rs[val].as_bytes()[3..]).unwrap());
            assert_eq!(&rs[val].as_bytes()[3..], sub_zipper.path());
        }

        for (path, &val) in zipper {
            // println!("{val}  {} = {}", std::str::from_utf8(&path).unwrap(), std::str::from_utf8(rs[val].as_bytes()).unwrap());
            assert_eq!(rs[val].as_bytes(), path);
        }
    }

    #[test]
    fn path_concat_test() {
        let parent_path = "�parent";
        let exprs = [
            "�parent�Tom�Bob",
            "�parent�Pam�Bob",
            "�parent�Tom�Liz",
            "�parent�Bob�Ann",
            "�parent�Bob�Pat",
            "�parent�Pat�Jim",
            "�female�Pam",
            "�male�Tom",
            "�male�Bob",
            "�female�Liz",
            "�female�Pat",
            "�female�Ann",
            "�male�Jim",
        ];
        let family: BytesTrieMap<i32> = exprs.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();

        let mut parent_zipper = family.read_zipper_at_path(parent_path.as_bytes());

        assert!(family.contains_path(parent_path));

        let mut full_parent_path = parent_path.as_bytes().to_vec();
        full_parent_path.extend(parent_zipper.path());
        assert!(family.contains_path(&full_parent_path));

        while let Some(_val) = parent_zipper.to_next_val() {
            let mut full_parent_path = parent_path.as_bytes().to_vec();
            full_parent_path.extend(parent_zipper.path());
            assert!(family.contains(full_parent_path.clone()));
            assert_eq!(full_parent_path, parent_zipper.origin_path().unwrap());
        }
    }

    #[test]
    fn full_path_test() {
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let btm: BytesTrieMap<u64> = rs.into_iter().enumerate().map(|(i, k)| (k, i as u64)).collect();

        let mut zipper = btm.read_zipper_at_path(b"roma");
        assert_eq!(format!("roma{}", std::str::from_utf8(zipper.path()).unwrap()), "roma");
        assert_eq!(std::str::from_utf8(zipper.origin_path().unwrap()).unwrap(), "roma");
        zipper.descend_to(b"n");
        assert_eq!(format!("roma{}", std::str::from_utf8(zipper.path()).unwrap()), "roman");
        assert_eq!(std::str::from_utf8(zipper.origin_path().unwrap()).unwrap(), "roman");
        zipper.to_next_val();
        assert_eq!(format!("roma{}", std::str::from_utf8(zipper.path()).unwrap()), "romane");
        assert_eq!(std::str::from_utf8(zipper.origin_path().unwrap()).unwrap(), "romane");
        zipper.to_next_val();
        assert_eq!(format!("roma{}", std::str::from_utf8(zipper.path()).unwrap()), "romanus");
        assert_eq!(std::str::from_utf8(zipper.origin_path().unwrap()).unwrap(), "romanus");
        zipper.to_next_val();
        assert_eq!(zipper.path().len(), 0);
    }

    #[test]
    fn k_path_test() {
        //This is a toy encoding where `:n:` precedes a symbol of `n` characters long
        let keys = [
            ":5:above:3:the:4:fray:",
            ":5:err:",
            ":5:erronious:6:potato:",
            ":5:error:2:is:2:my:4:name:",
            ":5:hello:5:world:",
            ":5:mucky:4:muck:",
            ":5:roger:6:rabbit:",
            ":5:zebra:",
            ":9:muckymuck:5:raker:",
        ];
        let map: BytesTrieMap<u64> = keys.into_iter().enumerate().map(|(i, k)| (k, i as u64)).collect();
        let mut zipper = map.read_zipper_at_path(b":");

        //This is a cheesy way to encode lengths, but it's is more readable than unprintable chars
        assert!(zipper.descend_indexed_branch(0));
        let sym_len = usize::from_str_radix(std::str::from_utf8(&[zipper.path()[0]]).unwrap(), 10).unwrap();
        assert_eq!(sym_len, 5);

        //Step over the ':' character
        assert!(zipper.descend_indexed_branch(0));
        assert_eq!(zipper.child_count(), 6);

        //Start iterating over all the symbols of length=sym_len
        assert_eq!(zipper.descend_first_k_path(sym_len+1), true);

        //This should have taken us to "above:"
        assert_eq!(zipper.path(), b"5:above:");

        //Go to the next symbol.
        // Two interesting things will happen.  First, we blow past "err" because its path length is
        // shorter than `k`.  Second, we will stop in the middle of "erronious".
        // These situations would be caused by an encode bug.  Which hopefully we won't have in real
        // paths. But the parser should recognize the last digit of the path isn't ':'
        assert_eq!(zipper.to_next_k_path(sym_len+1), true);
        assert_eq!(zipper.path(), b"5:erroni");
        assert_ne!(zipper.path().last(), Some(&b':'));

        //Now we'll move on to some correctly formed symbols
        assert_eq!(zipper.to_next_k_path(sym_len+1), true);
        assert_eq!(zipper.path(), b"5:error:");
        assert_eq!(zipper.to_next_k_path(sym_len+1), true);
        assert_eq!(zipper.path(), b"5:hello:");
        assert_eq!(zipper.to_next_k_path(sym_len+1), true);
        assert_eq!(zipper.path(), b"5:mucky:");
        assert_eq!(zipper.to_next_k_path(sym_len+1), true);
        assert_eq!(zipper.path(), b"5:roger:");
        assert_eq!(zipper.to_next_k_path(sym_len+1), true);
        assert_eq!(zipper.path(), b"5:zebra:");

        //The last step should return false, and put us back to where we began
        assert_eq!(zipper.to_next_k_path(sym_len+1), false);
        assert_eq!(zipper.path(), b"5:");
        assert_eq!(zipper.child_count(), 6);
    }
}

// GOAT, new zipper API.  "fork_zipper_at_path".  Cheap call to make a new zipper cheaper than descend_to
//   for the current zipper.  The idea is that there is no need to save the intervening node pointers along the path
//