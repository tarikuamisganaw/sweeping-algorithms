
use mutcursor::MutCursorRootedVec;

use crate::trie_node::{TrieNode, TrieNodeODRc};
use crate::zipper::*;
use crate::zipper::zipper_priv::*;
use crate::ring::{Lattice, DistributiveLattice, PartialDistributiveLattice};

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
        self.key.prefix_buf.clear();
        self.key.prefix_idx.clear();
    }

    fn path(&self) -> &[u8] {
        if self.key.prefix_buf.len() > 0 {
            &self.key.prefix_buf[self.key.root_key.len()..]
        } else {
            &[]
        }
    }

    fn child_count(&self) -> usize {
//GOAT, this might be wrong because we may need to descend
        panic!()
        //self.focus_stack.top().unwrap().child_count_at_key(self.key.node_key())
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
        panic!()
    }

    fn ascend_until(&mut self) -> bool {
        panic!()
    }

    fn fork_zipper(&self) -> ReadZipper<V> {
        panic!()
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
        if self.key.node_key().len() == 0 {
            self.focus_stack.top().unwrap().node_subtree_len() + (self.is_value() as usize)
        } else {
            match self.clone_focus() {
                Some(temp_root) => {
                    temp_root.borrow().node_subtree_len() + (self.is_value() as usize)
                },
                None => 0
            }
        }
    }
}

impl<'a, 'k, V : Clone> zipper_priv::ZipperPriv for WriteZipper<'a, 'k, V> {
    type V = V;

    fn clone_focus(&self) -> Option<TrieNodeODRc<V>> {
        self.focus_stack.top().unwrap().clone_node_at_key(self.key.node_key())
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
    /// Sets the value at the zipper's focus
    ///
    /// Returns `Some(replaced_val)` if an existing value was replaced, otherwise returns `None` if
    /// the value was added without replacing anything.
    ///
    /// Panics if the zipper's focus is unable to hold a value
    pub fn set_value(&mut self, val: V) -> Option<V> {
        let old_val = self.in_zipper_mut_static_result(
            |node, remaining_key| node.node_set_val(remaining_key, val),
            |_new_leaf_node, _remaining_key| None);
        self.mend_root();
        self.descend_to_internal();
        old_val
    }
    /// Returns a refernce to the value at the zipper's focus, or `None` if there is no value
    pub fn get_value(&mut self) -> Option<&V> {
        self.focus_stack.top().unwrap().node_get_val(self.key.node_key())
    }
    /// Returns a mutable reference to a value at the zipper's focus, or None if no value exists
    pub fn get_value_mut(&mut self) -> Option<&mut V> {
        self.focus_stack.top_mut().unwrap().node_get_val_mut(self.key.node_key())
    }
    /// Returns a mutable reference to the value at the zipper's focus, inserting `default` if no value exists
    pub fn get_value_or_insert(&mut self, default: V) -> &mut V {
        let val_added = self.in_zipper_mut_static_result(
            |node, key| {
                if !node.node_contains_val(key) {
                    node.node_set_val(key, default).map(|_| true)
                } else {
                    Ok(false)
                }
            },
            |_, _| true);
        if val_added {
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
        let val_added = self.in_zipper_mut_static_result(
            |node, key| {
                if !node.node_contains_val(key) {
                    node.node_set_val(key, func()).map(|_| true)
                } else {
                    Ok(false)
                }
            },
            |_, _| true);
        if val_added {
            self.mend_root();
            self.descend_to_internal();
        }
        self.get_value_mut().unwrap()
    }

    /// Replaces the trie below the zipper's focus with the subtrie downstream from the focus of `read_zipper`
    ///
    /// If there is a value at the zipper's focus, it will not be affected.  If the `read_zipper` is not on
    /// an existing path (according to [Zipper::path_exists]) then the trie will be pruned below the graft location.
    pub fn graft<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) {
        self.graft_internal(read_zipper.clone_focus())
    }

    /// Joins (union of) the subtrie below the zipper's focus with the subtrie downstream from the focus of `read_zipper`
    pub fn join<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) where V: Lattice {
        let src = match read_zipper.clone_focus() {
            Some(src) => src,
            None => return
        };
        match self.clone_focus() {
            Some(self_node) => {
                let joined = self_node.join(&src);
                self.graft_internal(Some(joined))
            },
            None => { self.graft_internal(Some(src)) }
        }
    }

    /// Meets (retains the intersection of) the subtrie below the zipper's focus with the subtrie downstream from the focus of `read_zipper`
    pub fn meet<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) where V: Lattice {
        let src = match read_zipper.clone_focus() {
            Some(src) => src,
            None => return
        };
        match self.clone_focus() {
            Some(self_node) => {
                let joined = self_node.meet(&src);
                self.graft_internal(Some(joined))
            },
            None => { self.graft_internal(Some(src)) }
        }
    }

    /// Subtracts the subtrie downstream of the focus of `read_zipper` from the subtrie below the zipper's focus
    pub fn subtract<'z, Z: Zipper<'z, V=V>>(&mut self, read_zipper: &Z) where V: PartialDistributiveLattice {
        let src = match read_zipper.clone_focus() {
            Some(src) => src,
            None => return
        };
        match self.clone_focus() {
            Some(self_node) => {
                let joined = self_node.subtract(&src);
                self.graft_internal(Some(joined))
            },
            None => { self.graft_internal(Some(src)) }
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

//GOAT, also implement remove_val

    /// Internal implementation of graft, and other methods that do the same thing
    #[inline]
    fn graft_internal(&mut self, src: Option<TrieNodeODRc<V>>) {
        match src {
            Some(src) => {
                debug_assert!(!src.borrow().node_is_empty());
                let node_key = self.key.node_key();
                if node_key.len() > 0 {
                    match self.focus_stack.top_mut().unwrap().node_set_branch(node_key, src) {
                        Ok(_) => {},
                        Err(_replacement_node) => {
                            panic!(); //TODO
                        }
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
    #[inline]
    fn prune_path(&mut self) {
        println!("GOAT prune path");
    }

    /// Internal method that regularizes the `focus_stack` if nodes were created above the root
    #[inline]
    fn mend_root(&mut self) {
        if self.key.prefix_idx.len() == 0 && self.key.root_key.len() > 1 {
            let (key, node) = node_along_path_mut(self.focus_stack.take_root().unwrap(), &self.key.root_key);
            self.key.root_key = key;
            self.focus_stack.replace_root(node);
            self.focus_stack.advance_from_root(|root| Some(root.make_mut()));
        }
    }

    /// Internal method to perform the part of `descend_to` that moves the focus node
    #[inline]
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

    //SAFETY: Pononius is ok with this code.  All mutable borrows of the current version of the
    //  `node` &mut ref have ended by this point
    node = unsafe{ &mut *node_ptr };
    (key, node)
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
        wz.remove_branch();
        assert!(!wz.path_exists());
        assert!(!map.contains_path(b"abcdefghijklmnopq"));
        assert!(!map.contains_path(b"abc"));
    }
}