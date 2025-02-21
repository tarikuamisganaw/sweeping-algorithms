
use core::slice;
use std::mem::MaybeUninit;

use crate::empty_node::EmptyNode;
use crate::trie_map::BytesTrieMap;
use crate::trie_node::*;
use crate::zipper::*;

/// A borrowed read-only reference to a location in a trie
///
/// `TrieRef`s are like a read-only [Zipper] that can't move, but it is *much* smaller, cheaper to
/// create, and cheaper to work with.
pub struct TrieRef<'a, V> {
    focus_node: TaggedNodeRef<'a, V>,
    val_or_key: ValRefOrKey<'a, V>
}

/// A TrieRef will never have both a non-zero-len node_key and a non-None value reference
#[repr(C)]
union ValRefOrKey<'a, V> {
    /// A length byte, followed by the key bytes themselves
    node_key: (u8, [MaybeUninit<u8>; MAX_NODE_KEY_BYTES]),
    /// VAL_REF_SENTINEL, followed by the 
    val_ref: (u64, Option<&'a V>)
}

/// Marks the first part of the `val_ref` variant of the [ValRefOrKey] enum.  This will never occur
/// by accident because the length byte at the beginning of the `node_key` variant has limited range
const VAL_REF_SENTINEL: u64 = 0xFFFFFFFFFFFFFFFF;

/// Marks a [TrieRef] that is invalid.  Same logic as VAL_REF_SENTINEL regarding accidental collision
const BAD_SENTINEL: u64 = 0xFEFEFEFEFEFEFEFE;

impl<V> Clone for ValRefOrKey<'_, V> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}
impl<V> Copy for ValRefOrKey<'_, V> {}

impl<V> Clone for TrieRef<'_, V> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}
impl<V> Copy for TrieRef<'_, V> {}

impl<'a, V> TrieRef<'a, V> {
    pub(crate) fn new_invalid() -> Self {
        Self { focus_node: TaggedNodeRef::EmptyNode(EmptyNode), val_or_key: ValRefOrKey { val_ref: (BAD_SENTINEL, None) } }
    }
    /// Internal constructor
    pub(crate) fn new_with_node_and_path(root_node: &'a dyn TrieNode<V>, root_val: Option<&'a V>, path: &[u8]) -> Self {
        let (node, key, val) = node_along_path(root_node, path, root_val);
        let node_key_len = key.len();
        let val_or_key = if node_key_len > 0 && node_key_len <= MAX_NODE_KEY_BYTES {
            debug_assert!(val.is_none());
            let mut node_key_bytes = [MaybeUninit::uninit(); MAX_NODE_KEY_BYTES];
            unsafe {
                let src_ptr = key.as_ptr();
                let dst_ptr = node_key_bytes.as_mut_ptr().cast::<u8>();
                core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, node_key_len);
            }
            ValRefOrKey { node_key: (node_key_len as u8, node_key_bytes) }
        } else {
            if node_key_len <= MAX_NODE_KEY_BYTES {
                ValRefOrKey { val_ref: (VAL_REF_SENTINEL, val) }
            } else {
                ValRefOrKey { val_ref: (BAD_SENTINEL, None) }
            }
        };

        Self { focus_node: node.as_tagged(), val_or_key }
    }
    /// Internal.  Checks if the `TrieRef` is valid, which is a prerequisite to see if it's pointing
    /// at an existing path
    #[inline]
    fn is_valid(&self) -> bool {
        (unsafe{ self.val_or_key.node_key.0 } != 0xFE)
    }
    /// Internal.  Gets the node key from the `TrieRef`
    #[inline]
    fn node_key(&self) -> &[u8] {
        let key_len = unsafe{ self.val_or_key.node_key.0 } as usize;
        if key_len > MAX_NODE_KEY_BYTES {
            &[]
        } else {
            unsafe{ slice::from_raw_parts(self.val_or_key.node_key.1.as_ptr().cast(), key_len) }
        }
    }
    /// Internal.  Gets the root val from the `TrieRef`, which is `None` if the `TrieRef` has a [Self::node_key]
    #[inline]
    fn root_val(&self) -> Option<&'a V> {
        if unsafe{ self.val_or_key.val_ref.0 } == VAL_REF_SENTINEL {
            unsafe{ self.val_or_key.val_ref.1 }
        } else {
            None
        }
    }
}

impl<V: Clone + Send + Sync + Unpin> Zipper<V> for TrieRef<'_, V> {
    type ReadZipperT<'a> = ReadZipperUntracked<'a, 'a, V> where Self: 'a;
    fn path_exists(&self) -> bool {
        if self.is_valid() {
            let key = self.node_key();
            if key.len() > 0 {
                self.focus_node.node_contains_partial_key(key)
            } else {
                true
            }
        } else {
            false
        }
    }
    fn is_value(&self) -> bool {
        self.get_value().is_some()
    }
    fn value(&self) -> Option<&V> {
        self.get_value()
    }
    fn child_count(&self) -> usize {
        if self.is_valid() {
            self.focus_node.count_branches(self.node_key())
        } else {
            0
        }
    }
    fn child_mask(&self) -> [u64; 4] {
        if self.is_valid() {
            self.focus_node.node_branches_mask(self.node_key())
        } else {
            [0u64; 4]
        }
    }
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a> {
        unimplemented!() //GOAT finish this impl!!
        // let new_root_val = self.get_value();
        // let (new_root_path, new_root_key_offset) = match &self.root_key_offset {
        //     Some(_) => {
        //         let new_root_path = self.origin_path().unwrap();
        //         let new_root_key_offset = new_root_path.len() - self.node_key().len();
        //         (new_root_path, Some(new_root_key_offset))
        //     },
        //     None => (self.node_key(), None)
        // };
        // Self::ReadZipperT::new_with_node_and_path_internal(self.focus_node.clone(), new_root_path, new_root_key_offset, new_root_val)
    }
    fn make_map(&self) -> Option<BytesTrieMap<Self::V>> {
        unimplemented!() //GOAT finish this impl!!
        // #[cfg(not(feature = "graft_root_vals"))]
        // let root_val = None;
        // #[cfg(feature = "graft_root_vals")]
        // let root_val = self.get_value().cloned();

        // let root_node = self.get_focus().into_option();
        // if root_node.is_some() || root_val.is_some() {
        //     Some(BytesTrieMap::new_with_root(root_node, root_val))
        // } else {
        //     None
        // }
    }
}

impl<V: Clone + Send + Sync> zipper_priv::ZipperPriv for TrieRef<'_, V> {
    type V = V;

    fn get_focus(&self) -> AbstractNodeRef<Self::V> {
        if self.is_valid() {
            self.focus_node.get_node_at_key(self.node_key())
        } else {
            AbstractNodeRef::None
        }
    }
    fn try_borrow_focus(&self) -> Option<&dyn TrieNode<Self::V>> {
        if self.is_valid() {
            let node_key = self.node_key();
            if node_key.len() == 0 {
                Some(self.focus_node.borrow())
            } else {
                match self.focus_node.node_get_child(node_key) {
                    Some((consumed_bytes, child_node)) => {
                        debug_assert_eq!(consumed_bytes, node_key.len());
                        Some(child_node)
                    },
                    None => None
                }
            }
        } else {
            None
        }
    }
}

impl<'a, V: Clone + Send + Sync + Unpin> ZipperReadOnly<'a, V> for TrieRef<'a, V> {
    #[inline]
    fn get_value(&self) -> Option<&'a V> {
        if self.is_valid() {
            let key = self.node_key();
            if key.len() > 0 {
                self.focus_node.node_get_val(key)
            } else {
                unsafe{
                    debug_assert_eq!(self.val_or_key.val_ref.0, VAL_REF_SENTINEL);
                    self.val_or_key.val_ref.1
                }
            }
        } else {
            None
        }
    }
    #[inline]
    fn trie_ref_at_path(&self, path: &[u8]) -> TrieRef<'a, V> {
        if self.is_valid() {
            let node_key = self.node_key();
            if node_key.len() > 0 {
                trie_ref_at_path(self.focus_node.borrow(), None, node_key, path)
            } else {
                trie_ref_at_path(self.focus_node.borrow(), self.root_val(), &[], path)
            }
        } else {
            TrieRef::new_invalid()
        }
    }
}

/// Internal function to implement [ZipperReadOnly::trie_ref_at_path] for all the types that need it
pub(crate) fn trie_ref_at_path<'a, 'paths, V>(mut node: &'a dyn TrieNode<V>, root_val: Option<&'a V>, node_key: &'paths [u8], mut path: &'paths [u8]) -> TrieRef<'a, V> {

    // A temporary buffer on the stack, if we need to assemble a combined key from both the `node_key` and `path`
    let mut temp_key_buf: [MaybeUninit<u8>; MAX_NODE_KEY_BYTES] = [MaybeUninit::uninit(); MAX_NODE_KEY_BYTES];

    let node_key_len = node_key.len();
    let path_len = path.len();

    //Copy the existing node key and the first chunk of the path into the temp buffer, and try to
    // descend one step
    if node_key_len > 0 && path_len > 0 {
        let next_node_path = unsafe {
            let src_ptr = node_key.as_ptr();
            let dst_ptr = temp_key_buf.as_mut_ptr().cast::<u8>();
            core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, node_key_len);

            let remaining_len = (MAX_NODE_KEY_BYTES - node_key_len).min(path_len);
            let src_ptr = path.as_ptr();
            let dst_ptr = temp_key_buf.as_mut_ptr().cast::<u8>().add(node_key_len);
            core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, remaining_len);

            let total_buf_len = node_key_len + remaining_len;
            core::slice::from_raw_parts(temp_key_buf.as_mut_ptr().cast::<u8>(), total_buf_len)
        };

        if let Some((consumed_byte_cnt, next_node)) = node.node_get_child(next_node_path) {
            debug_assert!(consumed_byte_cnt >= node_key_len);
            node = next_node;
            path = &path[consumed_byte_cnt-node_key_len..];
        } else {
            path = next_node_path;
        }
    } else {
        if path_len == 0 {
            path = node_key;
        }
    }

    //Descend the rest of the way along the path
    let (node, key, val) = node_along_path(node, path, root_val);

    TrieRef::new_with_node_and_path(node, val, key)
}


#[cfg(test)]
mod tests {
    use crate::{trie_map::BytesTrieMap, utils::ByteMask};
    use super::*;

    #[test]
    fn trie_ref_test() {
        //TODO: If we want to get a `TrieRef` down to 32 bytes, we can push the tag in [TaggedNodeRef]
        // into 3 or 4 unused bits in the pointer
        //
        //TODO: We could go even further towards shrinking the `TrieRef` and ultimately get down to 16 Bytes
        // total by modifying the TrieNode API to create a "location_ref".  That would look roughly like this:
        //
        // - The `node_contains_partial_key` method would be expanded into something like:
        //  `fn location_for_partial_key(&self, key: &[u8]) -> u64;`  The returned location token
        //  would uniquely identify any existing location within the node.
        //
        // - The returned location token needs to be able to represent any location within the node,
        //  not just endpoints.  For a ByteNode, it's easy, it's just a sentinel to indicate pointing
        //  at the base of the node, and a u8 for positions one byte below the base.  For the ListNode/
        //  aka PairNode, the logic would probably be a bit to indicate whether we're looking at slot0
        //  or slot1, and a counter to indicate how many bytes into that slot's key we are pointing at.
        //
        // - There would be universally recognized sentinel value (universal across all node types) for
        //   non-existant paths, which would be the equivalent to `node_contains_partial_key` returning false.
        //
        // - We'd want another method to reverse the transformation from location token back into a path,
        //   This would be needed to initialize the path of a zipper, forked from a TrieRef, and likely
        //   elsewhere too if we used location tokens extensively inside the zipper.
        //
        // - Many accessor functions could take a location token instead of a node_key.  For example,
        //   `count_branches`, `node_branches_mask`, `get_node_at_key` (may rename it), `get_node_at_key`,
        //   `node_get_child`
        //
        // - Implementing this change above may have some interactions with `tiny_node` / TinyRefNode,
        //   it could lead to some potential simplifications to the code overall, if we can come up with
        //   an interface that allows any subtrie within a node to function as a node unto itself.
        //   Because currently `TinyRefNode` targets a special case, so we need a fallback for when
        //   that case doesn't apply.
        //
        assert!(core::mem::size_of::<TrieRef<()>>() <= 40);

        let keys = ["Hello", "Hell", "Help", "Helsinki"];
        let map: BytesTrieMap<()> = keys.iter().map(|k| (k, ())).collect();

        // With the current node types, there likely isn't any reason the node would be split at "He"
        let trie_ref = TrieRef::new_with_node_and_path(map.root().unwrap().borrow(), map.root_val(), b"He");
        assert_eq!(trie_ref.node_key(), b"He");
        assert_eq!(trie_ref.get_value(), None);
        assert_eq!(trie_ref.path_exists(), true);

        // "Hel" on the other hand was likely split into its own node
        let trie_ref = TrieRef::new_with_node_and_path(map.root().unwrap().borrow(), map.root_val(), b"Hel");
        assert_eq!(trie_ref.node_key().len(), 0);
        assert_eq!(trie_ref.get_value(), None);
        assert_eq!(trie_ref.path_exists(), true);

        // Make sure we get a value at a leaf
        let trie_ref = TrieRef::new_with_node_and_path(map.root().unwrap().borrow(), map.root_val(), b"Help");
        assert_eq!(trie_ref.get_value(), Some(&()));
        assert_eq!(trie_ref.path_exists(), true);

        // Make sure we get a value in the middle of a path
        let trie_ref = TrieRef::new_with_node_and_path(map.root().unwrap().borrow(), map.root_val(), b"Hell");
        assert_eq!(trie_ref.get_value(), Some(&()));
        assert_eq!(trie_ref.path_exists(), true);

        // Try a path that doesn't exist
        let trie_ref = TrieRef::new_with_node_and_path(map.root().unwrap().borrow(), map.root_val(), b"Hi");
        assert_eq!(trie_ref.get_value(), None);
        assert_eq!(trie_ref.path_exists(), false);

        // Try a very long path that doesn't exist but is sure to blow the single-node path buffer
        let trie_ref = TrieRef::new_with_node_and_path(map.root().unwrap().borrow(), map.root_val(), b"Hello Mr. Washington, my name is John, but sometimes people call me Jack.  I live in Springfield.");
        assert_eq!(trie_ref.get_value(), None);
        assert_eq!(trie_ref.path_exists(), false);

        //Try using TrieRefs to descend a trie
        let trie_ref0 = TrieRef::new_with_node_and_path(map.root().unwrap().borrow(), map.root_val(), b"H");
        assert_eq!(trie_ref0.get_value(), None);
        assert_eq!(trie_ref0.path_exists(), true);
        assert_eq!(trie_ref0.child_count(), 1);
        assert_eq!(trie_ref0.child_mask(), ByteMask::from(b'e'));

        //"Hel"
        let trie_ref1 = trie_ref0.trie_ref_at_path(b"el");
        assert_eq!(trie_ref1.get_value(), None);
        assert_eq!(trie_ref1.path_exists(), true);
        assert_eq!(trie_ref1.child_count(), 3);

        //"Hello"
        let trie_ref2 = trie_ref1.trie_ref_at_path(b"lo");
        assert_eq!(trie_ref2.get_value(), Some(&()));
        assert_eq!(trie_ref2.path_exists(), true);
        assert_eq!(trie_ref2.child_count(), 0);

        //"HelloOperator"
        let trie_ref3 = trie_ref2.trie_ref_at_path(b"Operator");
        assert_eq!(trie_ref3.get_value(), None);
        assert_eq!(trie_ref3.path_exists(), false);
        assert_eq!(trie_ref3.child_count(), 0);

        //"HelloOperator, give me number 9"
        let trie_ref4 = trie_ref3.trie_ref_at_path(b", give me number 9");
        assert_eq!(trie_ref4.get_value(), None);
        assert_eq!(trie_ref4.path_exists(), false);
        assert_eq!(trie_ref4.child_count(), 0);

        //"Hell"
        let trie_ref2 = trie_ref1.trie_ref_at_path(b"l");
        assert_eq!(trie_ref2.get_value(), Some(&()));
        assert_eq!(trie_ref2.path_exists(), true);
        assert_eq!(trie_ref2.child_count(), 1);
    }
}
