
use core::hint::unreachable_unchecked;
use core::mem::ManuallyDrop;
use std::collections::HashMap;
use dyn_clone::*;
use local_or_heap::LocalOrHeap;
use arrayvec::ArrayVec;

use crate::utils::ByteMask;
use crate::Allocator;
use crate::dense_byte_node::*;
use crate::ring::*;
use crate::tiny_node::TinyRefNode;
use crate::line_list_node::LineListNode;

#[cfg(feature = "bridge_nodes")]
use crate::bridge_node::BridgeNode;

/// The maximum key length any node type may require to access any value or sub-path within the node
pub(crate) const MAX_NODE_KEY_BYTES: usize = 23;

/// The abstract interface to all nodes, from which tries are built
///
/// TrieNodes are small tries that can be stitched together into larger tries.  Within a TrieNode, value
/// and onward link locations are defined by key paths.  There are a few conventions and caveats to this
/// iterface:
///
/// 1. A TrieNode will never have a value or an onward link at a zero-length key.  A value associated with
/// the path to the root of a TrieNode must be stored in the parent node.
pub trait TrieNode<V: Clone + Send + Sync, A: Allocator>: TrieNodeDowncast<V, A> + DynClone + core::fmt::Debug + Send + Sync {

    /// Returns `true` if the node contains a key that begins with `key`, irrespective of whether the key
    /// specifies a child, value, or both
    ///
    /// This method should never be called with a zero-length key.  If the `key` arg is longer than the
    /// keys contained within the node, this method should return `false`
    fn node_contains_partial_key(&self, key: &[u8]) -> bool {
        self.node_key_overlap(key) == key.len()
    }

    /// Returns the number of bytes in `key` that overlap a key contained within the node, irrespective
    /// of what the contained key specifies
    ///
    /// For example, this method should return `2` when called on a node that contains the key "telephone",
    /// with the argument "test".
    ///
    /// This method should never be called with a zero-length key.
    fn node_key_overlap(&self, key: &[u8]) -> usize;

    /// Returns the child node that matches `key` along with the number of `key` characters matched.
    /// Returns `None` if no child node matches the key, even if there is a value with that prefix
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &TrieNodeODRc<V, A>)>;

    //GOAT, Deprecated node_get_child_and_val_mut
    // /// Returns mutable pointers to both an onward child link as well as a value.
    // ///
    // /// If the node is not capable of storing either the onward link or the value, this function must
    // /// return `None`.  The returned `usize` describes the number of key-bytes matched, similar to the
    // /// return value from [Self::node_get_child].
    // ///
    // /// This method is needed because it's impossible to split the borrows to different parts of the
    // /// same node.  However, the a Zipper or ZipperHead much contain a reference to both the onward
    // /// link and value.
    // fn node_get_child_and_val_mut(&mut self, key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>, &mut Option<V>)>;

    /// Same behavior as `node_get_child`, but operates across a mutable reference
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V, A>)>;

    //GOAT, we probably don't need this interface
    // /// Returns `true` if the node does *NOT* contain any onward children at paths aside from the provided
    // /// `keys`
    // ///
    // /// NOTE: It isn't necessary for the node to contain all `keys` provided, simply that it contains no
    // /// additional onward links with other keys.
    // ///
    // /// The implementation may assume `keys` will be in sorted order
    // ///
    // /// See [TrieNode::node_contains_vals_exclusive] for the values counterpart.
    // fn node_contains_children_exclusive(&self, keys: &[&[u8]]) -> bool;

    //GOAT, Probably can be removed
    /// Replaces a child-node at `key` with the node provided, returning a `&mut` reference to the newly
    /// added child node
    ///
    /// Unlike [node_get_child], this method requires an exact key and not just a prefix, in order to
    /// maintain tree integrity.  This method is not intended as a general-purpose "set" operation, and
    /// may panic if the node does not already contain a child node at the specified key.
    ///
    /// QUESTION: Does this method have a strong purpose, or can it be superseded by node_set_branch?
    fn node_replace_child(&mut self, key: &[u8], new_node: TrieNodeODRc<V, A>) -> &mut dyn TrieNode<V, A>;

    /// Retrieves multiple values or child links from the node, associated with elements from `keys`,
    /// and places them into the respective element in `results`
    ///
    /// The `bool` in `keys` indicates whether a value is expected at the requested key.  `true` will be
    /// passed to indicate a **value**. (WARNING: This is different from the convention in some node types)
    ///
    /// If a node contains both an onward link and a value at the same key, the `bool` specifies which to
    /// return; however, a node may be returned for a requested value, if the path to the node is a prefix
    /// to the path to the requested value.  This is because the value may live within a child node.  On
    /// the other hand, a value will only be returned if it is an exact match with the key provided.
    ///
    /// The `usize` in `results` functions the same way as the returned `usize` in [TrieNode::node_get_child],
    /// to indicate the number of key bytes matched by the key contained within the node.
    ///
    /// The implementation may assume `keys` will be in sorted order, and `false` sorts before `true` if
    /// both a value and a node at the same key are requested.
    ///
    /// Returns `true` if the requested `keys` completely enumerate the set of elements contained within
    /// the node, or `false` if the node contains additional elements that were not requested
    ///
    /// If a result is not found for a given key, the implementation does not guarantee the corresponding
    /// element in `results` will be set to [`PayloadRef::None`], therefore the caller should init `results`
    /// to default values.
    ///
    /// Panics if `keys.len() > results.len()`
    ///
    /// NOTE: It perfectly fine for multiple keys to share a prefix, and sometimes that means multiple
    /// results will be identical if the node represents only the prefix portion of the key.
    fn node_get_payloads<'node, 'res>(&'node self, keys: &[(&[u8], bool)], results: &'res mut [(usize, PayloadRef<'node, V, A>)]) -> bool;

    /// Returns `true` if the node contains a value at the specified key, otherwise returns `false`
    ///
    /// NOTE: just as with [Self::node_get_val], this method will return `false` if key is longer than
    /// the exact key contained within this node
    fn node_contains_val(&self, key: &[u8]) -> bool;

    //GOAT, we probably don't need this interface
    // /// Returns `true` if the node does *NOT* contain any values at paths aside from the provided `keys`
    // ///
    // /// See [TrieNode::node_contains_children_exclusive] for a complete description of behavior and
    // /// requirements.
    // fn node_contains_vals_exclusive(&self, keys: &[&[u8]]) -> bool;

    /// Returns the value that matches `key` if it contained within the node
    ///
    /// NOTE: this method will return `None` if key is longer than the exact key contained within this
    /// node, even if there is a valid value at the leading subset of `key`
    fn node_get_val<'a>(&'a self, key: &[u8]) -> Option<&'a V>;

    /// Mutable version of [node_get_val]
    fn node_get_val_mut(&mut self, key: &[u8]) -> Option<&mut V>;

    /// Sets the value specified by `key` to the object V
    ///
    /// Returns `Ok((None, _))` if a new value was added where there was no previous value, returns
    /// `Ok((Some(v), false))` with the old value if the value was replaced.  The returned `bool` is a
    /// "sub_node_created" flag that will be `true` if `key` now specifies a different subnode; `false`
    /// if key still specifies a branch within the node.
    ///
    /// If this method returns Err(node), then the node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    fn node_set_val(&mut self, key: &[u8], val: V) -> Result<(Option<V>, bool), TrieNodeODRc<V, A>>;

    /// Deletes the value specified by `key`
    ///
    /// Returns `Some(val)` with the value that was removed, otherwise returns `None`
    ///
    /// WARNING: This method may leave the node empty
    fn node_remove_val(&mut self, key: &[u8]) -> Option<V>;

    /// Sets the downstream branch from the specified `key`.  Does not affect the value at the `key`
    ///
    /// Returns `Ok(sub_node_created)`, which will be `true` if `key` now specifies a different subnode;
    /// and `false` if key still specifies a branch within the node.
    ///
    /// If this method returns Err(node), then the `self` node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    fn node_set_branch(&mut self, key: &[u8], new_node: TrieNodeODRc<V, A>) -> Result<bool, TrieNodeODRc<V, A>>;

    /// Removes the downstream branch from the specified `key`.  Does not affect the value at the `key`
    ///
    /// Returns `true` if one or more downstream branches were removed from the node; returns `false` if
    /// the node did not contain any downstream branches from the specified key
    ///
    /// WARNING: This method may leave the node empty.  If eager pruning of branches is desired then the
    /// node should subsequently be checked to see if it is empty
    fn node_remove_all_branches(&mut self, key: &[u8]) -> bool;

    /// Uses a 256-bit mask to filter down children and values from the specified `key`.  Does not affect
    /// the value at the `key`
    ///
    /// WARNING: This method may leave the node empty.  If eager pruning of branches is desired then the
    /// node should subsequently be checked to see if it is empty
    fn node_remove_unmasked_branches(&mut self, key: &[u8], mask: ByteMask);

    /// Returns `true` if the node contains no children nor values, otherwise false
    fn node_is_empty(&self) -> bool;

    /// Generates a new iter token, to iterate the children and values contained within this node
    fn new_iter_token(&self) -> u128;

    /// Generates an iter token that can be passed to [Self::next_items] to continue iteration from the
    /// specified path
    fn iter_token_for_path(&self, key: &[u8]) -> u128;

    /// Steps to the next existing path within the node, in a depth-first order
    ///
    /// Returns `(next_token, path, child_node, value)`
    /// - `next_token` is the value to pass to a subsequent call of this method.  Returns
    ///   [NODE_ITER_FINISHED] when there are no more sub-paths
    /// - `path` is relative to the start of `node`
    /// - `child_node` an onward node link, of `None`
    /// - `value` that exists at the path, or `None`
    fn next_items(&self, token: u128) -> (u128, &[u8], Option<&TrieNodeODRc<V, A>>, Option<&V>);

    /// Returns the total number of leaves contained within the whole subtree defined by the node
    fn node_val_count(&self, cache: &mut HashMap<*const dyn TrieNode<V, A>, usize>) -> usize;

    #[cfg(feature = "counters")]
    /// Returns the number of internal items (onward links and values) within the node.  In the case where
    /// a child node and a value have the same internal path it should be counted as two items
    fn item_count(&self) -> usize;

    /// Returns the depth (byte count) of the first value encountered along the specified key
    ///
    /// For example, if the node contains a value at "he" and another value at "hello", this method should
    /// return `Some(1)` for the key "hello", because the "he" value is encountered first.  Returns `None`
    /// if no value is contained within the node along the specified `key`.
    ///
    /// If this method returns `Some(n)`, then `node_get_val(&key[..=n])` must return a non-None result.
    ///
    /// This method will never be called with a zero-length key.
    fn node_first_val_depth_along_key(&self, key: &[u8]) -> Option<usize>;

    /// Returns the nth descending child path from the branch specified by `key` within this node, as the
    /// prefix leading to that new path and optionally a new node
    ///
    /// This method returns (None, _) if `n >= self.count_branches()`.
    /// This method returns (Some(_), None) if the child path is is contained within the same node.
    /// This method returns (Some(_), Some(_)) if the child path is is contained within a different node.
    ///
    /// NOTE: onward paths that lead to values are still part of the enumeration
    /// NOTE: Unlike some other trait methods, method may be called with a zero-length key
    fn nth_child_from_key(&self, key: &[u8], n: usize) -> (Option<u8>, Option<&dyn TrieNode<V, A>>);

    /// Behaves similarly to [Self::nth_child_from_key(0)] with the difference being that the returned
    /// prefix should be an entire path to the onward link or to the next branch
    fn first_child_from_key(&self, key: &[u8]) -> (Option<&[u8]>, Option<&dyn TrieNode<V, A>>);

    /// Returns the number of onward (child) paths within a node from a specified key
    ///
    /// If the node doesn't contain the key, this method returns 0.
    /// If the key identifies a value but no onward path within the node, this method returns 0.
    /// If the key identifies a partial path within the node, this method returns 1.
    ///
    /// WARNING: This method does not recurse, so an onward child link's children will not be
    ///   considered.  Therefore, it is necessary to call this method on the referenced node and
    ///   not the parent.  Call [node_count_branches_recursive] to get this behavior.
    /// NOTE: Unlike some other trait methods, method may be called with a zero-length key
    fn count_branches(&self, key: &[u8]) -> usize;

    /// Returns 256-bit mask, indicating which children exist from the branch specified by `key`
    fn node_branches_mask(&self, key: &[u8]) -> ByteMask;

    /// Returns `true` if the key specifies a leaf within the node from which it is impossible to
    /// descend further, otherwise returns `false`
    ///
    /// NOTE: Returns `true` if the key specifies an invalid path, because an invalid path has no
    ///   onward paths branching from it.
    /// NOTE: The reason this is not the same as `node.count_branches() == 0` is because [Self::count_branches]
    ///   counts only internal children, and treats values and onward links equivalently.  Therefore
    ///   some keys that specify onward links will be reported as having a `count_branches` of 0, but
    ///   `is_leaf` will not be true.
    fn is_leaf(&self, key: &[u8]) -> bool;

    /// Returns the key of the prior upstream branch or value, within the node
    ///
    /// This method will never be called with a zero-length key.
    /// Returns &[] if `key` is descended from the root and therefore has no upstream branch.
    /// Returns &[] if `key` does not exist within the node.
    /// Returns the path to a value within the node, if there is a value located at a prefix of `key`
    fn prior_branch_key(&self, key: &[u8]) -> &[u8];

    /// Returns the child of this node that is immediately before or after the child identified by `key`
    ///
    /// Returns None if the found child node is already the first or last child, or if `key` does not
    /// identify any contained subnode
    ///
    /// If 'next == true` then the returned child will be immediately after to the node found by
    /// `key`, otherwise it will be immedtely before
    ///
    /// NOTE: This method will never be called with a zero-length key
    fn get_sibling_of_child(&self, key: &[u8], next: bool) -> (Option<u8>, Option<&dyn TrieNode<V, A>>);

    /// Returns a new node which is a clone or reference to the portion of the node rooted at `key`, or
    /// `None` if `key` does not specify a path within the node
    ///
    /// If `key.len() == 0` this method will return a reference to or a clone of the node.
    ///
    /// If `self.node_is_empty() == true`, this method should return `AbstractNodeRef::None`
    fn get_node_at_key(&self, key: &[u8]) -> AbstractNodeRef<'_, V, A>;

    /// Returns a node which is the the portion of the node rooted at `key`, or `None` if `key` does
    /// not specify a path within the node
    ///
    /// WARNING: This method may leave the node empty
    ///
    /// This method should never be called with `key.len() == 0`
    fn take_node_at_key(&mut self, key: &[u8]) -> Option<TrieNodeODRc<V, A>>;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types
    fn pjoin_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: Lattice;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types
    fn join_into_dyn(&mut self, other: TrieNodeODRc<V, A>) -> (AlgebraicStatus, Result<(), TrieNodeODRc<V, A>>) where V: Lattice;

    /// Returns a node composed of the children of `self`, `byte_cnt` bytes downstream, all joined together,
    /// or `None` if the node has no children at that depth
    ///
    /// After this method, `self` will be invalid and/ or empty, and should be replaced with the result.
    ///
    /// QUESTION: Is there a value to a "copying" version of drop_head?  It has higher overheads but could
    /// be safely implemented by the [crate::zipper::ReadZipper].
    fn drop_head_dyn(&mut self, byte_cnt: usize) -> Option<TrieNodeODRc<V, A>> where V: Lattice;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types
    fn pmeet_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: Lattice;

    /// Allows for the implementation of the DistributiveLattice algebraic operations
    fn psubtract_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: DistributiveLattice;

    /// Allows for the implementation of the Quantale algebraic operations
    fn prestrict_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>>;

    /// Returns a clone of the node in its own Rc
    fn clone_self(&self) -> TrieNodeODRc<V, A>;
}

/// Implements methods to get the concrete type from a dynamic TrieNode
//GOAT, see if this trait can be eliminated once we no longer need to do dyn dispatch
pub trait TrieNodeDowncast<V: Clone + Send + Sync, A: Allocator> {
    /// Returns the tag associated with the node type
    fn tag(&self) -> usize;

    /// Returns a [TaggedNodeRef] referencing this node
    fn as_tagged(&self) -> TaggedNodeRef<'_, V, A>;

    /// Returns a [TaggedNodeRefMut] referencing this node
    fn as_tagged_mut(&mut self) -> TaggedNodeRefMut<'_, V, A>;

    /// Migrates the contents of the node into a new CellByteNode.  After this method, `self` will be empty
    fn convert_to_cell_node(&mut self) -> TrieNodeODRc<V, A>;
}

/// Special sentinel token value indicating iteration of a node has not been initialized
pub const NODE_ITER_INVALID: u128 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

/// Special sentinel token value indicating iteration of a node has concluded
pub const NODE_ITER_FINISHED: u128 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE;

/// Internal.  A pointer to an onward link or a value contained within a node
pub enum PayloadRef<'a, V: Clone + Send + Sync, A: Allocator> {
    None,
    Val(&'a V),
    Child(&'a TrieNodeODRc<V, A>),
}

// Deriving Clone puts an unnecessary bound on `V`
impl<V: Clone + Send + Sync, A: Allocator> Clone for PayloadRef<'_, V, A> {
    fn clone(&self) -> Self {
        match self {
            Self::None => Self::None,
            Self::Val(v) => Self::Val(v),
            Self::Child(c) => Self::Child(c)
        }
    }
}
impl<V: Clone + Send + Sync, A: Allocator> Copy for PayloadRef<'_, V, A> {}

impl<V: Clone + Send + Sync, A: Allocator> PartialEq for PayloadRef<'_, V, A> {
    #[inline]
    fn eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::None, Self::None) => true,
            (Self::Val(l_val), Self::Val(r_val)) => core::ptr::eq(*l_val, *r_val),
            (Self::Child(l_link), Self::Child(r_link)) => core::ptr::eq(*l_link, *r_link),
            _ => false
        }
    }
}
impl<V: Clone + Send + Sync, A: Allocator> Eq for PayloadRef<'_, V, A> {}

impl<V: Clone + Send + Sync, A: Allocator> Default for PayloadRef<'_, V, A> {
    fn default() -> Self {
        Self::None
    }
}

impl<'a, V: Clone + Send + Sync, A: Allocator> PayloadRef<'a, V, A> {
    pub fn is_none(&self) -> bool {
        match self {
            Self::None => true,
            _ => false
        }
    }
    pub fn is_val(&self) -> bool {
        match self {
            Self::Val(_) => true,
            _ => false
        }
    }
    pub fn child(&self) -> &'a TrieNodeODRc<V, A> {
        match self {
            Self::Child(child) => child,
            _ => panic!()
        }
    }
    pub fn val(&self) -> &'a V {
        match self {
            Self::Val(val) => val,
            _ => panic!()
        }
    }
}

#[derive(Clone)]
pub(crate) enum ValOrChild<V: Clone + Send + Sync, A: Allocator> {
    Val(V),
    Child(TrieNodeODRc<V, A>)
}

impl<V: Clone + Send + Sync, A: Allocator> core::fmt::Debug for ValOrChild<V, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Val(_v) => write!(f, "ValOrChild::Val"), //Don't want to restrict the impl to V: Debug
            Self::Child(c) => write!(f, "ValOrChild::Child{{ {c:?} }}"),
        }
    }
}

impl<V: Clone + Send + Sync, A: Allocator> ValOrChild<V, A> {
    pub fn into_child(self) -> TrieNodeODRc<V, A> {
        match self {
            Self::Child(child) => child,
            _ => panic!()
        }
    }
    pub fn into_val(self) -> V {
        match self {
            Self::Val(val) => val,
            _ => panic!()
        }
    }
    pub fn from_union<const IS_CHILD: bool>(union: ValOrChildUnion<V, A>) -> Self {
        match IS_CHILD {
            true => Self::Child(unsafe{ union.into_child() }),
            false => Self::Val(unsafe{ union.into_val() })
        }
    }
}

pub union ValOrChildUnion<V: Clone + Send + Sync, A: Allocator> {
    pub child: ManuallyDrop<TrieNodeODRc<V, A>>,
    #[cfg(feature = "slim_ptrs")]
    pub val: ManuallyDrop<LocalOrHeap<V, [u8; 8]>>,
    #[cfg(not(feature = "slim_ptrs"))]
    pub val: ManuallyDrop<LocalOrHeap<V, [u8; 16]>>,
    pub _unused: ()
}

impl<V: Clone + Send + Sync, A: Allocator> Default for ValOrChildUnion<V, A> {
    fn default() -> Self {
        Self { _unused: () }
    }
}
impl<V: Clone + Send + Sync, A: Allocator> From<V> for ValOrChildUnion<V, A> {
    fn from(val: V) -> Self {
        Self{ val: ManuallyDrop::new(LocalOrHeap::new(val)) }
    }
}
impl<V: Clone + Send + Sync, A: Allocator> From<TrieNodeODRc<V, A>> for ValOrChildUnion<V, A> {
    fn from(child: TrieNodeODRc<V, A>) -> Self {
        Self{ child: ManuallyDrop::new(child) }
    }
}
impl<V: Clone + Send + Sync, A: Allocator> From<ValOrChild<V, A>> for ValOrChildUnion<V, A> {
    fn from(voc: ValOrChild<V, A>) -> Self {
        match voc {
            ValOrChild::Child(child) => Self{ child: ManuallyDrop::new(child) },
            ValOrChild::Val(val) => Self{ val: ManuallyDrop::new(LocalOrHeap::new(val)) }
        }
    }
}
impl<V: Clone + Send + Sync, A: Allocator> ValOrChildUnion<V, A> {
    pub unsafe fn into_val(self) -> V {
        LocalOrHeap::into_inner(ManuallyDrop::into_inner(self.val))
    }
    pub unsafe fn into_child(self) -> TrieNodeODRc<V, A> {
        ManuallyDrop::into_inner(self.child)
    }
}

/// An implementation of pmeet_dyn that should be correct for any two node types, Although it
/// certainly won't be optimally efficient.
///
/// WARNING: just like [TrieNode::node_get_payloads], the keys in `self_payloads` must be in
/// sorted order.
//
//GOAT: I have confirmed that this function behaves no more conservatively than the function it replaces.
// In other words, I have confirmed that, in tests where the old function was behaving correctly, this
// function returns *identical* results.  Furthermore those same tests are the ones where the 20% slowdown
// was observed.  Therefore the issue is simply the higher overheads of this function.
//
//The next port of call for optimization is probably to remove the recursion
pub(crate) fn pmeet_generic<const MAX_PAYLOAD_CNT: usize, V, A: Allocator, MergeF>(self_payloads: &[(&[u8], PayloadRef<V, A>)], other: &dyn TrieNode<V, A>, merge_f: MergeF) -> AlgebraicResult<TrieNodeODRc<V, A>>
    where
    MergeF: FnOnce(&mut [Option<ValOrChild<V, A>>]) -> TrieNodeODRc<V, A>,
    V: Clone + Send + Sync + Lattice
{
    let mut request_keys = ArrayVec::<(&[u8], bool), MAX_PAYLOAD_CNT>::new();
    //GOAT, we can remove the `Option<>` around the `FatAlgebraicResult`, once we are satisfied that
    // we never fail to set a result, and we never attempt to set the same result more than once.
    let mut element_results = ArrayVec::<Option<FatAlgebraicResult<ValOrChild<V, A>>>, MAX_PAYLOAD_CNT>::new();
    let mut request_results = ArrayVec::<(usize, PayloadRef<V, A>), MAX_PAYLOAD_CNT>::new();
    for (self_key, self_payload) in self_payloads.iter() {
        debug_assert!(!self_payload.is_none());
        request_keys.push((self_key, self_payload.is_val()));
        element_results.push(None);
        request_results.push((0, PayloadRef::default()));
    }

    let is_exhaustive = pmeet_generic_internal::<MAX_PAYLOAD_CNT, V, A>(self_payloads, &mut request_keys[..], &mut request_results[..], &mut element_results[..], other);
    let mut is_none = true;
    let mut combined_mask = SELF_IDENT | COUNTER_IDENT;
    let mut result_payloads = ArrayVec::<Option<ValOrChild<V, A>>, MAX_PAYLOAD_CNT>::new();
    for result in element_results {
        let result = result.unwrap();
        combined_mask &= result.identity_mask;
        is_none = is_none && result.element.is_none();
        result_payloads.push(result.element);
    }

    if is_none {
        return AlgebraicResult::None
    }
    if !is_exhaustive {
        combined_mask &= !COUNTER_IDENT;
    }
    if combined_mask > 0 {
        return AlgebraicResult::Identity(combined_mask)
    }
    AlgebraicResult::Element(merge_f(&mut result_payloads[..]))
}

pub(crate) fn node_count_branches_recursive<V: Clone + Send + Sync, A: Allocator>(node: &dyn TrieNode<V, A>, key: &[u8]) -> usize {
    if key.len() == 0 {
        return node.count_branches(b"");
    }
    match node.node_get_child(key) {
        Some((consumed_bytes, child_node)) => {
            let child_node = child_node.borrow();
            if key.len() >= consumed_bytes {
                child_node.count_branches(&key[consumed_bytes..])
            } else {
                0
            }
        },
        None => node.count_branches(key)
    }
}

/// Internal function to implement the recursive part of `pmeet_generic`
pub(crate) fn pmeet_generic_internal<'trie, const MAX_PAYLOAD_CNT: usize, V, A: Allocator>(self_payloads: &[(&[u8], PayloadRef<V, A>)], keys: &mut [(&[u8], bool)], request_results: &mut [(usize, PayloadRef<'trie, V, A>)], results: &mut [Option<FatAlgebraicResult<ValOrChild<V, A>>>], other_node: &'trie dyn TrieNode<V, A>) -> bool
    where V: Clone + Send + Sync + Lattice
{
    //If is_exhaustive gets set to `false`, then the pmeet method cannot return a `COUNTER_IDENTITY` result
    let mut is_exhaustive = true;

    //Get the payload results from the node
    if !other_node.node_get_payloads(&keys[..], request_results) {
        is_exhaustive = false;
    }

    //Divide the results into groups based on the returned node.  Because keys must be
    // in sorted order, we can assume that query results returning the same node will
    // be contiguous.
    //NOTE: It's theoretically possible (although pretty unlikely) that a node will
    // have multiple discontinuous internal paths leading to the same child node, however
    // the TrieNodeODRc pointers will be different in that case, so this logic is still
    // correct.
    let mut cur_group: Option<(usize, &TrieNodeODRc<V, A>)> = None;
    for idx in 0..keys.len() {
        let (consumed_bytes, payload) = core::mem::take(request_results.get_mut(idx).unwrap());
        if !payload.is_none() {
            let is_val = keys[idx].1;
            if consumed_bytes < keys[idx].0.len() {
                keys[idx].0 = &keys[idx].0[consumed_bytes..];
                debug_assert!(!payload.is_val());
                let child = payload.child();

                //Continue to grow range, or do the recursive call, depending on whether
                // we have the same node as the previous time through the loop
                if cur_group.is_some() {
                    if (cur_group.as_ref().unwrap().1 as *const TrieNodeODRc<V, A>) != (child as *const TrieNodeODRc<V, A>) {
                        pmeet_generic_recursive_reset::<MAX_PAYLOAD_CNT, V, A>(&mut cur_group, &mut is_exhaustive, idx, self_payloads, keys, request_results, results);
                        cur_group = Some((idx, child));
                    }
                } else {
                    cur_group = Some((idx, child));
                }
            } else {
                pmeet_generic_recursive_reset::<MAX_PAYLOAD_CNT, V, A>(&mut cur_group, &mut is_exhaustive, idx, self_payloads, keys, request_results, results);

                //We've arrived at a contained value or onward link that has a correspondence
                // to one of the values or links in `self`
                debug_assert_eq!(consumed_bytes, keys[idx].0.len());
                debug_assert_eq!(is_val, payload.is_val());
                let result = match &self_payloads[idx].1 {
                    PayloadRef::Child(self_link) => {
                        let other_link = payload.child();
                        let result = self_link.pmeet(other_link);
                        FatAlgebraicResult::from_binary_op_result(result, self_link, other_link)
                            .map(|child| ValOrChild::Child(child))
                    },
                    PayloadRef::Val(self_val) => {
                        let other_val = payload.val();
                        let result = (*self_val).pmeet(other_val);
                        FatAlgebraicResult::from_binary_op_result(result, *self_val, other_val)
                            .map(|val| ValOrChild::Val(val))
                    },
                    _ => unreachable!()
                };
                //GOAT, use the commented-out asserts when we get rid of the option wrapping the FatAlgebraicResult
                debug_assert!(results[idx].is_none());
                // debug_assert!(results[idx].element.is_none());
                // debug_assert_eq!(results[idx].mask, 0);
                results[idx] = Some(result);
            }
        } else {
            pmeet_generic_recursive_reset::<MAX_PAYLOAD_CNT, V, A>(&mut cur_group, &mut is_exhaustive, idx, self_payloads, keys, request_results, results);

            let result = match &self_payloads[idx].1 {
                PayloadRef::Child(self_link) => {
                    match other_node.get_node_at_key(keys[idx].0).into_option() {
                        Some(other_onward_node) => {
                            let result = self_link.borrow().pmeet_dyn(other_onward_node.borrow());
                            FatAlgebraicResult::from_binary_op_result(result, self_link, &other_onward_node)
                                .map(|child| ValOrChild::Child(child))
                        },
                        None => {
                            FatAlgebraicResult::new(COUNTER_IDENT, None)
                        }
                    }
                },
                PayloadRef::Val(_self_val) => {
                    //If self_payload is a val and we didn't get a corresponding val, then this result is None
                    FatAlgebraicResult::new(COUNTER_IDENT, None)
                },
                _ => unreachable!()
            };
            results[idx] = Some(result);
        }
    }
    pmeet_generic_recursive_reset::<MAX_PAYLOAD_CNT, V, A>(&mut cur_group, &mut is_exhaustive, keys.len(), self_payloads, keys, request_results, results);

    is_exhaustive
}

/// Effectively part of `pmeet_generic_internal`, but factored out separately because it's called in
/// several different places.  Resets the `cur_group` state and does a recursive call of `pmeet_generic_internal`
#[inline]
fn pmeet_generic_recursive_reset<'trie, const MAX_PAYLOAD_CNT: usize, V, A: Allocator>(cur_group: &mut Option<(usize, &'trie TrieNodeODRc<V, A>)>, is_exhaustive: &mut bool, idx: usize, self_payloads: &[(&[u8], PayloadRef<V, A>)], keys: &mut [(&[u8], bool)], request_results: &mut [(usize, PayloadRef<'trie, V, A>)], results: &mut [Option<FatAlgebraicResult<ValOrChild<V, A>>>])
    where V: Clone + Send + Sync + Lattice
{
    match core::mem::take(cur_group) {
        Some((group_start, next_node)) => {
            let group_keys = &mut keys[group_start..idx];
            let group_results = &mut results[group_start..idx];
            let group_self_payloads = &self_payloads[group_start..idx];
            if !pmeet_generic_internal::<MAX_PAYLOAD_CNT, V, A>(group_self_payloads, group_keys, request_results, group_results, next_node.borrow()) {
                *is_exhaustive = false;
            }
        },
        None => {}
    }
}

pub enum AbstractNodeRef<'a, V: Clone + Send + Sync, A: Allocator> {
    None,
    BorrowedDyn(&'a dyn TrieNode<V, A>),
    BorrowedRc(&'a TrieNodeODRc<V, A>),
    BorrowedTiny(TinyRefNode<'a, V, A>),
    OwnedRc(TrieNodeODRc<V, A>)
}

impl<'a, V: Clone + Send + Sync, A: Allocator> core::fmt::Debug for AbstractNodeRef<'a, V, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::None => write!(f, "AbstractNodeRef::None"),
            Self::BorrowedDyn(_) => write!(f, "AbstractNodeRef::BorrowedDyn"),
            Self::BorrowedRc(_) => write!(f, "AbstractNodeRef::BorrowedRc"),
            Self::BorrowedTiny(_) => write!(f, "AbstractNodeRef::BorrowedTiny"),
            Self::OwnedRc(_) => write!(f, "AbstractNodeRef::OwnedRc"),
        }
    }
}

impl<'a, V: Clone + Send + Sync, A: Allocator> AbstractNodeRef<'a, V, A> {
    pub fn is_none(&self) -> bool {
        matches!(self, AbstractNodeRef::None)
    }
    pub fn borrow(&self) -> &dyn TrieNode<V, A> {
        match self {
            AbstractNodeRef::None => panic!(),
            AbstractNodeRef::BorrowedDyn(node) => *node,
            AbstractNodeRef::BorrowedRc(rc) => rc.borrow(),
            AbstractNodeRef::BorrowedTiny(tiny) => tiny,
            AbstractNodeRef::OwnedRc(rc) => rc.borrow()
        }
    }
    pub fn try_borrow(&self) -> Option<&dyn TrieNode<V, A>> {
        match self {
            AbstractNodeRef::None => None,
            AbstractNodeRef::BorrowedDyn(node) => Some(*node),
            AbstractNodeRef::BorrowedRc(rc) => Some(rc.borrow()),
            AbstractNodeRef::BorrowedTiny(tiny) => Some(tiny),
            AbstractNodeRef::OwnedRc(rc) => Some(rc.borrow())
        }
    }
    pub fn into_option(self) -> Option<TrieNodeODRc<V, A>> {
        match self {
            AbstractNodeRef::None => None,
            AbstractNodeRef::BorrowedDyn(node) => Some(node.clone_self()),
            AbstractNodeRef::BorrowedRc(rc) => Some(rc.clone()),
            AbstractNodeRef::BorrowedTiny(tiny) => tiny.into_full().map(|list_node| TrieNodeODRc::new_in(list_node, tiny.alloc)),
            AbstractNodeRef::OwnedRc(rc) => Some(rc)
        }
    }
}

/// A stable tag index for each concrete node type
pub(crate) const EMPTY_NODE_TAG: usize = 0;
pub(crate) const DENSE_BYTE_NODE_TAG: usize = 1;
pub(crate) const LINE_LIST_NODE_TAG: usize = 2;
pub(crate) const CELL_BYTE_NODE_TAG: usize = 3;

pub use tagged_node_ref::TaggedNodeRef;
pub use tagged_node_ref::TaggedNodeRefMut;

#[cfg(not(feature = "slim_ptrs"))]
mod tagged_node_ref {
    use super::*;
    use crate::empty_node::EmptyNode;

    /// A reference to a node with a concrete type
    pub enum TaggedNodeRef<'a, V: Clone + Send + Sync, A: Allocator> {
        DenseByteNode(&'a DenseByteNode<V, A>),
        LineListNode(&'a LineListNode<V, A>),
        TinyRefNode(&'a TinyRefNode<'a, V, A>),
        #[cfg(feature = "bridge_nodes")]
        BridgeNode(&'a BridgeNode<V>),
        CellByteNode(&'a CellByteNode<V, A>),
        EmptyNode,
    }
    impl<V: Clone + Send + Sync, A: Allocator> Clone for TaggedNodeRef<'_, V, A> {
        fn clone(&self) -> Self {
            //Ugh!  This manual impl is so we can implement `Copy` without a bound on `V: Copy`
            //But hopefully there is a way to do this without so much boilerplate (or unsafe either)
            match self {
                Self::DenseByteNode(node) => Self::DenseByteNode(node),
                Self::LineListNode(node) => Self::LineListNode(node),
                Self::TinyRefNode(node) => Self::TinyRefNode(node),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => Self::BridgeNode(node),
                Self::CellByteNode(node) => Self::CellByteNode(node),
                Self::EmptyNode => Self::EmptyNode,
            }
        }
    }
    impl<V: Clone + Send + Sync, A: Allocator> Copy for TaggedNodeRef<'_, V, A> {}

    impl<'a, V: Clone + Send + Sync, A: Allocator> TaggedNodeRef<'a, V, A> {
        #[inline]
        pub fn empty_node() -> Self {
            Self::EmptyNode
        }
        #[inline]
        pub fn into_dyn(self) -> &'a dyn TrieNode<V, A> {
            match self {
                Self::DenseByteNode(node) => node as &dyn TrieNode<V, A>,
                Self::LineListNode(node) => node as &dyn TrieNode<V, A>,
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node as &dyn TrieNode<V, A>,
                Self::TinyRefNode(node) => node as &dyn TrieNode<V, A>,
                Self::CellByteNode(node) => node as &dyn TrieNode<V, A>,
                Self::EmptyNode => &crate::empty_node::EMPTY_NODE as &dyn TrieNode<V, A>,
            }
        }
    }

    /// A mutable reference to a node with a concrete type
    pub enum TaggedNodeRefMut<'a, V: Clone + Send + Sync, A: Allocator> {
        DenseByteNode(&'a mut DenseByteNode<V, A>),
        LineListNode(&'a mut LineListNode<V, A>),
        #[cfg(feature = "bridge_nodes")]
        BridgeNode(&'a mut BridgeNode<V, A>),
        CellByteNode(&'a mut CellByteNode<V, A>),
        Unsupported,
    }

    impl<'a, V: Clone + Send + Sync, A: Allocator> TaggedNodeRefMut<'a, V, A> {
        #[inline]
        pub fn into_dyn(self) -> &'a mut dyn TrieNode<V, A> {
            match self {
                Self::DenseByteNode(node) => node as &mut dyn TrieNode<V, A>,
                Self::LineListNode(node) => node as &mut dyn TrieNode<V, A>,
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node as &mut dyn TrieNode<V, A>,
                Self::CellByteNode(node) => node as &mut dyn TrieNode<V, A>,
                Self::Unsupported => unsafe{ unreachable_unchecked() },
            }
        }
    }

    //NOTE: this is a not derived because we don't want to restrict the impl to V: Debug
    impl<V: Clone + Send + Sync, A: Allocator> core::fmt::Debug for TaggedNodeRefMut<'_, V, A> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                Self::DenseByteNode(node) => write!(f, "{node:?}"),
                Self::LineListNode(node) => write!(f, "{node:?}"),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => write!(f, "{node:?}"),
                Self::CellByteNode(node) => write!(f, "{node:?}"),
                Self::Unsupported => write!(f, "Unsupported node type"),
            }
        }
    }

    //NOTE: this is a not derived because we don't want to restrict the impl to V: Debug
    impl<V: Clone + Send + Sync, A: Allocator> core::fmt::Debug for TaggedNodeRef<'_, V, A> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                Self::DenseByteNode(node) => write!(f, "{node:?}"),
                Self::LineListNode(node) => write!(f, "{node:?}"),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => write!(f, "{node:?}"),
                Self::TinyRefNode(node) => write!(f, "{node:?}"),
                Self::CellByteNode(node) => write!(f, "{node:?}"),
                Self::EmptyNode => write!(f, "{EmptyNode:?}"),
            }
        }
    }

    impl<'a, V: Clone + Send + Sync, A: Allocator> TaggedNodeRef<'a, V, A> {
        #[inline]
        pub fn borrow(&self) -> &'a dyn TrieNode<V, A> {
            match self {
                Self::DenseByteNode(node) => *node as &dyn TrieNode<V, A>,
                Self::LineListNode(node) => *node as &dyn TrieNode<V, A>,
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => *node as &dyn TrieNode<V, A>,
                Self::TinyRefNode(node) => *node as &dyn TrieNode<V, A>,
                Self::CellByteNode(node) => *node as &dyn TrieNode<V, A>,
                Self::EmptyNode => &crate::empty_node::EMPTY_NODE as &dyn TrieNode<V, A>,
            }
        }
        #[inline]
        pub fn node_key_overlap(&self, key: &[u8]) -> usize {
            match self {
                Self::DenseByteNode(node) => node.node_key_overlap(key),
                Self::LineListNode(node) => node.node_key_overlap(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.node_key_overlap(key),
                Self::TinyRefNode(node) => node.node_key_overlap(key),
                Self::CellByteNode(node) => node.node_key_overlap(key),
                Self::EmptyNode => 0
            }
        }
        pub fn node_contains_partial_key(&self, key: &[u8]) -> bool {
            match self {
                Self::DenseByteNode(node) => node.node_contains_partial_key(key),
                Self::LineListNode(node) => node.node_contains_partial_key(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.node_contains_partial_key(key),
                Self::TinyRefNode(node) => node.node_contains_partial_key(key),
                Self::CellByteNode(node) => node.node_contains_partial_key(key),
                Self::EmptyNode => false
            }
        }
        #[inline(always)]
        pub fn node_get_child(&self, key: &[u8]) -> Option<(usize, &'a TrieNodeODRc<V, A>)> {
            match self {
                Self::DenseByteNode(node) => node.node_get_child(key),
                Self::LineListNode(node) => node.node_get_child(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.node_get_child(key),
                Self::TinyRefNode(node) => node.node_get_child(key),
                Self::CellByteNode(node) => node.node_get_child(key),
                Self::EmptyNode => None,
            }
        }

        // fn node_get_child_and_val_mut<'a>(&'a mut self, key: &[u8]) -> Option<(usize, Option<&'a mut V>, Option<&'a mut TrieNodeODRc<V>>)>;

        // fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>)>;

        // fn node_replace_child(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> &mut dyn TrieNode<V>;

        pub fn node_contains_val(&self, key: &[u8]) -> bool {
            match self {
                Self::DenseByteNode(node) => node.node_contains_val(key),
                Self::LineListNode(node) => node.node_contains_val(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.node_contains_val(key),
                Self::TinyRefNode(node) => node.node_contains_val(key),
                Self::CellByteNode(node) => node.node_contains_val(key),
                Self::EmptyNode => false,
            }
        }
        pub fn node_get_val(&self, key: &[u8]) -> Option<&'a V> {
            match self {
                Self::DenseByteNode(node) => node.node_get_val(key),
                Self::LineListNode(node) => node.node_get_val(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.node_get_val(key),
                Self::TinyRefNode(node) => node.node_get_val(key),
                Self::CellByteNode(node) => node.node_get_val(key),
                Self::EmptyNode => None,
            }
        }

        // fn node_get_val_mut(&mut self, key: &[u8]) -> Option<&mut V>;

        // fn node_set_val(&mut self, key: &[u8], val: V) -> Result<(Option<V>, bool), TrieNodeODRc<V>>;

        // fn node_remove_val(&mut self, key: &[u8]) -> Option<V>;

        // fn node_set_branch(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> Result<bool, TrieNodeODRc<V>>;

        // fn node_remove_all_branches(&mut self, key: &[u8]) -> bool;

        // fn node_remove_unmasked_branches(&mut self, key: &[u8], mask: ByteMask);

        // fn node_is_empty(&self) -> bool;

        #[inline(always)]
        pub fn new_iter_token(&self) -> u128 {
            match self {
                Self::DenseByteNode(node) => node.new_iter_token(),
                Self::LineListNode(node) => node.new_iter_token(),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.new_iter_token(),
                Self::TinyRefNode(node) => node.new_iter_token(),
                Self::CellByteNode(node) => node.new_iter_token(),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::new_iter_token(&crate::empty_node::EMPTY_NODE),
            }
        }
        #[inline(always)]
        pub fn iter_token_for_path(&self, key: &[u8]) -> u128 {
            match self {
                Self::DenseByteNode(node) => node.iter_token_for_path(key),
                Self::LineListNode(node) => node.iter_token_for_path(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.iter_token_for_path(key),
                Self::TinyRefNode(node) => node.iter_token_for_path(key),
                Self::CellByteNode(node) => node.iter_token_for_path(key),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::iter_token_for_path(&crate::empty_node::EMPTY_NODE, key),
            }
        }
        #[inline(always)]
        pub fn next_items(&self, token: u128) -> (u128, &'a[u8], Option<&'a TrieNodeODRc<V, A>>, Option<&'a V>) {
            match self {
                Self::DenseByteNode(node) => node.next_items(token),
                Self::LineListNode(node) => node.next_items(token),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.next_items(token),
                Self::TinyRefNode(node) => node.next_items(token),
                Self::CellByteNode(node) => node.next_items(token),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::next_items(&crate::empty_node::EMPTY_NODE, token),
            }
        }

        // fn node_val_count(&self, cache: &mut HashMap<*const dyn TrieNode<V>, usize>) -> usize;

        // #[cfg(feature = "counters")]
        // fn item_count(&self) -> usize;

        pub fn node_first_val_depth_along_key(&self, key: &[u8]) -> Option<usize> {
            match self {
                Self::DenseByteNode(node) => node.node_first_val_depth_along_key(key),
                Self::LineListNode(node) => node.node_first_val_depth_along_key(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.node_first_val_depth_along_key(key),
                Self::TinyRefNode(node) => node.node_first_val_depth_along_key(key),
                Self::CellByteNode(node) => node.node_first_val_depth_along_key(key),
                Self::EmptyNode => None,
            }
        }

        pub fn nth_child_from_key(&self, key: &[u8], n: usize) -> (Option<u8>, Option<&'a dyn TrieNode<V, A>>) {
            match self {
                Self::DenseByteNode(node) => node.nth_child_from_key(key, n),
                Self::LineListNode(node) => node.nth_child_from_key(key, n),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.nth_child_from_key(key, n),
                Self::TinyRefNode(node) => node.nth_child_from_key(key, n),
                Self::CellByteNode(node) => node.nth_child_from_key(key, n),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::nth_child_from_key(&crate::empty_node::EMPTY_NODE, key, n),
            }
        }
        pub fn first_child_from_key(&self, key: &[u8]) -> (Option<&'a [u8]>, Option<&'a dyn TrieNode<V, A>>) {
            match self {
                Self::DenseByteNode(node) => node.first_child_from_key(key),
                Self::LineListNode(node) => node.first_child_from_key(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.first_child_from_key(key),
                Self::TinyRefNode(node) => node.first_child_from_key(key),
                Self::CellByteNode(node) => node.first_child_from_key(key),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::first_child_from_key(&crate::empty_node::EMPTY_NODE, key),
            }
        }
        #[inline(always)]
        pub fn count_branches(&self, key: &[u8]) -> usize {
            match self {
                Self::DenseByteNode(node) => node.count_branches(key),
                Self::LineListNode(node) => node.count_branches(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.count_branches(key),
                Self::TinyRefNode(node) => node.count_branches(key),
                Self::CellByteNode(node) => node.count_branches(key),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::count_branches(&crate::empty_node::EMPTY_NODE, key),
            }
        }
        #[inline(always)]
        pub fn node_branches_mask(&self, key: &[u8]) -> ByteMask {
            match self {
                Self::DenseByteNode(node) => node.node_branches_mask(key),
                Self::LineListNode(node) => node.node_branches_mask(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.node_branches_mask(key),
                Self::TinyRefNode(node) => node.node_branches_mask(key),
                Self::CellByteNode(node) => node.node_branches_mask(key),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::node_branches_mask(&crate::empty_node::EMPTY_NODE, key),
            }
        }
        #[inline(always)]
        pub fn is_leaf(&self, key: &[u8]) -> bool {
            match self {
                Self::DenseByteNode(node) => node.is_leaf(key),
                Self::LineListNode(node) => node.is_leaf(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.is_leaf(key),
                Self::TinyRefNode(node) => node.is_leaf(key),
                Self::CellByteNode(node) => node.is_leaf(key),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::is_leaf(&crate::empty_node::EMPTY_NODE, key),
            }
        }
        pub fn prior_branch_key(&self, key: &[u8]) -> &[u8] {
            match self {
                Self::DenseByteNode(node) => node.prior_branch_key(key),
                Self::LineListNode(node) => node.prior_branch_key(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.prior_branch_key(key),
                Self::TinyRefNode(node) => node.prior_branch_key(key),
                Self::CellByteNode(node) => node.prior_branch_key(key),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::prior_branch_key(&crate::empty_node::EMPTY_NODE, key),
            }
        }
        pub fn get_sibling_of_child(&self, key: &[u8], next: bool) -> (Option<u8>, Option<&'a dyn TrieNode<V, A>>) {
            match self {
                Self::DenseByteNode(node) => node.get_sibling_of_child(key, next),
                Self::LineListNode(node) => node.get_sibling_of_child(key, next),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.get_sibling_of_child(key, next),
                Self::TinyRefNode(node) => node.get_sibling_of_child(key, next),
                Self::CellByteNode(node) => node.get_sibling_of_child(key, next),
                Self::EmptyNode => <EmptyNode as TrieNode<V, A>>::get_sibling_of_child(&crate::empty_node::EMPTY_NODE, key, next),
            }
        }
        pub fn get_node_at_key(&self, key: &[u8]) -> AbstractNodeRef<'_, V, A> {
            match self {
                Self::DenseByteNode(node) => node.get_node_at_key(key),
                Self::LineListNode(node) => node.get_node_at_key(key),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(node) => node.get_node_at_key(key),
                Self::TinyRefNode(node) => node.get_node_at_key(key),
                Self::CellByteNode(node) => node.get_node_at_key(key),
                Self::EmptyNode => EmptyNode.get_node_at_key(key),
            }
        }

        // fn take_node_at_key(&mut self, key: &[u8]) -> Option<TrieNodeODRc<V>>;

        // fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice;

        // fn join_into_dyn(&mut self, other: TrieNodeODRc<V>) where V: Lattice;

        // fn drop_head_dyn(&mut self, byte_cnt: usize) -> Option<TrieNodeODRc<V>> where V: Lattice;

        // fn meet_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: Lattice;

        // fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> (bool, Option<TrieNodeODRc<V>>) where V: DistributiveLattice;

        // fn prestrict_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>>;

        #[inline(always)]
        pub fn as_dense(&self) -> Option<&'a DenseByteNode<V, A>> {
            match self {
                Self::DenseByteNode(node) => Some(node),
                Self::LineListNode(_) => None,
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(_) => None,
                Self::TinyRefNode(_) => None,
                Self::CellByteNode(_) => None,
                Self::EmptyNode => None,
            }
        }

        // fn as_dense_mut(&mut self) -> Option<&mut DenseByteNode<V>>;

        #[inline(always)]
        pub fn as_list(&self) -> Option<&'a LineListNode<V, A>> {
            match self {
                Self::DenseByteNode(_) => None,
                Self::LineListNode(node) => Some(node),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(_) => None,
                Self::TinyRefNode(_) => None,
                Self::CellByteNode(_) => None,
                Self::EmptyNode => None,
            }
        }

        #[cfg(feature = "bridge_nodes")]
        #[inline(always)]
        pub fn as_bridge(&self) -> Option<&'a BridgeNode<V, A>> {
            match self {
                Self::DenseByteNode(_) => None,
                Self::LineListNode(_) => None,
                Self::BridgeNode(node) => Some(node),
                Self::TinyRefNode(_) => None,
                Self::CellByteNode(_) => None,
                Self::EmptyNode(_) => None,
            }
        }

        // fn as_list_mut(&mut self) -> Option<&mut LineListNode<V>>;

        // fn as_tagged(&self) -> TaggedNodeRef<V>;

        // fn clone_self(&self) -> TrieNodeODRc<V>;

        #[inline(always)]
        pub fn is_cell_node(&self) -> bool {
            match self {
                Self::CellByteNode(_) => true,
                _ => false
            }
        }
    }

    impl<'a, V: Clone + Send + Sync, A: Allocator> TaggedNodeRefMut<'a, V, A> {
        #[inline(always)]
        pub fn into_dense(self) -> Option<&'a mut DenseByteNode<V, A>> {
            match self {
                Self::DenseByteNode(node) => Some(node),
                Self::LineListNode(_) => None,
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(_) => None,
                Self::CellByteNode(_) => None,
                Self::Unsupported => None,
            }
        }
        #[inline(always)]
        pub fn into_list(self) -> Option<&'a mut LineListNode<V, A>> {
            match self {
                Self::LineListNode(node) => Some(node),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(_) => None,
                Self::DenseByteNode(_) => None,
                Self::CellByteNode(_) => None,
                Self::Unsupported => None,
            }
        }
        #[inline(always)]
        pub fn into_cell_node(self) -> Option<&'a mut CellByteNode<V, A>> {
            match self {
                Self::CellByteNode(node) => Some(node),
                #[cfg(feature = "bridge_nodes")]
                Self::BridgeNode(_) => None,
                Self::DenseByteNode(_) => None,
                Self::LineListNode(_) => None,
                Self::Unsupported => None,
            }
        }
    }
}

#[cfg(feature = "slim_ptrs")]
mod tagged_node_ref {
    use core::marker::PhantomData;
    use crate::trie_node::slim_node_ptr::SlimNodePtr;
    use super::*;

    pub struct TaggedNodeRef<'a, V: Clone + Send + Sync, A: Allocator> {
        ptr: SlimNodePtr<V, A>,
        phantom: PhantomData<&'a V>
    }

    impl<V: Clone + Send + Sync, A: Allocator> Clone for TaggedNodeRef<'_, V, A> {
        fn clone(&self) -> Self {
            //Ugh!  This manual impl is so we can implement `Copy` without a bound on `V: Copy`
            //But hopefully there is a way to do this without so much boilerplate (or unsafe either)
            Self{ ptr: self.ptr, phantom: PhantomData }
        }
    }
    impl<V: Clone + Send + Sync, A: Allocator> Copy for TaggedNodeRef<'_, V, A> {}

    //NOTE: this is a not derived because we don't want to restrict the impl to V: Debug
    impl<V: Clone + Send + Sync, A: Allocator> core::fmt::Debug for TaggedNodeRef<'_, V, A> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            core::fmt::Debug::fmt(&self.ptr, f)
        }
    }

    //GOAT, dead code, hopefully
    // //GOAT, hopefully this is temporary
    // impl<'a, V: Clone + Send + Sync + 'a, A: Allocator + 'a> core::ops::Deref for TaggedNodeRef<'a, V, A> {
    //     type Target = dyn TrieNode<V, A> + 'a;
    //     fn deref(&self) -> &Self::Target {
    //         let (ptr, tag) = self.ptr.get_raw_parts();
    //         match tag {
    //             EMPTY_NODE_TAG => &crate::empty_node::EMPTY_NODE as &dyn TrieNode<V, A>,
    //             DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() },
    //             LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() },
    //             CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() },
    //             _ => unsafe{ unreachable_unchecked() }
    //         }
    //     }
    // }

    impl<'a, V: Clone + Send + Sync + 'a, A: Allocator + 'a> TaggedNodeRef<'a, V, A> {
        #[inline]
        pub(crate) fn empty_node() -> Self {
            Self { ptr: SlimNodePtr::from_raw_parts(core::ptr::without_provenance_mut::<usize>(0xBAADF00D), EMPTY_NODE_TAG), phantom: PhantomData }
        }
        #[inline]
        pub(super) fn from_slim_ptr(ptr: SlimNodePtr<V, A>) -> Self {
            Self { ptr, phantom: PhantomData }
        }
        //GOAT dead code
        // #[inline]
        // unsafe fn from_raw_parts(ptr: *mut core::sync::atomic::AtomicU32, tag: usize) -> Self {
        //     match tag {
        //         EMPTY_NODE_TAG => Self::EmptyNode,
        //         DENSE_BYTE_NODE_TAG => Self::DenseByteNode(&*ptr.cast()),
        //         LINE_LIST_NODE_TAG => Self::LineListNode(&*ptr.cast()),
        //         CELL_BYTE_NODE_TAG => Self::CellByteNode(&*ptr.cast()),
        //         _ => unreachable_unchecked()
        //     }
        // }

        /// Consumes the `TaggedNodeRef` and returns a dyn ptr GOAT: Hopefully we can deprecate this soon
        #[inline]
        pub fn into_dyn(self) -> &'a dyn TrieNode<V, A> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => &crate::empty_node::EMPTY_NODE as &dyn TrieNode<V, A>,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() },
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() },
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() },
                _ => unsafe{ unreachable_unchecked() }
            }
        }
        /// GOAT: Hopefully we can deprecate this soon
        #[inline]
        pub fn borrow(&self) -> &'a dyn TrieNode<V, A> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => &crate::empty_node::EMPTY_NODE as &dyn TrieNode<V, A>,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() },
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() },
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() },
                _ => unsafe{ unreachable_unchecked() }
            }
        }
        pub fn node_contains_partial_key(&self, key: &[u8]) -> bool {
            self.node_key_overlap(key) == key.len()
        }
        #[inline]
        pub fn node_key_overlap(&self, key: &[u8]) -> usize {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => 0,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.node_key_overlap(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.node_key_overlap(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.node_key_overlap(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }
        #[inline]
        pub fn node_get_child(&self, key: &[u8]) -> Option<(usize, &'a TrieNodeODRc<V, A>)> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => None,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.node_get_child(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.node_get_child(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.node_get_child(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        // fn node_get_payloads<'node, 'res>(&'node self, keys: &[(&[u8], bool)], results: &'res mut [(usize, PayloadRef<'node, V, A>)]) -> bool;

        pub fn node_contains_val(&self, key: &[u8]) -> bool {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => false,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.node_contains_val(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.node_contains_val(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.node_contains_val(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        pub fn node_get_val(&self, key: &[u8]) -> Option<&'a V> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => None,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.node_get_val(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.node_get_val(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.node_get_val(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        // fn node_is_empty(&self) -> bool;

        #[inline]
        pub fn new_iter_token(&self) -> u128 {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => 0,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.new_iter_token(),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.new_iter_token(),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.new_iter_token(),
                _ => unsafe{ unreachable_unchecked() }
            }
        }
        #[inline]
        pub fn iter_token_for_path(&self, key: &[u8]) -> u128 {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => 0,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.iter_token_for_path(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.iter_token_for_path(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.iter_token_for_path(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }
        #[inline]
        pub fn next_items(&self, token: u128) -> (u128, &[u8], Option<&'a TrieNodeODRc<V, A>>, Option<&'a V>) {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => (NODE_ITER_FINISHED, &[], None, None),
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.next_items(token),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.next_items(token),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.next_items(token),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        // fn node_val_count(&self, cache: &mut HashMap<*const dyn TrieNode<V, A>, usize>) -> usize;

        // #[cfg(feature = "counters")]
        // fn item_count(&self) -> usize;

        // fn node_first_val_depth_along_key(&self, key: &[u8]) -> Option<usize>;

        pub fn nth_child_from_key(&self, key: &[u8], n: usize) -> (Option<u8>, Option<&'a dyn TrieNode<V, A>>) {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => (None, None),
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.nth_child_from_key(key, n),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.nth_child_from_key(key, n),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.nth_child_from_key(key, n),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        pub fn first_child_from_key(&self, key: &[u8]) -> (Option<&'a [u8]>, Option<&'a dyn TrieNode<V, A>>) {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => (None, None),
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.first_child_from_key(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.first_child_from_key(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.first_child_from_key(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        #[inline]
        pub fn count_branches(&self, key: &[u8]) -> usize {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => 0,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.count_branches(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.count_branches(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.count_branches(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }
        #[inline]
        pub fn node_branches_mask(&self, key: &[u8]) -> ByteMask {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => ByteMask::EMPTY,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.node_branches_mask(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.node_branches_mask(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.node_branches_mask(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }
        // #[inline]
        // fn is_leaf(&self, key: &[u8]) -> bool;

        pub fn prior_branch_key(&self, key: &[u8]) -> &[u8] {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => &[],
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.prior_branch_key(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.prior_branch_key(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.prior_branch_key(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        pub fn get_sibling_of_child(&self, key: &[u8], next: bool) -> (Option<u8>, Option<&'a dyn TrieNode<V, A>>) {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => (None, None),
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.get_sibling_of_child(key, next),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.get_sibling_of_child(key, next),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.get_sibling_of_child(key, next),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        pub fn get_node_at_key(&self, key: &[u8]) -> AbstractNodeRef<'_, V, A> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => AbstractNodeRef::None,
                DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() }.get_node_at_key(key),
                LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() }.get_node_at_key(key),
                CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() }.get_node_at_key(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        // fn pjoin_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: Lattice;

        // fn pmeet_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: Lattice;

        // fn psubtract_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>> where V: DistributiveLattice;

        // fn prestrict_dyn(&self, other: &dyn TrieNode<V, A>) -> AlgebraicResult<TrieNodeODRc<V, A>>;

        // fn clone_self(&self) -> TrieNodeODRc<V, A>;

        #[inline]
        pub fn is_cell_node(&self) -> bool {
            let (_, tag) = self.ptr.get_raw_parts();
            tag == CELL_BYTE_NODE_TAG
        }
    }

    pub struct TaggedNodeRefMut<'a, V: Clone + Send + Sync, A: Allocator> {
        ptr: SlimNodePtr<V, A>,
        phantom: PhantomData<&'a mut V>
    }

    //NOTE: this is a not derived because we don't want to restrict the impl to V: Debug
    impl<V: Clone + Send + Sync, A: Allocator> core::fmt::Debug for TaggedNodeRefMut<'_, V, A> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            core::fmt::Debug::fmt(&self.ptr, f)
        }
    }

    //GOAT, hopefully dead
    // //GOAT, hopefully this is temporary
    // impl<'a, V: Clone + Send + Sync + 'a, A: Allocator + 'a> core::ops::Deref for TaggedNodeRefMut<'a, V, A> {
    //     type Target = dyn TrieNode<V, A> + 'a;
    //     fn deref(&self) -> &Self::Target {
    //         let (ptr, tag) = self.ptr.get_raw_parts();
    //         match tag {
    //             EMPTY_NODE_TAG => &crate::empty_node::EMPTY_NODE as &dyn TrieNode<V, A>,
    //             DENSE_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<DenseByteNode<V, A>>() },
    //             LINE_LIST_NODE_TAG => unsafe{ &*ptr.cast::<LineListNode<V, A>>() },
    //             CELL_BYTE_NODE_TAG => unsafe{ &*ptr.cast::<CellByteNode<V, A>>() },
    //             _ => unsafe{ unreachable_unchecked() }
    //         }
    //     }
    // }
    // //GOAT, hopefully this is temporary
    // impl<'a, V: Clone + Send + Sync + 'a, A: Allocator + 'a> core::ops::DerefMut for TaggedNodeRefMut<'a, V, A> {
    //     fn deref_mut(&mut self) -> &mut Self::Target {
    //         let (ptr, tag) = self.ptr.get_raw_parts();
    //         match tag {
    //             EMPTY_NODE_TAG => unreachable!(),
    //             DENSE_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<DenseByteNode<V, A>>() },
    //             LINE_LIST_NODE_TAG => unsafe{ &mut *ptr.cast::<LineListNode<V, A>>() },
    //             CELL_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<CellByteNode<V, A>>() },
    //             _ => unsafe{ unreachable_unchecked() }
    //         }
    //     }
    // }

    impl<'a, V: Clone + Send + Sync, A: Allocator> TaggedNodeRefMut<'a, V, A> {
        #[inline]
        pub(super) fn from_slim_ptr(ptr: SlimNodePtr<V, A>) -> Self {
            Self { ptr, phantom: PhantomData }
        }
        //GOAT dead code
        // #[inline]
        // unsafe fn from_raw_parts(ptr: *mut core::sync::atomic::AtomicU32, tag: usize) -> Self {
        //     match tag {
        //         DENSE_BYTE_NODE_TAG => Self::DenseByteNode(&mut *ptr.cast()),
        //         LINE_LIST_NODE_TAG => Self::LineListNode(&mut *ptr.cast()),
        //         CELL_BYTE_NODE_TAG => Self::CellByteNode(&mut *ptr.cast()),
        //         _ => { panic!("Invalid Tag: {tag}") } //GOAT put this back to unreachable_unchecked()
        //     }
        // }

        /// GOAT, this is definitely trash.  It's here to keep the same usage pattern for the
        /// dyn dispatch and the table dispatch, but it does ABSOLUTELY NOTHING.  So when it's
        /// time to remove it, we ought to delete it, and then delete it from every location from
        /// which it's called
        pub fn as_tagged_mut(&mut self) -> TaggedNodeRefMut<'_, V, A> {
            Self { ptr: self.ptr, phantom: PhantomData }
        }

        /// GOAT: Hopefully we can deprecate this soon
        #[inline]
        pub fn into_dyn(self) -> &'a mut dyn TrieNode<V, A> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => unreachable!(),
                DENSE_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<DenseByteNode<V, A>>() },
                LINE_LIST_NODE_TAG => unsafe{ &mut *ptr.cast::<LineListNode<V, A>>() },
                CELL_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<CellByteNode<V, A>>() },
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        pub fn node_get_child_mut(self, key: &[u8]) -> Option<(usize, &'a mut TrieNodeODRc<V, A>)> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => unreachable!(),
                DENSE_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<DenseByteNode<V, A>>() }.node_get_child_mut(key),
                LINE_LIST_NODE_TAG => unsafe{ &mut *ptr.cast::<LineListNode<V, A>>() }.node_get_child_mut(key),
                CELL_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<CellByteNode<V, A>>() }.node_get_child_mut(key),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        pub fn join_into_dyn(&mut self, other: TrieNodeODRc<V, A>) -> (AlgebraicStatus, Result<(), TrieNodeODRc<V, A>>) where V: Lattice {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => unreachable!(),
                DENSE_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<DenseByteNode<V, A>>() }.join_into_dyn(other),
                LINE_LIST_NODE_TAG => unsafe{ &mut *ptr.cast::<LineListNode<V, A>>() }.join_into_dyn(other),
                CELL_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<CellByteNode<V, A>>() }.join_into_dyn(other),
                _ => unsafe{ unreachable_unchecked() }
            }
        }

        #[inline(always)]
        pub fn into_dense(self) -> Option<&'a mut DenseByteNode<V, A>> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                DENSE_BYTE_NODE_TAG => Some( unsafe{ &mut *ptr.cast::<DenseByteNode<V, A>>() } ),
                _ => None
            }
        }
        #[inline(always)]
        pub fn into_list(self) -> Option<&'a mut LineListNode<V, A>> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                LINE_LIST_NODE_TAG => Some( unsafe{ &mut *ptr.cast::<LineListNode<V, A>>() } ),
                _ => None
            }
        }
        pub fn convert_to_cell_node(self) -> TrieNodeODRc<V, A> {
            let (ptr, tag) = self.ptr.get_raw_parts();
            match tag {
                EMPTY_NODE_TAG => unreachable!(),
                DENSE_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<DenseByteNode<V, A>>() }.convert_to_cell_node(),
                LINE_LIST_NODE_TAG => unsafe{ &mut *ptr.cast::<LineListNode<V, A>>() }.convert_to_cell_node(),
                CELL_BYTE_NODE_TAG => unsafe{ &mut *ptr.cast::<CellByteNode<V, A>>() }.convert_to_cell_node(),
                _ => unsafe{ unreachable_unchecked() }
            }
        }
    }
}

/// Returns the count of values in the subtrie descending from the node, caching shared subtries
pub(crate) fn val_count_below_root<V: Clone + Send + Sync, A: Allocator>(node: &dyn TrieNode<V, A>) -> usize {
    let mut cache = std::collections::HashMap::new();
    node.node_val_count(&mut cache)
}

pub(crate) fn val_count_below_node<V: Clone + Send + Sync, A: Allocator>(node: &TrieNodeODRc<V, A>, cache: &mut HashMap<*const dyn TrieNode<V, A>, usize>) -> usize {
    if node.refcount() > 1 {
        let ptr = node.as_ptr();
        match cache.get(&ptr) {
            Some(cached) => *cached,
            None => {
                let val = node.borrow().node_val_count(cache);
                cache.insert(ptr, val);
                val
            },
        }
    } else {
        node.borrow().node_val_count(cache)
    }
}

/// Internal function to walk a mut TrieNodeODRc<V> ref along a path
///
/// If `stop_early` is `true`, this function will return the parent node of the path and will never return
/// a zero-length continuation path.  If `stop_early` is `false`, the returned continuation path may be
/// zero-length and the returned node will represent as much of the path as is possible.
#[inline]
pub(crate) fn node_along_path_mut<'a, 'k, V: Clone + Send + Sync, A: Allocator>(start_node: &'a mut TrieNodeODRc<V, A>, path: &'k [u8], stop_early: bool) -> (&'k [u8], &'a mut TrieNodeODRc<V, A>) {
    let mut key = path;
    let mut node = start_node;

    //Step until we get to the end of the key or find a leaf node
    let mut node_ptr: *mut TrieNodeODRc<V, A> = node; //Work-around for lack of polonius
    if key.len() > 0 {
        while let Some((consumed_byte_cnt, next_node)) = node.make_mut().node_get_child_mut(key) {
            if consumed_byte_cnt < key.len() || !stop_early {
                node = next_node;
                node_ptr = node;
                key = &key[consumed_byte_cnt..];
                if key.len() == 0 {
                    break;
                }
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

/// Ensures the node is a CellByteNode
///
/// Returns `true` if the node was upgraded and `false` if it already was a CellByteNode
pub(crate) fn make_cell_node<V: Clone + Send + Sync, A: Allocator>(node: &mut TrieNodeODRc<V, A>) -> bool {
    if !node.as_tagged().is_cell_node() {
        let replacement = node.make_mut().convert_to_cell_node();
        *node = replacement;
        true
    } else {
        false
    }
}

//TODO: Make a Macro to generate OpaqueDynBoxes and ODRc (OpaqueDynRc) and an Arc version
//NOTE for future separation into stand-alone crate: The `pub(crate)` visibility inside the `opaque_dyn_rc_trie_node`
//  module come from the visibility of the trait it is derived on.  In this case, `TrieNode`
//Credit to QuineDot for his ideas on this pattern here: https://users.rust-lang.org/t/inferred-lifetime-for-dyn-trait/112116/7
pub(crate) use opaque_dyn_rc_trie_node::TrieNodeODRc;
#[cfg(not(feature = "slim_ptrs"))]
mod opaque_dyn_rc_trie_node {
    use std::sync::Arc;
    use super::TrieNode;
    use crate::Allocator;
    use super::TaggedNodeRef;

    //TODO_FUTURE: make a type alias within the trait to refer to this type, as soon as
    // https://github.com/rust-lang/rust/issues/29661 is addressed

    #[cfg(feature = "nightly")]
    #[derive(Clone)]
    #[repr(transparent)]
    pub struct TrieNodeODRc<V, A: Allocator>(Arc<dyn TrieNode<V, A> + 'static, A>);

    #[cfg(not(feature = "nightly"))]
    #[derive(Clone)]
    #[repr(transparent)]
    pub struct TrieNodeODRc<V, A: Allocator>(Arc<dyn TrieNode<V, A> + 'static>);

    impl<V: Clone + Send + Sync, A: Allocator> TrieNodeODRc<V, A> {
        #[inline]
        pub(crate) fn new_in<'odb, T>(obj: T, alloc: A) -> Self
            where T: 'odb + TrieNode<V, A>,
            V: 'odb
        {
            #[cfg(not(feature = "nightly"))]
            let inner: Arc<dyn TrieNode<V, A>> = {
                let _ = alloc;
                Arc::new(obj)
            };
            #[cfg(feature = "nightly")]
            let inner: Arc<dyn TrieNode<V, A>, A> = Arc::new_in(obj, alloc);

            //SAFETY NOTE: The key to making this abstraction safe is the bound on this method,
            // such that it's impossible to create this wrapper around a concrete type unless the
            // same lifetime can bound both the trait's type parameter and the type itself
            unsafe { Self(core::mem::transmute(inner)) }
        }
        /// Creates a new `TrieNodeODRc` that references a node that exists in memory (ie. not a sentinel for EmptyNode),
        /// but contains no values or onward links
        ///
        /// This method is needed because it's impossible to get a mutable reference to the EmptyNode, but WriteZippers
        /// carry a mutable reference ato the node at their root
        pub(crate) fn new_allocated_in(_child_cnt_capacity: usize, _val_cnt_capacity: usize, alloc: A) -> Self {
            let new_node = crate::line_list_node::LineListNode::new_in(alloc.clone());
            Self::new_in(new_node, alloc)
        }
        //GOAT, Seems like we don't use this impl anymore
        // #[cfg(feature = "nightly")]
        // #[inline]
        // pub(crate) fn new_from_arc<'odb>(arc: Arc<dyn TrieNode<V, A> + 'odb, A>) -> Self
        //     where V: 'odb
        // {
        //     let inner = arc as Arc<dyn TrieNode<V, A>, A>;
        //     //SAFETY NOTE: The key to making this abstraction safe is the bound on this method,
        //     // such that it's impossible to create this wrapper around a concrete type unless the
        //     // same lifetime can bound both the trait's type parameter and the type itself
        //     unsafe { Self(core::mem::transmute(inner)) }
        // }
        //GOAT, Seems like we don't use this impl anymore
        // #[cfg(not(feature = "nightly"))]
        // #[inline]
        // pub(crate) fn new_from_arc<'odb>(arc: Arc<dyn TrieNode<V, A> + 'odb>) -> Self
        //     where V: 'odb
        // {
        //     let inner = arc as Arc<dyn TrieNode<V, A>>;
        //     //SAFETY NOTE: The key to making this abstraction safe is the bound on this method,
        //     // such that it's impossible to create this wrapper around a concrete type unless the
        //     // same lifetime can bound both the trait's type parameter and the type itself
        //     unsafe { Self(core::mem::transmute(inner)) }
        // }
        #[inline]
        pub(crate) fn refcount(&self) -> usize {
            Arc::strong_count(&self.0)
        }
        #[cfg(not(feature = "nightly"))]
        #[inline]
        pub(crate) fn as_arc(&self) -> &Arc<dyn TrieNode<V, A>> {
            &self.0
        }
        #[cfg(feature = "nightly")]
        #[inline]
        pub(crate) fn as_arc(&self) -> &Arc<dyn TrieNode<V, A>, A> {
            &self.0
        }
        #[inline]
        pub(crate) fn as_tagged(&self) -> TaggedNodeRef<'_, V, A> {
            self.borrow().as_tagged()
        }
        #[inline]
        pub(crate) fn borrow(&self) -> &dyn TrieNode<V, A> {
            &*self.0
        }
        #[inline]
        pub(crate) fn as_ptr(&self) -> *const dyn TrieNode<V, A> {
            Arc::as_ptr(&self.0)
        }
        /// Returns `true` if both internal Rc ptrs point to the same object
        #[inline]
        pub fn ptr_eq(&self, other: &Self) -> bool {
            Arc::ptr_eq(self.as_arc(), other.as_arc())
        }
        //NOTE for future separation into stand-alone crate: Make this contingent on a dyn_clone compile-time feature
        #[inline]
        pub(crate) fn make_mut(&mut self) -> &mut (dyn TrieNode<V, A> + 'static) {
            #[cfg(not(feature = "nightly"))]
            let node = dyn_clone::arc_make_mut(&mut self.0) as &mut dyn TrieNode<V, A>;
            #[cfg(feature = "nightly")]
            let node = odrc_arc_make_mut(self) as &mut dyn TrieNode<V, A>;
            node
        }
    }

    /// Code adapted from https://docs.rs/dyn-clone/latest/src/dyn_clone/lib.rs.html#154-177
    /// Modified to use a custom allocator.  Used under the terms of the MIT license
    #[cfg(feature = "nightly")]
    #[inline]
    fn odrc_arc_make_mut<V: Clone + Send + Sync, A: Allocator>(arc: &mut TrieNodeODRc<V, A>) -> &mut (dyn TrieNode<V, A> + 'static) {
        let is_unique = Arc::get_mut(&mut arc.0).is_some();
        if !is_unique {
            let clone = arc.borrow().clone_self();
            *arc = clone;
        }
        // Non-atomic. TODO: replace with Arc::get_mut_unchecked when stable.
        let ptr = Arc::as_ptr(&mut arc.0) as *mut (dyn TrieNode<V, A> + 'static);
        unsafe { &mut *ptr }
    }

    impl<V, A: Allocator> core::fmt::Debug for TrieNodeODRc<V, A>
        where for<'a> &'a dyn TrieNode<V, A>: core::fmt::Debug
    {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            core::fmt::Debug::fmt(&self.0, f)
        }
    }

    //GOAT, dead code.  Impossible to implement Default if allocator must be provided
    // //NOTE for future separation into stand-alone crate: Make this impl contingent on a "DefaultT" argument to the macro
    // //NOTE2, in the general case, we may also want a DefaultT that is parameterized with a type, e.g. `DefaultT<V>`
    // type DefaultT = super::EmptyNode;
    // impl<V: Clone + Send + Sync, A: Allocator> Default for TrieNodeODRc<V, A> where DefaultT: Default + TrieNode<V, A> {
    //     fn default() -> Self {
    //         Self::new(DefaultT::default())
    //     }
    // }

    //GOAT, this might be nice to have in a stand alone crate for the ODRc pattern, but it's doing nothing for us inside pathmap
    // impl<'odb, V: Clone + Send + Sync, A: Allocator> From<Arc<dyn TrieNode<V, A> + 'odb>> for TrieNodeODRc<V, A>
    //     where V: 'odb
    // {
    //     fn from(arc: Arc<dyn TrieNode<V, A> + 'odb>) -> Self {
    //         Self::new_from_arc(arc)
    //     }
    // }
}

/// Interesting Reading:
/// https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html
/// https://github.com/irrustible/ointers/blob/main/src/lib.rs
#[cfg(feature = "slim_ptrs")]
mod slim_node_ptr {
    use core::marker::PhantomData;
    use core::ptr::NonNull;
    use core::sync::atomic::AtomicU32;
    use crate::Allocator;
    use super::{TaggedNodeRef, TrieNode};

    #[cfg(all(not(target_pointer_width="64")))]
    compile_error!("slim_ptrs is only compatible with 64-bit architectures");

    #[repr(align(8))]
    pub(super) struct SlimNodePtr<V: Clone + Send + Sync, A: Allocator> {
        ptr: NonNull<AtomicU32>,
        phantom: PhantomData<(V, A)>,
    }

    unsafe impl<V: Clone + Send + Sync, A: Allocator> Send for SlimNodePtr<V, A> {}
    unsafe impl<V: Clone + Send + Sync, A: Allocator> Sync for SlimNodePtr<V, A> {}

    impl<V: Clone + Send + Sync, A: Allocator> Clone for SlimNodePtr<V, A> {
        #[inline]
        fn clone(&self) -> Self {
            Self{
                ptr: self.ptr,
                phantom: PhantomData,
            }
        }
    }
    impl<V: Clone + Send + Sync, A: Allocator> Copy for SlimNodePtr<V, A> {}

    impl<V, A: Allocator> core::fmt::Debug for SlimNodePtr<V, A>
    where
    for<'a> &'a dyn TrieNode<V, A>: core::fmt::Debug,
    V: Clone + Send + Sync
    {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            core::fmt::Debug::fmt(&self.borrow(), f)
        }
    }

    impl<V: Clone + Send + Sync, A: Allocator> SlimNodePtr<V, A> {
        #[inline]
        pub(crate) fn get_raw_parts(&self) -> (*mut AtomicU32, usize) {
            let tag = (self.ptr.addr().get() >> 59) & 0xF;
            let unpacked_ptr = unpack(self.ptr.as_ptr(), 0, false, 7);
            (unpacked_ptr, tag)
        }
        #[inline]
        pub(super) fn from_raw_parts<T>(ptr: *mut T, tag: usize) -> Self {
            let packed_addr = pack(ptr, 0, false, 7).addr() | (tag << 59);
            let packed_ptr = ptr.with_addr(packed_addr);
            Self{
                ptr: unsafe{ NonNull::new_unchecked(packed_ptr.cast()) },
                phantom: PhantomData,
            }
        }
        //GOAT, next we can try to get rid of the TaggedNodeRef too, although TaggedNodeRef
        // has a lifetime bound and doesn't count borrows, so it's a different type.  But maybe
        // they could both be based on the same tagged 64bit pointer
        #[inline]
        pub(crate) fn as_tagged(&self) -> TaggedNodeRef<'_, V, A> {
            TaggedNodeRef::from_slim_ptr(*self)
        }
        #[inline]
        pub(crate) fn borrow(&self) -> &dyn TrieNode<V, A> {
            self.as_tagged().into_dyn()
        }
        #[inline]
        pub(crate) fn as_ptr(&self) -> *const dyn TrieNode<V, A> {
            let dyn_ref = self.as_tagged().into_dyn();
            unsafe{ core::mem::transmute(dyn_ref) }
        }
        /// Returns `true` if both internal Rc ptrs point to the same object
        #[inline]
        pub fn ptr_eq(&self, other: &Self) -> bool {
            self.ptr == other.ptr
        }
    }

    /// From [ointers](https://github.com/irrustible/ointers) crate, used under terms of Apache-2 license
    /// Produces a mask where the stolen bits (at the top) are set
    const fn mask(bits: u8) -> usize { (isize::MIN >> (max(bits as usize,1) - 1)) as usize }

    pub const fn asv_mask(a: u8, s: bool, v: u8) -> usize { mask(a + s as u8 + v) }

    // core::cmp::max and usize::max aren't const fns
    const fn max(x: usize, y: usize) -> usize {
        if x <= y { y } else { x }
    }

    /// Packs a pointer into the bottom `sizeof(usize) - (a + s + v)` bits
    ///
    /// A: number of bits to steal based on the alignment requirements of T.
    /// S: whether to steal the sign bit.
    /// V: number of bits to steal from unused virtual address space.
    ///
    /// # Safety
    ///
    /// * T's alignment must enable stealing A bits.
    /// * The high bits (sign upwards) must match a stack pointer's high bits.
    /// * If compiling for a 64bit arch, V must be at most 25.
    /// * If compiling for a non-64bit arch, V must be 0.
    #[inline]
    fn pack<T: Sized>(ptr: *mut T, a: u8, s: bool, v: u8) -> *mut T {
        let sv = asv_mask(0, s, v);
        #[cfg(debug_assertions)]
        {
            debug_assert!((1 << a) <= align_of::<T>()); //Eventually it will be enough if pointers are page-aligned
            debug_assert!(v <= 25);
            // If S is set, the user has indicated they will never be
            // dealing with foreign pointers, so we can check that
            // too. We need only really check the sign bit because of
            // canonicalisation, but it's actually cheaper to check
            // all the high bits.
            if s {
                // We don't want to take account of A yet as the pointer
                // is still in its undoctored state.
                let ptr = ptr.addr();
                let stack = (&ptr as *const usize).addr();
                // the top bits should match
                debug_assert!((sv & ptr) == (sv & stack));
            }
        }
        ptr.with_addr((ptr.addr() & !sv) >> a as usize)
    }

    /// Turns the `sizeof(usize) - (a + s + v)` bits of a usize (as returned from `pack`) back into a pointer
    ///
    /// # Safety
    ///
    /// The pointer must be of the correct type, otherwise you're basically unsafely casting the pointer.
    ///
    /// You must use the same settings as you packed the pointer with. The pointer must be packed into the lower bits
    fn unpack<T: Sized>(packed: *mut T, a: u8, s: bool, v: u8) -> *mut T {
        // Mask off all the stolen bits to get the pointer data.
        let asv = asv_mask(a, s, v);
        let masked = packed.addr() & !asv;
        // Restore the empty alignment bits
        let base = masked << a;
        if s {
            // Copy the top bits of a stack pointer
            let sv = asv_mask(0, s, v);
            let base = base & !sv;
            let stack = (&base as *const usize).addr() & sv;
            packed.with_addr(stack | base)
        } else {
            // We need to extend the sign bit.
            packed.with_addr((((base << v as usize) as isize) >> v as usize) as usize)
        }
    }
}

#[cfg(feature = "slim_ptrs")]
mod opaque_dyn_rc_trie_node {
    use core::sync::atomic::{AtomicU32, Ordering::Acquire, Ordering::Relaxed, Ordering::Release};
    use crate::Allocator;
    use crate::dense_byte_node::{DenseByteNode, CellByteNode};
    use crate::line_list_node::LineListNode;
    use super::slim_node_ptr::SlimNodePtr;

    use super::{TaggedNodeRef, TaggedNodeRefMut, TrieNode, EMPTY_NODE_TAG, DENSE_BYTE_NODE_TAG, LINE_LIST_NODE_TAG, CELL_BYTE_NODE_TAG};

    /// TrieNodeODRc = TrieNode Opaque Dynamic RefCounting Pointer
    ///
    /// The `TrieNodeODRc` type is a wrapper around a [SlimNodePtr], however, `SlimNodePtr` does not
    ///  adjust refcounts while `TrieNodeODRc` does.
    pub struct TrieNodeODRc<V: Clone + Send + Sync, A: Allocator> {
        ptr: SlimNodePtr<V, A>,
        alloc: A
    }

    impl<V: Clone + Send + Sync, A: Allocator> Clone for TrieNodeODRc<V, A> {
        /// Increases the node refcount.  See the implementation of Arc::clone in the stdlib
        #[inline]
        fn clone(&self) -> Self {
            //NOTE: This explanation copied verbatim from the Arc implementation in stdlib
            // -------------------------------------------------------------------------------
            // Using a relaxed ordering is alright here, as knowledge of the
            // original reference prevents other threads from erroneously deleting
            // the object.
            //
            // As explained in the [Boost documentation][1], Increasing the
            // reference counter can always be done with memory_order_relaxed: New
            // references to an object can only be formed from an existing
            // reference, and passing an existing reference from one thread to
            // another must already provide any required synchronization.
            //
            // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
            let (ptr, _tag) = self.ptr.get_raw_parts();
            let _old_size = unsafe{ &*ptr }.fetch_add(1, Relaxed);

            Self{ ptr: self.ptr.clone(), alloc: self.alloc.clone() }
        }
    }

    /// We want to saturate at this refcount.  So if we ever see this value, we stop decrementing
    const MAX_REFCOUNT: u32 = 0x7FFFFFFF;

    impl<V: Clone + Send + Sync, A: Allocator> Drop for TrieNodeODRc<V, A> {
        /// Decrements the refcount, and deletes the node if the refcount reaches 0
        #[inline]
        fn drop(&mut self) {
            let (ptr, tag) = self.ptr.get_raw_parts();
            if tag == EMPTY_NODE_TAG {
                return
            }

            //NOTE: This explanation copied verbatim from the Arc implementation in stdlib
            // -------------------------------------------------------------------------------

            // Because `fetch_sub` is already atomic, we do not need to synchronize
            // with other threads unless we are going to delete the object. This
            // same logic applies to the below `fetch_sub` to the `weak` count.
            if unsafe{ &*ptr }.fetch_sub(1, Release) != 1 {
                return;
            }

//GOAT, deal with saturation
            // This fence is needed to prevent reordering of use of the data and
            // deletion of the data. Because it is marked `Release`, the decreasing
            // of the reference count synchronizes with this `Acquire` fence. This
            // means that use of the data happens before decreasing the reference
            // count, which happens before this fence, which happens before the
            // deletion of the data.
            //
            // As explained in the [Boost documentation][1],
            //
            // > It is important to enforce any possible access to the object in one
            // > thread (through an existing reference) to *happen before* deleting
            // > the object in a different thread. This is achieved by a "release"
            // > operation after dropping a reference (any access to the object
            // > through this reference must obviously happened before), and an
            // > "acquire" operation before deleting the object.
            //
            // In particular, while the contents of an Arc are usually immutable, it's
            // possible to have interior writes to something like a Mutex<T>. Since a
            // Mutex is not acquired when it is deleted, we can't rely on its
            // synchronization logic to make writes in thread A visible to a destructor
            // running in thread B.
            //
            // Also note that the Acquire fence here could probably be replaced with an
            // Acquire load, which could improve performance in highly-contended
            // situations. See [2].
            //
            // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
            // [2]: (https://github.com/rust-lang/rust/pull/41714)

            //The fence from Arc is overkill here, so we'll go with an Acquire load
            //Code from Arc with macro expanded: fence(Acquire);
            let refcount = unsafe{ &*ptr }.load(Acquire);
            debug_assert_eq!(refcount, 0);

            drop_inner_in::<V, A>(ptr, tag, self.alloc.clone());
        }
    }

    #[cfg(feature = "nightly")]
    #[inline]
    fn drop_inner_in<V: Clone + Send + Sync, A: Allocator>(ptr: *mut AtomicU32, tag: usize, alloc: A) {
        //Convert the pointer back into a box, so it will drop
        match tag {
            EMPTY_NODE_TAG => {},
            DENSE_BYTE_NODE_TAG => unsafe { let _ = Box::<DenseByteNode<V, A>, A>::from_raw_in(ptr.cast(), alloc); },
            LINE_LIST_NODE_TAG => unsafe { let _ = Box::<LineListNode<V, A>, A>::from_raw_in(ptr.cast(), alloc); },
            CELL_BYTE_NODE_TAG => unsafe { let _ = Box::<CellByteNode<V, A>, A>::from_raw_in(ptr.cast(), alloc); },
            _ => unsafe{ core::hint::unreachable_unchecked() }
        };
    }

    #[cfg(not(feature = "nightly"))]
    #[inline]
    fn drop_inner_in<V: Clone + Send + Sync, A: Allocator>(ptr: *mut AtomicU32, tag: usize, _alloc: A) {
        //Convert the pointer back into a box, so it will drop
        match tag {
            EMPTY_NODE_TAG => {},
            DENSE_BYTE_NODE_TAG => unsafe { let _ = Box::<DenseByteNode<V, A>>::from_raw(ptr.cast()); },
            LINE_LIST_NODE_TAG => unsafe { let _ = Box::<LineListNode<V, A>>::from_raw(ptr.cast()); },
            CELL_BYTE_NODE_TAG => unsafe { let _ = Box::<CellByteNode<V, A>>::from_raw(ptr.cast()); },
            _ => unsafe{ core::hint::unreachable_unchecked() }
        };
    }

    impl<V, A: Allocator> core::fmt::Debug for TrieNodeODRc<V, A>
    where
    for<'a> &'a dyn TrieNode<V, A>: core::fmt::Debug,
    V: Clone + Send + Sync
    {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            core::fmt::Debug::fmt(&self.ptr, f)
        }
    }

    impl<V: Clone + Send + Sync, A: Allocator> TrieNodeODRc<V, A> {
        #[inline]
        pub(crate) fn new_in<'odb, T>(node: T, alloc: A) -> Self
        where
        T: 'odb + TrieNode<V, A>,
        V: 'odb
        {
            let tag = node.tag() as usize;
            #[cfg(not(feature = "nightly"))]
            let boxed = {
                let _ = alloc;
                Box::into_raw(Box::new(node))
            };
            #[cfg(feature = "nightly")]
            let boxed = Box::into_raw(Box::new_in(node, alloc.clone()));
            Self{ ptr: SlimNodePtr::from_raw_parts(boxed, tag), alloc }
        }
        /// Creates a new `TrieNodeODRc` that references a node that exists in memory (ie. not a sentinel for EmptyNode),
        /// but contains no values or onward links
        ///
        /// This method is needed because it's impossible to get a mutable reference to the EmptyNode, but WriteZippers
        /// carry a mutable reference ato the node at their root
        #[inline]
        pub(crate) fn new_allocated_in(_child_cnt_capacity: usize, _val_cnt_capacity: usize, alloc: A) -> Self {
            let new_node = crate::line_list_node::LineListNode::new_in(alloc.clone());
            Self::new_in(new_node, alloc)
        }
        #[inline]
        pub(crate) fn as_tagged(&self) -> TaggedNodeRef<'_, V, A> {
            self.ptr.as_tagged()
        }
        #[inline]
        pub(crate) fn borrow(&self) -> &dyn TrieNode<V, A> {
            self.ptr.borrow()
        }
        #[inline]
        pub(crate) fn as_ptr(&self) -> *const dyn TrieNode<V, A> {
            self.ptr.as_ptr()
        }
        /// Returns `true` if both internal Rc ptrs point to the same object
        #[inline]
        pub fn ptr_eq(&self, other: &Self) -> bool {
            self.ptr.ptr_eq(&other.ptr)
        }
        #[inline]
        pub(crate) fn refcount(&self) -> usize {
            let (ptr, _tag) = self.ptr.get_raw_parts();
            unsafe{ &*ptr }.load(Acquire) as usize
        }
        #[inline]
        pub(crate) fn make_mut(&mut self) -> TaggedNodeRefMut<'_, V, A> {
            let (ptr, _tag) = self.ptr.get_raw_parts();

            if unsafe{ &*ptr }.compare_exchange(1, 0, Acquire, Relaxed).is_err() {
                // Another pointer exists, so we must clone.
                let cloned_node = self.borrow().clone_self();

                //The decrement of the old `self` refcount will happen at this assignment
                *self = cloned_node;

            } else {
                // We were the sole reference so bump back up the  ref count.
                unsafe{ &*ptr }.store(1, Release);
            }

            // We are now clear to copy the inner pointer because our reference was either unique
            // to begin with, or became unique upon cloning the contents.
            TaggedNodeRefMut::from_slim_ptr(self.ptr)
        }
    }
}

//NOTE: This resembles the Lattice trait impl, but we want to return option instead of allocating a
// an empty node to return a reference to
impl<V: Lattice + Clone + Send + Sync, A: Allocator> TrieNodeODRc<V, A> {
    #[inline]
    pub fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        if self.ptr_eq(other) {
            AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT)
        } else {
            self.borrow().pjoin_dyn(other.borrow())
            //GOAT, question: Is there any point to this pre-check, or is it enough to just let pjoin_dyn handle it?
            // let node = self.borrow();
            // let other_node = other.borrow();
            // match (node.node_is_empty(), other_node.node_is_empty()) {
            //     (false, false) => node.pjoin_dyn(other_node),
            //     (false, true) => AlgebraicResult::Identity(SELF_IDENT),
            //     (true, false) => AlgebraicResult::Identity(COUNTER_IDENT),
            //     (true, true) => AlgebraicResult::None,
            // }
        }
    }
    #[inline]
    pub fn join_into(&mut self, node: TrieNodeODRc<V, A>) -> AlgebraicStatus {
        let (status, result) = self.make_mut().join_into_dyn(node);
        match result {
            Ok(()) => {},
            Err(replacement_node) => {
                *self = replacement_node;
            }
        }
        status
    }
    #[inline]
    pub fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        if self.ptr_eq(other) {
            AlgebraicResult::Identity(SELF_IDENT | COUNTER_IDENT)
        } else {
            self.borrow().pmeet_dyn(other.borrow())
        }
    }
}

//See above, pseudo-impl for [DistributiveLattice] trait
impl<V: DistributiveLattice + Clone + Send + Sync, A: Allocator> TrieNodeODRc<V, A> {
    pub fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> {
        if self.ptr_eq(other) {
            AlgebraicResult::None
        } else {
            self.borrow().psubtract_dyn(other.borrow())
        }
    }
}

impl <V: Clone + Send + Sync, A: Allocator> Quantale for TrieNodeODRc<V, A> {
    fn prestrict(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        self.borrow().prestrict_dyn(other.borrow())
    }
}

impl<V: Lattice + Clone + Send + Sync, A: Allocator> Lattice for Option<TrieNodeODRc<V, A>> {
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        match self {
            None => match other {
                None => { AlgebraicResult::None }
                Some(_) => { AlgebraicResult::Identity(COUNTER_IDENT) }
            },
            Some(l) => match other {
                None => { AlgebraicResult::Identity(SELF_IDENT) }
                Some(r) => { l.pjoin(r).map(|result| Some(result)) }
            }
        }
    }
    // GOAT, maybe the default impl is fine... Or maybe not... I need to think through whether any efficiency
    // is left on the table
    // fn join_into(&mut self, other: Self) {
    //     match self {
    //         None => { match other {
    //             None => { }
    //             Some(r) => { *self = Some(r) }
    //         } }
    //         Some(l) => match other {
    //             None => { }
    //             Some(r) => { l.join_into(r) }
    //         }
    //     }
    // }
    fn pmeet(&self, other: &Option<TrieNodeODRc<V, A>>) -> AlgebraicResult<Option<TrieNodeODRc<V, A>>> {
        match self {
            None => { AlgebraicResult::None }
            Some(l) => {
                match other {
                    None => { AlgebraicResult::None }
                    Some(r) => l.pmeet(r).map(|result| Some(result))
                }
            }
        }
    }
    //GOAT trash
    // fn bottom() -> Self {
    //     None
    // }
}

impl<V: Lattice + Clone + Send + Sync, A: Allocator> LatticeRef for Option<&TrieNodeODRc<V, A>> {
    type T = Option<TrieNodeODRc<V, A>>;
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self::T> {
        match self {
            None => match other {
                None => { AlgebraicResult::None }
                Some(_) => { AlgebraicResult::Identity(COUNTER_IDENT) }
            },
            Some(l) => match other {
                None => { AlgebraicResult::Identity(SELF_IDENT) }
                Some(r) => { l.pjoin(r).map(|result| Some(result)) }
            }
        }
    }
    fn pmeet(&self, other: &Option<&TrieNodeODRc<V, A>>) -> AlgebraicResult<Option<TrieNodeODRc<V, A>>> {
        match self {
            None => { AlgebraicResult::None }
            Some(l) => {
                match other {
                    None => { AlgebraicResult::None }
                    Some(r) => l.pmeet(r).map(|result| Some(result))
                }
            }
        }
    }
}

impl<V: DistributiveLattice + Clone + Send + Sync, A: Allocator> DistributiveLattice for Option<TrieNodeODRc<V, A>> {
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> {
        match self {
            None => { AlgebraicResult::None }
            Some(s) => {
                match other {
                    None => { AlgebraicResult::Identity(SELF_IDENT) }
                    Some(o) => { s.psubtract(o).map(|v| Some(v)) }
                }
            }
        }
    }
}

impl<V: DistributiveLattice + Clone + Send + Sync, A: Allocator> DistributiveLatticeRef for Option<&TrieNodeODRc<V, A>> {
    type T = Option<TrieNodeODRc<V, A>>;
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self::T> {
        match self {
            None => { AlgebraicResult::None }
            Some(s) => {
                match other {
                    None => { AlgebraicResult::Identity(SELF_IDENT) }
                    Some(o) => { s.psubtract(o).map(|v| Some(v)) }
                }
            }
        }
    }
}
