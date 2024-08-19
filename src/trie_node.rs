
use dyn_clone::*;

use crate::dense_byte_node::*;
use crate::line_list_node::LineListNode;
use crate::empty_node::EmptyNode;
use crate::ring::*;

/// The abstract interface to all nodes, from which tries are built
///
/// TrieNodes are small tries that can be stitched together into larger tries.  Within a TrieNode, value
/// and onward link locations are defined by key paths.  There are a few conventions and caveats to this
/// iterface:
///
/// 1. A TrieNode will never have a value or an onward link at a zero-length key.  A value associated with
/// the path to the root of a TrieNode must be stored in the parent node.
pub trait TrieNode<V>: DynClone + core::fmt::Debug {

    // /// Returns `true` if the node contains a child node for the key path, otherwise returns `false`
    //GOAT what would you do with a child node except for traverse it?
    // fn node_contains_child(&self, key: &[u8]) -> bool;

    /// Returns `true` if the node contains a key that begins with `key`, irrespective of whether the key
    /// specifies a child, value, or both
    ///
    /// This method should never be called with a zero-length key.  If the `key` arg is longer than the
    /// keys contained within the node, this method should return `false`
    fn node_contains_partial_key(&self, key: &[u8]) -> bool;

    /// Returns the child node that matches `key` along with the number of `key` characters matched.
    /// Returns `None` if no child node matches the key, even if there is a value with that prefix
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)>;

    /// Similar behavior to `node_get_child`, but operates across a mutable reference and returns both the 
    /// value and onward link associated with a given path
    ///
    /// Unlike `node_get_child`, if the key matches a value but not an onward link, this method will return
    /// `Some(byte_cnt, Some(val), None)`
    fn node_get_child_and_val_mut<'a>(&'a mut self, key: &[u8]) -> Option<(usize, Option<&'a mut V>, Option<&'a mut TrieNodeODRc<V>>)>;

    //GOAT, I don't think we need this function below since it's used to walk a mutable ref into the tree,
    // but we almost always want a value at the same time, hence node_get_child_and_val_mut
    /// Same behavior as `node_get_child`, but operates across a mutable reference
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>)>;

    /// Replaces a child-node at `key` with the node provided, returning a `&mut` reference to the newly
    /// added child node
    ///
    /// Unlike [node_get_child], this method requires an exact key and not just a prefix, in order to
    /// maintain tree integrity.  This method is not intended as a general-purpose "set" operation, and
    /// may panic if the node does not already contain a child node at the specified key.
    ///
    /// QUESTION: Does this method have a strong purpose, or can it be superseded by node_set_branch?
    fn node_replace_child(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> &mut dyn TrieNode<V>;

    /// Returns `true` if the node contains a value at the specified key, otherwise returns `false`
    ///
    /// NOTE: just as with [Self::node_get_val], this method will return `false` if key is longer than
    /// the exact key contained within this node
    fn node_contains_val(&self, key: &[u8]) -> bool;

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
    fn node_set_val(&mut self, key: &[u8], val: V) -> Result<(Option<V>, bool), TrieNodeODRc<V>>;

    /// Deletes the value specified by `key`
    ///
    /// Returns `Some(val)` with the value that was removed, otherwise returns `None`
    ///
    /// WARNING: This method may leave the node empty
    fn node_remove_val(&mut self, key: &[u8]) -> Option<V>;

    //GOAT-Deprecated-Update  deprecating `update` interface in favor of WriteZipper
    // /// Returns a mutable reference to the value, creating it using `default_f` if it doesn't already
    // /// exist
    // ///
    // /// If this method returns Err(node), then the node was upgraded, and the new node must be
    // /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    // /// Then the new node may be re-borrowed.
    // //GOAT, consider a boxless version of this that takes a regular &dyn Fn() instead of FnOnce
    // //Or maybe two versions, one that takes an &dyn Fn, and another that takes a V
    // fn node_update_val(&mut self, key: &[u8], default_f: Box<dyn FnOnce()->V + '_>) -> Result<&mut V, TrieNodeODRc<V>>;

    /// Sets the downstream branch from the specified `key`.  Does not affect the value at the `key`
    ///
    /// Returns `Ok(sub_node_created)`, which will be `true` if `key` now specifies a different subnode;
    /// and `false` if key still specifies a branch within the node.
    ///
    /// If this method returns Err(node), then the `self` node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    fn node_set_branch(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> Result<bool, TrieNodeODRc<V>>;

    /// Removes the downstream branch from the specified `key`.  Does not affect the value at the `key`
    ///
    /// Returns `true` if a value was sucessfully removed from the node; returns `false` if the node did not
    /// contain a branch at the specified key
    ///
    /// WARNING: This method may leave the node empty.  If eager pruning of branches is desired then the
    /// node should subsequently be checked to see if it is empty
    fn node_remove_branch(&mut self, key: &[u8]) -> bool;

    /// Returns `true` if the node contains no children nor values, otherwise false
    fn node_is_empty(&self) -> bool;

    /// Returns a boxed iterator over each item contained within the node, both child nodes and values
    /// TODO, hopefully we can deprecate this method when the zipper iteration gets a little faster.  See
    /// comments around [crate::trie_map::BytesTrieMapCursor]
    fn boxed_node_iter<'a>(&'a self) -> Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a>;

    /// Returns the total number of leaves contained within the whole subtree defined by the node
    fn node_subtree_len(&self) -> usize;

    #[cfg(feature = "counters")]
    /// Returns the number of internal paths within the node.  That includes child nodes descending from
    /// the node as well as values; in the case where a child node and a value have the same internal path
    /// it will be counted as one item
    fn item_count(&self) -> usize;

//GOAT this looks like trash
    // /// Returns the next key within the node that contains a value and/or a branch, from the 
    // /// supplied key.  The iteration order is unspecified and implementation-dependent.  However,
    // /// 
    // /// 
    // ///  according to an iteration
    // /// order that is internal to the node.  The constraints of the iteration order are that:
    // /// 1. Each key containing a value or branch must be visited exactly once
    // /// 2. For a given node, the order must not change 
    // //GOAT!!!! This won't work because the internal branching structure of the node matters because
    // // iteration might start in the middle of the node!!!!
    // fn next_within_node<'a>(&'a self, key: &[u8], key_or_val: bool) -> (&'a[u8], ValOrChildRef<'a, V>);

    /// Returns the nth child in the branch specified by `key` within this node, as the prefix leading to
    /// that child and optionally a new node
    ///
    /// This method returns (None, _) if `n >= self.child_count()`.
    /// This method returns (Some(_), None) if the child is is contained within the same node.
    /// This method returns (Some(_), Some(_)) if the child is is contained within a different node.
    ///
    /// NOTE: onward paths that lead to values are still part of the enumeration
    /// NOTE: Unlike some other trait methods, method may be called with a zero-length key
    fn nth_child_from_key(&self, key: &[u8], n: usize) -> (Option<u8>, Option<&dyn TrieNode<V>>);

    /// Behaves similarly to [Self::nth_child_from_key(0)] with the difference being that the returned
    /// prefix should be an entire path to the onward link or to the next branch
    fn first_child_from_key(&self, key: &[u8]) -> (Option<&[u8]>, Option<&dyn TrieNode<V>>);

    /// Returns the number of onward (child) paths within a node from a specified key
    ///
    /// If the node doesn't contain the key, this method returns 0.
    /// If the key identifies a value but no onward path within the node, this method returns 0.
    /// If the key identifies a partial path within the node, this method returns 1.
    ///
    /// WARNING: This method does not recurse, so an onward child link's children will not be
    ///   considered.  Therefore, it is necessary to call this method on the referenced node and
    ///   not the parent.
    /// NOTE: Unlike some other trait methods, method may be called with a zero-length key
    fn child_count_at_key(&self, key: &[u8]) -> usize;

    /// Returns 256-bit mask, indicating which children exist from the branch specified by `key`
    fn child_mask_at_key(&self, key: &[u8]) -> [u64; 4];

    /// Returns `true` if the key specifies a leaf within the node from which it is impossible to
    /// descend further, otherwise returns `false`
    ///
    /// NOTE: Returns `true` if the key specifies an invalid path, because an invalid path has no
    ///   onward paths branching from it.
    /// NOTE: The reason this is not the same as `node.child_count_at_key() == 0` is because [Self::child_count_at_key]
    ///   counts only internal children, and treats values and onward links equivalently.  Therefore
    ///   some keys that specify onward links will be reported as having a `child_count` of 0, but `is_leaf`
    ///   will be true.
    fn is_leaf(&self, key: &[u8]) -> bool;

    /// Returns the key of the prior upstream branch, within the node
    ///
    /// This method will never be called with a zero-length key.
    /// Returns &[] if `key` is descended from the root and therefore has no upstream branch.
    /// Returns &[] if `key` does not exist within the node.
    fn prior_branch_key(&self, key: &[u8]) -> &[u8];

//GOAT, Current thinking is this method (and the upstread functionality enabled by it) are unneeded
// This method itself has a number of conceptual issues - for example, is it the sibling count at the
// nearest upstream fork, or just the nearest upstream byte.  Both implementations come with extra
// complications, and neither provide functionality that isn't nearly as efficient to do another way.
//     /// Returns the number of siblings of a focus specified by a key within a node
//     ///
//     /// This method will never be invoked with a zero-length key
//     /// Returns 0 if the node doesn't contain the key
//     /// 
//     fn sibling_count_at_key(&self, key: &[u8]) -> usize;

    /// Returns the child of this node that is immediately before or after the child identified by `key`
    ///
    /// Returns None if the found child node is already the first or last child, or if `key` does not
    /// identify any contained subnode
    ///
    /// If 'next == true` then the returned child will be immediately after to the node found by
    /// `key`, otherwise it will be immedtely before
    ///
    /// NOTE: This method will never be called with a zero-length key
    fn get_sibling_of_child(&self, key: &[u8], next: bool) -> (Option<u8>, Option<&dyn TrieNode<V>>);

    /// Returns a new node which is a clone or reference to the portion of the node rooted at `key`, or
    /// `None` if `key` does not specify a path within the node
    ///
    /// If `key.len() == 0` this method will return a reference to or a clone of the node.
    fn get_node_at_key(&self, key: &[u8]) -> AbstractNodeRef<V>;

    /// Returns a node which is the the portion of the node rooted at `key`, or `None` if `key` does
    /// not specify a path within the node
    ///
    /// This method should never be called with `key.len() == 0`
    fn take_node_at_key(&mut self, key: &[u8]) -> Option<TrieNodeODRc<V>>;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types
    fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types
    fn join_into_dyn(&mut self, other: TrieNodeODRc<V>) where V: Lattice;

    /// Returns a node composed of the children of `self`, `byte_cnt` bytes downstream, all joined together,
    /// or `None` if the node has no children at that depth
    ///
    /// After this method, `self` will be invalid and/ or empty, and should be replaced with the result.
    ///
    /// QUESTION: Is there a value to a "copying" version of drop_head?  It has higher overheads but could
    /// be safely implemented by the [crate::zipper::ReadZipper].
    fn drop_head_dyn(&mut self, byte_cnt: usize) -> Option<TrieNodeODRc<V>> where V: Lattice;

//GOAT this is trash comments
    /// Replaces the contents of the `self` node with a node composed of the children of `self`,
    /// `byte_cnt` steps downstream, all joined together.
    ///
    /// Returns `Ok(())` if the operation completed sucessfully, or `Err(replacement_node)` if the `self`
    /// node must be replaced with the returned `replacement_node`
    ///
    /// QUESTION: Is there a value to a "copying" version of drop_head?  It has much higher overheads
    /// but could be safely implemented by the [crate::zipper::ReadZipper].


    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types.
    fn meet_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: Lattice;

    /// Allows for the implementation of the PartialDistributiveLattice trait on different node
    /// implementations, and the logic to promote nodes to other node types
    fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: PartialDistributiveLattice;

    /// Allows for the implementation of the PartialDistributiveLattice trait on different node
    /// implementations, and the logic to promote nodes to other node types
    fn prestrict_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: PartialDistributiveLattice;

    /// Returns a reference to the node as a specific concrete type or None if it is not that type
    ///
    /// NOTE: If we end up checking more than one concrete type in the same implementation, it probably
    /// makes sense to define a type enum.
    fn as_dense(&self) -> Option<&DenseByteNode<V>>;

    /// Returns a mutable reference to the node as a specific concrete type, or None if the node is another tyepe
    fn as_dense_mut(&mut self) -> Option<&mut DenseByteNode<V>>;

    /// Returns a reference to the node as a specific concrete type or None if it is not that type
    fn as_list(&self) -> Option<&LineListNode<V>>;

    /// Returns a clone of the node in its own Rc
    fn clone_self(&self) -> TrieNodeODRc<V>;
}

pub enum ValOrChildRef<'a, V> {
    Val(&'a V),
    Child(&'a dyn TrieNode<V>)
}

#[derive(Clone)]
pub(crate) enum ValOrChild<V> {
    Val(V),
    Child(TrieNodeODRc<V>)
}

impl<V> ValOrChild<V> {
    pub fn into_child(self) -> TrieNodeODRc<V> {
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
}

pub enum AbstractNodeRef<'a, V> {
    None,
    BorrowedDyn(&'a dyn TrieNode<V>),
    BorrowedRc(&'a TrieNodeODRc<V>),
    OwnedRc(TrieNodeODRc<V>)
}

impl<'a, V> core::fmt::Debug for AbstractNodeRef<'a, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::None => write!(f, "AbstractNodeRef::None"),
            Self::BorrowedDyn(_) => write!(f, "AbstractNodeRef::BorrowedDyn"),
            Self::BorrowedRc(_) => write!(f, "AbstractNodeRef::BorrowedRc"),
            Self::OwnedRc(_) => write!(f, "AbstractNodeRef::OwnedRc"),
        }
    }
}

impl<'a, V: Clone> AbstractNodeRef<'a, V> {
    pub fn is_none(&self) -> bool {
        matches!(self, AbstractNodeRef::None)
    }
    pub fn borrow(&self) -> &dyn TrieNode<V> {
        match self {
            AbstractNodeRef::None => panic!(),
            AbstractNodeRef::BorrowedDyn(node) => *node,
            AbstractNodeRef::BorrowedRc(rc) => rc.borrow(),
            AbstractNodeRef::OwnedRc(rc) => rc.borrow()
        }
    }
    pub fn borrow_option(&self) -> Option<&dyn TrieNode<V>> {
        match self {
            AbstractNodeRef::None => None,
            AbstractNodeRef::BorrowedDyn(node) => Some(*node),
            AbstractNodeRef::BorrowedRc(rc) => Some(rc.borrow()),
            AbstractNodeRef::OwnedRc(rc) => Some(rc.borrow())
        }
    }
    pub fn into_option(self) -> Option<TrieNodeODRc<V>> {
        match self {
            AbstractNodeRef::None => None,
            AbstractNodeRef::BorrowedDyn(node) => Some(node.clone_self()),
            AbstractNodeRef::BorrowedRc(rc) => Some(rc.clone()),
            AbstractNodeRef::OwnedRc(rc) => Some(rc)
        }
    }
}

//TODO: Make a Macro to generate OpaqueDynBoxes and ODRc (OpaqueDynRc) and an Arc version
//GOAT: the `pub(crate)` visibility inside the `opaque_dyn_rc_trie_node` module come from the visibility of
// the trait it is derived on.  In this case, `TrieNode`
pub(crate) use opaque_dyn_rc_trie_node::TrieNodeODRc;
mod opaque_dyn_rc_trie_node {
    use super::TrieNode;

    //TODO_FUTURE: make a type alias within the trait to refer to this type, as soon as
    // https://github.com/rust-lang/rust/issues/29661 is addressed

    #[derive(Clone, Debug)]
    #[repr(transparent)]
    pub struct TrieNodeODRc<V>(std::rc::Rc<dyn TrieNode<V> + 'static>);

    impl<V> TrieNodeODRc<V> {
        #[inline]
        pub(crate) fn new<'odb, T>(obj: T) -> Self
            where T: 'odb + TrieNode<V>,
            V: 'odb
        {
            let inner = std::rc::Rc::new(obj) as std::rc::Rc<dyn TrieNode<V>>;
            //SAFETY NOTE: The key to making this abstraction safe is the bound on this method,
            // such that it's impossible to create this wrapper around a concrete type unless the
            // same lifetime can bound both the trait's type parameter and the type itself
            unsafe { Self(core::mem::transmute(inner)) }
        }
        #[inline]
        pub(crate) fn new_from_rc<'odb>(rc: std::rc::Rc<dyn TrieNode<V> + 'odb>) -> Self
            where V: 'odb
        {
            let inner = rc as std::rc::Rc<dyn TrieNode<V>>;
            //SAFETY NOTE: The key to making this abstraction safe is the bound on this method,
            // such that it's impossible to create this wrapper around a concrete type unless the
            // same lifetime can bound both the trait's type parameter and the type itself
            unsafe { Self(core::mem::transmute(inner)) }
        }
        #[inline]
        pub(crate) fn as_rc(&self) -> &std::rc::Rc<dyn TrieNode<V>> {
            &self.0
        }
        #[inline]
        pub(crate) fn borrow(&self) -> &dyn TrieNode<V> {
            &*self.0
        }
        /// Returns `true` if both internal Rc ptrs point to the same object
        #[inline]
        pub fn ptr_eq(&self, other: &Self) -> bool {
            std::rc::Rc::ptr_eq(self.as_rc(), other.as_rc())
        }
        //GOAT, make this contingent on a dyn_clone compile-time feature
        #[inline]
        pub(crate) fn make_mut(&mut self) -> &mut dyn TrieNode<V> {
            dyn_clone::rc_make_mut(&mut self.0) as &mut dyn TrieNode<V>
        }
    }

    //GOAT, make this impl contingent on a "DefaultT" argument to the macro
    type DefaultT<V> = super::EmptyNode<V>;
    impl<V> Default for TrieNodeODRc<V> where DefaultT<V>: Default + TrieNode<V> {
        fn default() -> Self {
            Self::new(DefaultT::<V>::default())
        }
    }

    impl<'odb, V> From<std::rc::Rc<dyn TrieNode<V> + 'odb>> for TrieNodeODRc<V>
        where V: 'odb
    {
        fn from(rc: std::rc::Rc<dyn TrieNode<V> + 'odb>) -> Self {
            Self::new_from_rc(rc)
        }
    }
}

//NOTE: This resembles the Lattice trait impl, but we want to return option instead of allocating a
// an empty node to return a reference to
impl<V: Lattice + Clone> TrieNodeODRc<V> {
    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        if self.ptr_eq(other) {
            self.clone()
        } else {
            self.borrow().join_dyn(other.borrow())
        }
    }
    #[inline]
    pub fn join_into(&mut self, other: Self) {
        if !self.ptr_eq(&other) {
            self.make_mut().join_into_dyn(other)
        }
    }
    #[inline]
    pub fn meet(&self, other: &Self) -> Option<Self> {
        if self.ptr_eq(other) {
            Some(self.clone())
        } else {
            self.borrow().meet_dyn(other.borrow())
        }
    }
}

//See above, pseudo-impl for PartialDistributiveLattice trait
impl<V: PartialDistributiveLattice + Clone> TrieNodeODRc<V> {
    pub fn psubtract(&self, other: &Self) -> Option<Self> {
        if self.ptr_eq(other) {
            None
        } else {
            self.borrow().psubtract_dyn(other.borrow())
        }
    }

    pub fn prestrict(&self, other: &Self) -> Option<Self> where Self: Sized {
        self.borrow().prestrict_dyn(other.borrow())
    }
}

//See above, pseudo-impl for DistributiveLattice trait
impl<V: PartialDistributiveLattice + Clone> TrieNodeODRc<V> {
    pub fn subtract(&self, other: &Self) -> Self {
        if self.ptr_eq(other) {
            TrieNodeODRc::new(EmptyNode::new())
        } else {
            match self.borrow().psubtract_dyn(other.borrow()) {
                Some(node) => node,
                None => TrieNodeODRc::new(EmptyNode::new())
            }
        }
    }
}

impl <V : Lattice + Clone> Lattice for Option<TrieNodeODRc<V>> {
    fn join(&self, other: &Option<TrieNodeODRc<V>>) -> Option<TrieNodeODRc<V>> {
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
    /// GOAT, maybe the default impl is fine
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
    fn meet(&self, other: &Option<TrieNodeODRc<V>>) -> Option<TrieNodeODRc<V>> {
        match self {
            None => { None }
            Some(l) => {
                match other {
                    None => { None }
                    Some(r) => l.meet(r)
                }
            }
        }
    }
    fn bottom() -> Self {
        None
    }
}

impl <V : PartialDistributiveLattice + Clone> PartialDistributiveLattice for Option<TrieNodeODRc<V>> {
    fn psubtract(&self, other: &Self) -> Option<Self> {
        match self {
            None => { None }
            Some(s) => { match other {
                None => { Some(Some(s.clone())) }
                Some(o) => { Some(s.psubtract(o)) }
            } }
        }
    }

    fn prestrict(&self, other: &Self) -> Option<Self> where Self: Sized {
        panic!()
    }
}

impl <V : PartialDistributiveLattice + Clone> DistributiveLattice for Option<TrieNodeODRc<V>> {
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
