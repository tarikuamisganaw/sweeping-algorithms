
use dyn_clone::*;

use crate::dense_byte_node::*;
use crate::line_list_node::LineListNode;
use crate::empty_node::EmptyNode;
use crate::ring::*;


pub(crate) trait TrieNode<V>: DynClone {

    // /// Returns `true` if the node contains a child node for the key path, otherwise returns `false`
    //GOAT what would you do with a child node except for traverse it?
    // fn node_contains_child(&self, key: &[u8]) -> bool;

    /// Returns `true` if the node contains a key that begins with `key`, irrespective of whether the key
    /// specifies a child, value, or both
    fn node_contains_partial_key(&self, key: &[u8]) -> bool;

    /// Returns the child node that matches `key` along with the number of `key` characters matched.
    /// Returns `None` if no child node matches the key, even if there is a value with that prefix
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)>;

    /// Same behavior as `node_get_child`, but operates across a mutable reference
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut dyn TrieNode<V>)>;

    /// Replaces a child-node at `key` with the node provided, returning a `&mut` reference to the newly
    /// added child node
    ///
    /// Unlike [node_get_child], this method requires an exact key and not just a prefix, in order to
    /// maintain tree integrity.  This method is not intended as a general-purpose "set" operation, and
    /// may panic if the node does not already contain a child node at the specified key.
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
    fn node_get_val(&self, key: &[u8]) -> Option<&V>;

    /// Mutable version of [node_get_val]
    fn node_get_val_mut(&mut self, key: &[u8]) -> Option<&mut V>;

    /// Sets the value specified by `key` to the object V.  Returns Ok(None) if a new value was added,
    /// returns Ok(Some(v)) with the old value if the value was replaced
    ///
    /// If this method returns Err(node), then the node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    fn node_set_val(&mut self, key: &[u8], val: V) -> Result<Option<V>, TrieNodeODRc<V>>;

    /// Returns a mutable reference to the value, creating it using `default_f` if it doesn't already
    /// exist
    ///
    /// If this method returns Err(node), then the node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    /// Then the new node may be re-borrowed.
    //GOAT, consider a boxless version of this that takes a regular &dyn Fn() instead of FnOnce
    //Or maybe two versions, one that takes an &dyn Fn, and another that takes a V
    fn node_update_val(&mut self, key: &[u8], default_f: Box<dyn FnOnce()->V + '_>) -> Result<&mut V, TrieNodeODRc<V>>;

    /// Returns `true` if the node contains no children nor values, otherwise false
    fn node_is_empty(&self) -> bool;

    /// Returns a boxed iterator over each item contained within the node, both child nodes and values
    /// GOAT, hopefully we can deprecate this method
    fn boxed_node_iter<'a>(&'a self) -> Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a>;

    /// Returns the total number of leaves contained within the whole subtree defined by the node
    fn node_subtree_len(&self) -> usize;

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

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types.
    fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types.
    fn join_into_dyn(&mut self, other: TrieNodeODRc<V>) where V: Lattice;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types.
    fn meet_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice;

    /// Allows for the implementation of the PartialDistributiveLattice trait on different node
    /// implementations, and the logic to promote nodes to other node types.
    fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: PartialDistributiveLattice;

    /// Returns a reference to the node as a specific concrete type or None if it is not that type
    ///
    /// NOTE: If we end up checking more than one concrete type in the same implementation, it probably
    /// makes sense to define a type enum
    fn as_dense(&self) -> Option<&DenseByteNode<V>>;

    /// Returns a mutable reference to the node as a specific concrete type or None if it is not that type
    fn as_dense_mut(&mut self) -> Option<&mut DenseByteNode<V>>;

    /// Returns a reference to the node as a specific concrete type or None if it is not that type
    fn as_list(&self) -> Option<&LineListNode<V>>;

}

pub(crate) enum ValOrChildRef<'a, V> {
    Val(&'a V),
    Child(&'a dyn TrieNode<V>)
}

#[derive(Clone)]
pub(crate) enum ValOrChild<V> {
    Val(V),
    Child(TrieNodeODRc<V>)
}

//TODO: Make a Macro to generate OpaqueDynBoxes and ODRc (OpaqueDynRc) and an Arc version
pub(crate) use opaque_dyn_rc_trie_node::TrieNodeODRc;
mod opaque_dyn_rc_trie_node{
    use super::TrieNode;

    //TODO_FUTURE: make a type alias within the trait to refer to this type, as soon as
    // https://github.com/rust-lang/rust/issues/29661 is addressed

    #[derive(Clone)]
    #[repr(transparent)]
    pub struct TrieNodeODRc<V>(std::rc::Rc<dyn TrieNode<V> + 'static>);

    impl<V> TrieNodeODRc<V> {
        #[inline]
        pub fn new<'odb, T>(obj: T) -> Self
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
        pub fn new_from_rc<'odb>(rc: std::rc::Rc<dyn TrieNode<V> + 'odb>) -> Self
            where V: 'odb
        {
            let inner = rc as std::rc::Rc<dyn TrieNode<V>>;
            //SAFETY NOTE: The key to making this abstraction safe is the bound on this method,
            // such that it's impossible to create this wrapper around a concrete type unless the
            // same lifetime can bound both the trait's type parameter and the type itself
            unsafe { Self(core::mem::transmute(inner)) }
        }
        #[inline]
        pub fn as_rc(&self) -> &std::rc::Rc<dyn TrieNode<V>> {
            &self.0
        }
        #[inline]
        pub fn borrow(&self) -> &dyn TrieNode<V> {
            &*self.0
        }
        /// Returns `true` if both internal Rc ptrs point to the same object
        #[inline]
        pub fn ptr_eq(&self, other: &Self) -> bool {
            std::rc::Rc::ptr_eq(self.as_rc(), other.as_rc())
        }
        //GOAT, make this contingent on a dyn_clone compile-time feature
        #[inline]
        pub fn make_mut(&mut self) -> &mut dyn TrieNode<V> {
            dyn_clone::rc_make_mut(&mut self.0) as &mut dyn TrieNode<V>
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

impl<V: Lattice + Clone> Lattice for TrieNodeODRc<V> {
    fn join(&self, other: &Self) -> Self {
        if self.ptr_eq(other) {
            self.clone()
        } else {
            self.borrow().join_dyn(other.borrow())
        }
    }
    fn join_into(&mut self, other: Self) {
        if !self.ptr_eq(&other) {
            self.make_mut().join_into_dyn(other)
        }
    }
    fn meet(&self, other: &Self) -> Self {
        if self.ptr_eq(other) {
            self.clone()
        } else {
            self.borrow().meet_dyn(other.borrow())
        }
    }
    fn bottom() -> Self {
        //If we end up hitting this, we should add an "empty node" type that implements TrieNode,
        // but is incapable of holding any values or children
        panic!()
    }
}

impl<V: PartialDistributiveLattice + Clone> PartialDistributiveLattice for TrieNodeODRc<V> {
    fn psubtract(&self, other: &Self) -> Option<Self> {
        if self.ptr_eq(other) {
            None
        } else {
            self.borrow().psubtract_dyn(other.borrow())
        }
    }
}

impl<V: PartialDistributiveLattice + Clone> DistributiveLattice for TrieNodeODRc<V> {
    fn subtract(&self, other: &Self) -> Self {
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
