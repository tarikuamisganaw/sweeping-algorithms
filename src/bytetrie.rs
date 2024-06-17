
use dyn_clone::*;

use crate::dense_byte_node::*;
use crate::ring::*;

pub struct BytesTrieMapIter<'a, V> where V : Clone {
    prefixes: Vec<Vec<u8>>,
    btnis: Vec<Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a>>,
}

impl <'a, V : Clone> BytesTrieMapIter<'a, V> {
    fn new(btm: &'a BytesTrieMap<V>) -> Self {
        Self {
            prefixes: vec![vec![]],
            btnis: vec![btm.root.boxed_node_iter()],
        }
    }
}

impl <'a, V : Clone> Iterator for BytesTrieMapIter<'a, V> {
    type Item = (Vec<u8>, &'a V);

    fn next(&mut self) -> Option<(Vec<u8>, &'a V)> {
        loop {
            match self.btnis.last_mut() {
                None => { return None }
                Some(last) => {
                    match last.next() {
                        None => {
                            self.prefixes.pop();
                            self.btnis.pop();
                        }
                        Some((bytes, item)) => {
                            let mut cur_prefix = self.prefixes.last().unwrap().clone();
                            cur_prefix.extend(bytes);

                            match item {
                                ValOrChildRef::Val(val) => return Some((cur_prefix, val)),
                                ValOrChildRef::Child(child) => {
                                    self.prefixes.push(cur_prefix);
                                    self.btnis.push(child.boxed_node_iter())
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// An iterator-like object that traverses key-value pairs in a [BytesTrieMap], however only one
/// returned reference may exist at a given time
pub struct BytesTrieMapCursor<'a, V> where V : Clone {
    prefix_buf: Vec<u8>,
    prefix_idx: Vec<usize>,
    btnis: Vec<Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a>>,
}

impl <'a, V : Clone> BytesTrieMapCursor<'a, V> {
    fn new(btm: &'a BytesTrieMap<V>) -> Self {
        const EXPECTED_DEPTH: usize = 16;
        let mut prefix_idx = Vec::with_capacity(EXPECTED_DEPTH);
        prefix_idx.push(0);
        let mut btnis = Vec::with_capacity(EXPECTED_DEPTH);
        btnis.push(btm.root.boxed_node_iter());
        Self {
            prefix_buf: Vec::with_capacity(256),
            prefix_idx,
            btnis,
        }
    }
}

impl <'a, V : Clone> BytesTrieMapCursor<'a, V> {
    pub fn next(&mut self) -> Option<(&[u8], &'a V)> {
        loop {
            match self.btnis.last_mut() {
                None => { return None }
                Some(last) => {
                    match last.next() {
                        None => {
                            // decrease view len by one level
                            self.prefix_idx.pop();
                            self.btnis.pop();
                        }
                        Some((key_bytes, item)) => {
                            let key_start = *self.prefix_idx.last().unwrap();
                            self.prefix_buf.truncate(key_start);
                            self.prefix_buf.extend(key_bytes);

                            match item {
                                ValOrChildRef::Val(val) => return Some((&self.prefix_buf[..], val)),
                                ValOrChildRef::Child(child) => {
                                    self.prefix_idx.push(self.prefix_buf.len());
                                    self.btnis.push(child.boxed_node_iter())
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// A map type that uses byte slices `&[u8]` as keys
///
/// This type is implemented using some of the approaches explained in the
/// ["Bitwise trie with bitmap" Wikipedia article](https://en.wikipedia.org/wiki/Bitwise_trie_with_bitmap).
///
/// ```
/// # use ringmap::bytetrie::BytesTrieMap;
/// let mut map = BytesTrieMap::<String>::new();
/// map.insert("one", "1".to_string());
/// map.insert("two", "2".to_string());
///
/// assert!(map.contains("one"));
/// assert_eq!(map.get("two"), Some(&"2".to_string()));
/// assert!(!map.contains("three"));
/// ```
#[repr(transparent)]
#[derive(Clone)]
pub struct BytesTrieMap<V> {
    pub(crate) root: DenseByteNode<V>
}

impl <V : Clone> BytesTrieMap<V> {
    pub fn new() -> Self {
        Self {
            root: DenseByteNode::new()
        }
    }

    //GOAT, redo this as "sub_map"
    // //QUESTION: who is the intended user of this method?  This interface is fundamentally unsafe
    // // because it exposes a mutable reference inside an immutable structure
    // #[allow(invalid_reference_casting)] //TODO: Take this away when the QUESTION is answered
    // pub(crate) fn at<K: AsRef<[u8]>>(&self, k: K) -> Option<&mut BytesTrieMap<V>> {
    //     let k = k.as_ref();
    //     let mut node = &self.root;

    //     if k.len() > 1 {
    //         for i in 0..k.len() - 1 {
    //             match node.get(k[i]) {
    //                 Some(cf) => {
    //                     match cf.rec.as_ref() {
    //                         Some(r) => { node = r }
    //                         None => { return None }
    //                     }
    //                 }
    //                 None => { return None }
    //             }
    //         }
    //     }

    //     node.get(k[k.len() - 1]).and_then(|cf| cf.rec.as_ref()).map(|subnode| 
    //         //SAFETY: the type-cast should be ok, because BytesTrieMap<V> is a #[repr(transparent)]
    //         // wrapper around ByteTrieNode<CoFree<V>>.
    //         //WARNING.  The cast_mut() is actually UNSAFE!!  See QUESTION above
    //         unsafe{ &mut *((&**subnode) as *const ByteTrieNode<CoFree<V>>).cast_mut().cast()  }
    //     )
    // }

    pub fn items<'a>(&'a self) -> impl Iterator<Item=(Vec<u8>, &'a V)> + 'a {
        BytesTrieMapIter::new(self)
    }

    pub fn item_cursor<'a>(&'a self) -> BytesTrieMapCursor<'a, V> {
        BytesTrieMapCursor::new(self)
    }

    pub fn contains<K: AsRef<[u8]>>(&self, k: K) -> bool {
        let k = k.as_ref();
        let (node, remaining_key) = traverse_to_leaf(&self.root, k);
        node.node_contains_val(remaining_key)
    }

    /// Inserts `v` at into the map at `k`.  Panics if `k` has a zero length
    pub fn insert<K: AsRef<[u8]>>(&mut self, k: K, v: V) -> bool {
        let k = k.as_ref();
        let (node, remaining_key) = traverse_to_leaf_mut(&mut self.root, k);

        match node.node_set_val(remaining_key, v) {
            Ok(old_val) => old_val.is_some(),
            Err(replacement_node) => {
                //GOAT, this is where I need to call a function to swap replacement_node with node.
                panic!();
            }
        }
    }

    // pub fn remove(&mut self, k: u16) -> Option<V> {
    //     let k1 = k as u8;
    //     let k2 = (k >> 8) as u8;
    //     match self.root.get(k1) {
    //         Some(btn) => {
    //             let btnr = unsafe { &mut **btn };
    //             let r = btnr.remove(k2);
    //             if btnr.len() == 0 {
    //                 self.root.remove(k1);
    //                 unsafe { dealloc(ptr::from_mut(btnr).cast(), Layout::new::<ByteTrieNode<V>>()); }
    //             }
    //             r
    //         }
    //         None => None
    //     }
    // }

    pub fn update<K: AsRef<[u8]>, F: FnOnce()->V>(&mut self, k: K, default_f: F) -> &mut V {
        let k = k.as_ref();
        let (node, remaining_key) = traverse_to_leaf_mut(&mut self.root, k);

        match node.node_update_val(remaining_key, Box::new(default_f)) {
            Ok(val) => val,
            Err(replacement_node) => {
                //GOAT, this is where I need to call a function to swap replacement_node with node,
                // and the re-borrow with node_get_val_mut()
                panic!();
            }
        }
    }

    pub fn get<K: AsRef<[u8]>>(&self, k: K) -> Option<&V> {
        let k = k.as_ref();
        let (node, remaining_key) = traverse_to_leaf(&self.root, k);
        node.node_get_val(remaining_key)
    }

    pub fn len(&self) -> usize {
        return self.root.node_subtree_len()
    }
}

fn traverse_to_leaf<'a, 'k, V>(start_node: &'a dyn TrieNode<V>, mut key: &'k[u8]) -> (&'a dyn TrieNode<V>, &'k [u8]) {
    let mut node = start_node;

    while let Some((consumed, next_node)) = node.node_get_child(key) {
        if key.len() > consumed {
            key = &key[consumed..];
            node = next_node;
        } else {
            break;
        }
    }
    (node, key)
}

fn traverse_to_leaf_mut<'a, 'k, V>(start_node: &'a mut dyn TrieNode<V>, mut key: &'k[u8]) -> (&'a mut dyn TrieNode<V>, &'k [u8]) {
    let mut node = start_node;

    let mut node_ptr = node as *mut dyn TrieNode<V>;
    while let Some((consumed, next_node)) = node.node_get_child_mut(key) {
        if key.len() > consumed {
            key = &key[consumed..];
            node = next_node;
            node_ptr = node as *mut dyn TrieNode<V>;
        } else {
            break;
        }
    }

    //SAFETY: node_ptr is a work-around for lack of Polonius.  Remove node_ptr and just use node itself in Rust 2024
    let node = unsafe{ &mut *node_ptr }; 
    (node, key)
}

impl<V: Clone, K: AsRef<[u8]>> FromIterator<(K, V)> for BytesTrieMap<V> {
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> Self {
        let mut map = Self::new();
        for (key, val) in iter {
            map.insert(key, val);
        }
        map
    }
}

pub(crate) trait TrieNode<V>: DynClone {

    // /// Returns `true` if the node contains a child node for the key path, otherwise returns `false`
    //GOAT what would you do with a child node except for traverse it?
    // fn node_contains_child(&self, key: &[u8]) -> bool;

    /// Returns the child node that matches `key` along with the number of `key` characters matched.
    /// Returns `None` if no child node matches the key, even if there is a value with that prefix
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)>;

    /// Same behavior as `node_get_child`, but operates across a mutable reference
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut dyn TrieNode<V>)>;

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
    fn node_set_val(&mut self, key: &[u8], val: V) -> Result<Option<V>, Box<dyn TrieNode<V> + '_>>;

    /// Returns a mutable reference to the value, creating it using `default_f` if it doesn't already
    /// exist
    ///
    /// If this method returns Err(node), then the node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    /// Then the new node may be re-borrowed.
    //GOAT, consider a boxless version of this that takes a regular &dyn Fn() instead of FnOnce
    //Or maybe two versions, one that takes an &dyn Fn, and another that takes a V
    fn node_update_val(&mut self, key: &[u8], default_f: Box<dyn FnOnce()->V + '_>) -> Result<&mut V, Box<dyn TrieNode<V>>>;

    /// Returns `true` if the node contains no children nor values, otherwise false
    fn node_is_empty(&self) -> bool;

    /// Returns a boxed iterator over each item contained within the node, both child nodes and values
    fn boxed_node_iter<'a>(&'a self) -> Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a>;

    /// Returns the total number of leaves contained within the whole subtree defined by the node
    fn node_subtree_len(&self) -> usize;

    /// Returns the number of internal paths within the node.  That includes child nodes descending from
    /// the node as well as values; in the case where a child node and a value have the same internal path
    /// it will be counted as one item
    fn item_count(&self) -> usize;

    /// Returns the nth child of this node and the prefix leading to that child, or None
    /// if `n >= self.child_count()`
    ///
    /// If 'forward == true` then `n` counts forward from the first element, oterwise it counts
    /// backward from the last
    fn nth_child(&self, n: usize, forward: bool) -> Option<(&[u8], &dyn TrieNode<V>)>;

    /// Returns the child of this node that is immediately before or after the child identified by `key`
    ///
    /// Returns None if the found child node is already the first or last child, or if `key` does not
    /// identify any contained subnode
    ///
    /// If 'next == true` then the returned child will be immediately after to the node found by
    /// `key`, oterwise it will be immedtely before
    fn get_sibling_of_child(&self, key: &[u8], next: bool) -> Option<(&[u8], &dyn TrieNode<V>)>;

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
}

pub(crate) enum ValOrChildRef<'a, V> {
    Val(&'a V),
    Child(&'a dyn TrieNode<V>)
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
