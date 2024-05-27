use std::fmt::{Debug, Formatter};
use std::ptr::slice_from_raw_parts;

use crate::dense_byte_node::*;

use rclite::Rc;

//GOAT, get rid of this when the abstraction is complete
pub type ByteTrieNode<V> = DenseByteNode<V>;

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

                            // match &cf.rec {
                            //     None => {}
                            //     Some(rec) => {
                            //         self.prefix = k.clone();
                            //         self.btnis.push(rec.boxed_node_iter());
                            //     }
                            // }

                            // match &cf.value {
                            //     None => {}
                            //     Some(v) => {
                            //         return Some((k, &v))
                            //     }
                            // }

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

//GOAT, turn this back on
// /// An iterator-like object that traverses key-value pairs in a [BytesTrieMap], however only one
// /// returned reference may exist at a given time
// pub struct BytesTrieMapCursor<'a, V> where V : Clone {
//     prefix: Vec<u8>,
//     btnis: Vec<Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a>>,
//     nopush: bool
// }

// impl <'a, V : Clone> BytesTrieMapCursor<'a, V> {
//     fn new(btm: &'a BytesTrieMap<V>) -> Self {
//         Self {
//             prefix: vec![],
//             btnis: vec![btm.root.boxed_node_iter()],
//             nopush: false
//         }
//     }
// }

// impl <'a, V : Clone> BytesTrieMapCursor<'a, V> {
//     pub fn next(&mut self) -> Option<(&[u8], &'a V)> {
//         loop {
//             match self.btnis.last_mut() {
//                 None => { return None }
//                 Some(last) => {
//                     match last.next() {
//                         None => {
//                             // decrease view len with one
//                             self.prefix.pop();
//                             self.btnis.pop();
//                         }
//                         Some((b, cf)) => {
//                             if self.nopush {
//                                 *self.prefix.last_mut().unwrap() = b;
//                                 self.nopush = false;
//                             } else {
//                                 self.prefix.push(b);
//                             }

//                             match unsafe { cf.rec.as_ref() } {
//                                 None => {
//                                     self.nopush = true;
//                                 }
//                                 Some(rec) => {
//                                     self.nopush = false;
//                                     self.btnis.push(rec.boxed_node_iter());
//                                 }
//                             }

//                             match &cf.value {
//                                 None => {}
//                                 Some(v) => {
//                                     return Some((&self.prefix, v))
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
// }

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

    //goat turn this back on
    // pub fn item_cursor<'a>(&'a self) -> BytesTrieMapCursor<'a, V> {
    //     BytesTrieMapCursor::new(self)
    // }

    pub fn contains<K: AsRef<[u8]>>(&self, k: K) -> bool {
        self.get(k).is_some()
    }

    /// Inserts `v` at into the map at `k`.  Panics if `k` has a zero length
    pub fn insert<K: AsRef<[u8]>>(&mut self, k: K, v: V) -> bool {
        let mut k = k.as_ref();
        let (node, remaining_key) = traverse_to_leaf_mut(&mut self.root, k);

        //GOAT
        // let mut node = &mut self.root;

        // let mut node_ptr = node as *mut DenseByteNode<V>;
        // while let Some((consumed, next_node)) = node.node_get_child_mut(k) {
        //     if k.len() > consumed {
        //         k = &k[consumed..];
        //         node = next_node.as_dense_mut();
        //         node_ptr = node as *mut DenseByteNode<V>;
        //     } else {
        //         break;
        //     }
        // }

        // //SAFETY: node_ptr is a work-around for lack of Polonius.  Remove node_ptr and use node in Rust 2024
        // let node = unsafe{ &mut *node_ptr };


        match node.node_set_val(remaining_key, v) {
            Ok(old_val) => old_val.is_some(),
            Err(replacement_node) => {
                //GOAT, this is where I need to call a function to swap replacement_node with node.
                panic!();
            }
        }

        //GOAT DEAD
        // if k.len() > 1 {
        //     for i in 0..k.len() - 1 {
        //         let cf = node.update(k[i], || CoFree{rec: None, value: None});

        //         if cf.rec.is_none() {
        //             let l = ByteTrieNode::new();
        //             cf.rec = Some(Rc::new(l));
        //         }
        //         node = Rc::make_mut(cf.rec.as_mut().unwrap());
        //     }
        // }
        //
        // let lk = k[k.len() - 1];
        // if node.node_contains(&[lk]) { //GOAT, Need a "get_or_split" type interface
        //     let cf = unsafe{ node.get_unchecked_mut(lk) };
        //     match cf.value {
        //         None => {
        //             cf.value = Some(v);
        //             false
        //         }
        //         Some(_) => {
        //             true
        //         }
        //     }
        // } else {
        //     let cf = CoFree{ rec: None, value: Some(v) };
        //     node.insert(lk, cf)
        // }
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

    // pub fn deepcopy(&self) -> Self {
    //     return self.items().collect();
    // }

    pub fn update<K: AsRef<[u8]>, F: FnOnce()->V>(&mut self, k: K, default_f: F) -> &mut V {
        let mut k = k.as_ref();
        let (node, remaining_key) = traverse_to_leaf_mut(&mut self.root, k);

        // let k = k.as_ref();
        // let mut node = &mut self.root;

        // if k.len() > 1 {
        //     for i in 0..k.len() - 1 {
        //         let cf = node.update(k[i], || CoFree{rec: None, value: None});

        //         if cf.rec.is_none() {
        //             let l = ByteTrieNode::new();
        //             cf.rec = Some(Rc::new(l));
        //         }
        //         node = Rc::make_mut(cf.rec.as_mut().unwrap());
        //     }
        // }


        match node.node_update_val(remaining_key, Box::new(default_f)) {
            Ok(val) => val,
            Err(replacement_node) => {
                //GOAT, this is where I need to call a function to swap replacement_node with node,
                // and the re-borrow with node_get_val_mut()
                panic!();
            }
        }

        // let lk = k[k.len() - 1];
        // let cf = node.update(lk, || CoFree{ rec: None, value: None });
        // cf.value.get_or_insert_with(default)
    }

    pub fn get<K: AsRef<[u8]>>(&self, k: K) -> Option<&V> {
        let mut k = k.as_ref();
        let mut node = &self.root;

        while let Some((consumed, next_node)) = node.node_get_child(k) {
            if k.len() > consumed {
                k = &k[consumed..];
                node = next_node.as_dense();
            } else {
                break;
            }
        }

        node.node_get_val(k)


        //GOAT trash
        // if k.len() > 1 {
        //     for i in 0..k.len() - 1 {
        //         match node.get(k[i]) {
        //             Some(cf) => {
        //                 match cf.rec.as_ref() {
        //                     Some(r) => { node = r }
        //                     None => { return None }
        //                 }
        //             }
        //             None => { return None }
        //         }
        //     }
        // }

        // match node.get(k[k.len() - 1]) {
        //     None => { None }
        //     Some(CoFree{ rec: _, value }) => {
        //         match value {
        //             None => { None }
        //             Some(v) => { Some(v) }
        //         }
        //     }
        // }
    }

    pub fn len(&self) -> usize {
        return self.root.node_subtree_len()
    }
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

// #[derive(Clone)]
// pub struct ShortTrieMap<V> {
//     pub(crate) root: ByteTrieNode<Option<Rc<ByteTrieNode<V>>>>
// }

// impl <V : Clone> FromIterator<(u16, V)> for ShortTrieMap<V> {
//     fn from_iter<I: IntoIterator<Item=(u16, V)>>(iter: I) -> Self {
//         let mut tm = ShortTrieMap::new();
//         for (k, v) in iter { tm.insert(k, v); }
//         tm
//     }
// }

// impl <V : Clone> ShortTrieMap<V> {
//     pub fn new() -> Self {
//         Self {
//             root: ByteTrieNode::new()
//         }
//     }

//     pub fn items<'a>(&'a self) -> impl Iterator<Item=(u16, &'a V)> + 'a {
//         self.root.items().flat_map(|(k1, l1)| {
//             l1.as_ref().unwrap().items().map(move |(k2, v)| ((k1 as u16) | ((k2 as u16) << 8), v))
//         })
//     }

//     pub fn contains(&self, k: u16) -> bool {
//         let k1 = k as u8;
//         let k2 = (k >> 8) as u8;
//         if self.root.contains(k1) {
//             let rl1 = unsafe{ self.root.get_unchecked(k1) };
//             rl1.as_ref().unwrap().contains(k2)
//         } else {
//             false
//         }
//     }

//     pub fn insert(&mut self, k: u16, v: V) -> bool {
//         let k1 = k as u8;
//         let k2 = (k >> 8) as u8;
//         if self.root.contains(k1) {
//             let rl1 = unsafe{ self.root.get_unchecked_mut(k1) };
//             Rc::make_mut(rl1.as_mut().unwrap()).insert(k2, v)
//         } else {
//             let mut l1 = ByteTrieNode::new();
//             l1.insert(k2, v);
//             let rl1 = Some(Rc::new(l1));
//             self.root.insert(k1, rl1);
//             false
//         }
//     }

//     pub fn remove(&mut self, k: u16) -> Option<V> {
//         let k1 = k as u8;
//         let k2 = (k >> 8) as u8;
//         match self.root.get_mut(k1) {
//             Some(btn) => {
//                 let btnr = Rc::make_mut(btn.as_mut().unwrap());
//                 let r = btnr.remove(k2);
//                 if btnr.len() == 0 {
//                     btnr.remove(k1);
//                 }
//                 r
//             }
//             None => None
//         }
//     }

//     // pub fn deepcopy(&self) -> Self {
//     //     return self.items().collect();
//     // }

//     pub fn get(&self, k: u16) -> Option<&V> {
//         let k1 = k as u8;
//         let k2 = (k >> 8) as u8;
//         self.root.get(k1).and_then(|l1| {
//             let rl1 = &**l1.as_ref().unwrap();
//             rl1.get(k2)
//         })
//     }
// }

pub(crate) trait TrieNode<V> {

    // /// Returns `true` if the node contains a child node for the key path, otherwise returns `false`
    // fn node_contains_child(&self, key: &[u8]) -> bool;

    /// Returns the child node that matches `key` along with the number of `key` characters matched.
    /// Returns `None` if no child node matches the key, even if there is a value with that prefix
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)>;

    /// Same behavior as `node_get_child`, but operates across a mutable reference
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut dyn TrieNode<V>)>;

    /// Returns the value that matches `key` if it contained within the node
    fn node_get_val(&self, key: &[u8]) -> Option<&V>;

    /// Mutable version of [node_get_val]
    fn node_get_val_mut(&mut self, key: &[u8]) -> Option<&mut V>;

    /// Sets the value specified by `key` to the object V.  Returns Ok(None) if a new value was added,
    /// returns Ok(Some(v)) with the old value if the value was replaced
    ///
    /// If this method returns Err(node), then the node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    fn node_set_val(&mut self, key: &[u8], val: V) -> Result<Option<V>, Box<dyn TrieNode<V>>>;

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

    /// Returns the number of child nodes descending from this node
    fn child_count(&self) -> usize;

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




    /// Temporary scaffolding to make abstracting the code easier
    fn as_dense(&self) -> &DenseByteNode<V>;
    fn as_dense_mut(&mut self) -> &mut DenseByteNode<V>;


}

pub(crate) enum ValOrChildRef<'a, V> {
    Val(&'a V),
    Child(&'a dyn TrieNode<V>)
}

//GOAT, this is probably a pointless trait
// pub(crate) trait IterableNode {
//     type ValuesIterT;
//     type ChildIterT;

//     /// Returns an Iterator over all values directly contained by the node itself, but not by traversing
//     /// the node's subtrees
//     fn values_iter(self) -> Self::ValuesIterT;

//     /// Returns an Iterator over all child nodes of the node
//     fn child_iter(self) -> Self::ChildIterT;

// }

