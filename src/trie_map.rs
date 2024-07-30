
use crate::trie_node::*;
use crate::zipper::*;

/// A map type that uses byte slices `&[u8]` as keys
///
/// This type is implemented using some of the approaches explained in the
/// ["Bitwise trie with bitmap" Wikipedia article](https://en.wikipedia.org/wiki/Bitwise_trie_with_bitmap).
///
/// ```
/// # use ringmap::trie_map::BytesTrieMap;
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
    pub(crate) root: TrieNodeODRc<V>
}

impl <V : Clone> BytesTrieMap<V> {
    /// Creates a new empty map
    pub fn new() -> Self {
        #[cfg(feature = "all_dense_nodes")]
        let root = TrieNodeODRc::new(crate::dense_byte_node::DenseByteNode::new());
        #[cfg(not(feature = "all_dense_nodes"))]
        let root = TrieNodeODRc::new(crate::line_list_node::LineListNode::new());
        Self { root }
    }

    //GOAT, redo this as "at_path"
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

    /// Creates a new [ReadZipper] starting at the root of a BytesTrieMap
    pub fn read_zipper(&self) -> ReadZipper<V> {
        ReadZipper::new_with_node_and_path_internal(self.root.borrow(), &[], None)
    }

    /// Creates a new [ReadZipper] with the specified path from the root of the map
    pub fn read_zipper_at_path<'a, 'k>(&'a self, path: &'k[u8]) -> ReadZipper<'a, 'k, V> {
        ReadZipper::new_with_node_and_path(self.root.borrow(), path.as_ref())
    }

    /// Creates a new [WriteZipper] starting at the root of a BytesTrieMap
    pub fn write_zipper(&mut self) -> WriteZipper<V> {
        WriteZipper::new_with_node_and_path_internal(&mut self.root, &[])
    }

    /// Creates a new [WriteZipper] with the specified path from the root of the map
    pub fn write_zipper_at_path<'a, 'k>(&'a mut self, path: &'k[u8]) -> WriteZipper<'a, 'k, V> {
        WriteZipper::new_with_node_and_path(&mut self.root, path.as_ref())
    }

    /// Returns an iterator over all key-value pairs within the map
    ///
    /// NOTE: This is much less efficient than using the [read_zipper](Self::read_zipper) method
    pub fn iter<'a>(&'a self) -> impl Iterator<Item=(Vec<u8>, &'a V)> + 'a {
        self.read_zipper().into_iter()
    }

    /// Returns a [BytesTrieMapCursor] to traverse all key-value pairs within the map.  This is more efficient
    /// than using [iter](Self::iter), but is not compatible with the [Iterator] trait
    ///
    /// WARNING: This API will be deprecated in favor of the [read_zipper](Self::read_zipper) method
    pub fn cursor<'a>(&'a self) -> BytesTrieMapCursor<'a, V> {
        BytesTrieMapCursor::new(self)
    }

    /// Returns `true` if the map contains a value at the specified key, otherwise returns `false`
    pub fn contains<K: AsRef<[u8]>>(&self, k: K) -> bool {
        let k = k.as_ref();

        //NOTE: Here is the old impl traversing without the zipper.  The zipper version appears to be
        // nearly the same perf.  All averages within 3% in both directions, and the zipper impl being
        // faster as often as the native (non-zipper) version
        // let (node, remaining_key) = traverse_to_leaf(self.root.borrow(), k);
        // node.node_contains_val(remaining_key)

        let zipper = self.read_zipper_at_path(k);
        zipper.is_value()
    }

    /// Returns `true` if a path is contained within the map, or `false` otherwise
    pub fn contains_path<K: AsRef<[u8]>>(&self, k: K) -> bool {
        let k = k.as_ref();
        let zipper = self.read_zipper_at_path(k);
        zipper.path_exists()
    }

    /// Inserts `v` into the map at `k`.  Panics if `k` has a zero length
    ///
    /// Returns `Some(replaced_val)` if an existing value was replaced, otherwise returns `None` if
    /// the value was added to the map without replacing anything.
    pub fn insert<K: AsRef<[u8]>>(&mut self, k: K, v: V) -> Option<V> {
        let k = k.as_ref();

        //NOTE: Here is the old impl traversing without the zipper.  Kept here for benchmarking purposes
        // However, the zipper version is basically identical performance, within the margin of error 
        // traverse_to_leaf_static_result(&mut self.root, k,
        // |node, remaining_key| node.node_set_val(remaining_key, v),
        // |_new_leaf_node, _remaining_key| None)

        let mut zipper = self.write_zipper_at_path(k);
        zipper.set_value(v)
    }

    //GOAT, make a separate `join_with` that is similar to `insert` except replaces V with a merged V rather
    // than replacing it

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

    //GOAT-Deprecated-Update
    // pub fn update<K: AsRef<[u8]>, F: FnOnce()->V>(&mut self, k: K, default_f: F) -> &mut V {
    //     let k = k.as_ref();

    //     traverse_to_leaf_mut(&mut self.root, k,
    //     |node, remaining_key| node.node_update_val(remaining_key, Box::new(default_f)),
    //     |new_leaf_node, remaining_key| new_leaf_node.node_get_val_mut(remaining_key).unwrap())
    // }

    /// Returns a reference to the value at the specified path
    pub fn get<K: AsRef<[u8]>>(&self, k: K) -> Option<&V> {
        let k = k.as_ref();

        //NOTE: Here is the old impl traversing without the zipper.  The zipper version appears to be
        // nearly the same perf.  All averages within 3% in both directions, and the zipper impl being
        // faster as often as the native (non-zipper) version
        // let (node, remaining_key) = traverse_to_leaf(self.root.borrow(), k);
        // node.node_get_val(remaining_key)

        let zipper = self.read_zipper_at_path(k);
        zipper.get_value()
    }

    /// Returns the total number of items contained within the map
    ///
    /// WARNING: This is not a cheap method. It may have an order-N cost
    pub fn len(&self) -> usize {
        return self.root.borrow().node_subtree_len()
    }
}

/// An iterator-like object that traverses key-value pairs in a [BytesTrieMap], however only one
/// returned reference may exist at a given time
///
/// TODO: Soon we may want to deprecate this API entirely, as it is a subset of the functionality
/// available from the [crate::zipper::Zipper].  However, the current implementation is about 25% faster when comparing
/// like-for-like workloads that are non-pathological.  And this is including the overhead of allocating
/// boxed node_iterators.  I haven't investigated why the zipper isn't faster, but my guess is is 
/// that the probable cause is the higher cost of traversing using inner-paths instead of just treating
/// all contained sub-nodes as a flat collection of values and onward-links.  I believe it would probably
/// be possible to exceed the current BytesTrieMapCursor traversal speed with a Zipper, with a little
/// more work.  Possibly by using a fixed-size "token" that the node may used to encode some data about
/// its current position and intermediate traversal state.
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
        btnis.push(btm.root.borrow().boxed_node_iter());
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

// NOTE: The below function duplicates the functionality of the zipper, so it's deprecated and will be deleted
// however it's kept for now to re-enable the old code path if that's needed for any reason.
// #[inline]
// pub(crate) fn traverse_to_leaf<'a, 'k, V>(start_node: &'a dyn TrieNode<V>, mut key: &'k[u8]) -> (&'a dyn TrieNode<V>, &'k [u8]) {
//     let mut node = start_node;

//     while let Some((consumed, next_node)) = node.node_get_child(key) {
//         if key.len() > consumed {
//             key = &key[consumed..];
//             node = next_node;
//         } else {
//             break;
//         }
//     }
//     (node, key)
// }

// NOTE: the below function deuplicates the functionality of the WriteZipper, so it will be deleted.  It's kept
// for now to re-enable the old code paths for benchmarking, or any other reason
// use mutcursor::MutCursor;
// #[inline]
// fn traverse_to_leaf_mut<'a, V:Clone, NodeF, RetryF, R>(start_node: &'a mut TrieNodeODRc<V>, mut key: &[u8], node_f: NodeF, retry_f: RetryF) -> &'a mut R
//     where
//     NodeF: for<'f> FnOnce(&'f mut dyn TrieNode<V>, &[u8]) -> Result<&'f mut R, TrieNodeODRc<V>>,
//     RetryF: for<'f> FnOnce(&'f mut dyn TrieNode<V>, &[u8]) -> &'f mut R,
// {
//     //TODO: Get rid of this `start_node_ptr` under polonius
//     let start_node_ptr = start_node as *mut TrieNodeODRc<V>;
//     let mut node = MutCursor::<dyn TrieNode<V>, 2>::new(start_node.make_mut());

//     //Traverse until we find a leaf
//     let mut parent_key: &[u8] = &[];
//     loop {
//         if !node.advance(|node| {
//             match node.node_get_child_mut(key) {
//                 Some((consumed, next_node)) => {
//                     if key.len() > consumed {
//                         parent_key = &key[..consumed];
//                         key = &key[consumed..];
//                         Some(next_node.make_mut())
//                     } else {
//                         None
//                     }
//                 },
//                 None => None
//             }
//         }) {
//             break;
//         }
//     }

//     match node.try_map_into_mut(|top_ref| {
//         node_f(top_ref, key)
//     }) {
//         Ok(result) => result,
//         Err((mut node, err_node)) => {
//             if node.depth() > 0 {
//                 node.backtrack();
//                 let leaf_node = node.into_mut().node_replace_child(parent_key, err_node);
//                 retry_f(leaf_node, key)
//             } else {
//                 //Safety: Under Polonius, this is fine.
//                 let start_node = unsafe{ &mut *start_node_ptr };
//                 *start_node = err_node;
//                 retry_f(start_node.make_mut(), key)
//             }
//         }
//     }
// }

// /// This is an ugly duplication of the logic in [Self::traverse_to_leaf_mut].  The reason is a limitation in
// /// the generic system's inability to differentiate a mutable lifetime from a borrowed lifetime.  Duplicating
// /// the logic is the least-bad option for now.  See response from Quinedot in thread: https://users.rust-lang.org/t/lifetimes-on-closure-bounds-to-end-mutable-borrow/113575/3
// #[inline]
// fn traverse_to_leaf_static_result<'a, V:Clone, NodeF, RetryF, R>(start_node: &'a mut TrieNodeODRc<V>, mut key: &[u8], node_f: NodeF, retry_f: RetryF) -> R
//     where
//     NodeF: FnOnce(&mut dyn TrieNode<V>, &[u8]) -> Result<R, TrieNodeODRc<V>>,
//     RetryF: FnOnce(&mut dyn TrieNode<V>, &[u8]) -> R,
// {
//     let mut node = MutCursor::<dyn TrieNode<V>, 2>::new(start_node.make_mut());

//     //Traverse until we find a leaf
//     let mut parent_key: &[u8] = &[];
//     loop {
//         if !node.advance(|node| {
//             match node.node_get_child_mut(key) {
//                 Some((consumed, next_node)) => {
//                     if key.len() > consumed {
//                         parent_key = &key[..consumed];
//                         key = &key[consumed..];
//                         Some(next_node.make_mut())
//                     } else {
//                         None
//                     }
//                 },
//                 None => None
//             }
//         }) {
//             break;
//         }
//     }

//     match node_f(node.top_mut(), key) {
//         Ok(result) => result,
//         Err(err_node) => {
//             if node.depth() > 0 {
//                 node.backtrack();
//                 let leaf_node = node.top_mut().node_replace_child(parent_key, err_node);
//                 retry_f(leaf_node, key)
//             } else {
//                 *start_node = err_node;
//                 retry_f(start_node.make_mut(), key)
//             }
//         }
//     }
// }

impl<V: Clone, K: AsRef<[u8]>> FromIterator<(K, V)> for BytesTrieMap<V> {
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> Self {
        let mut map = Self::new();
        for (key, val) in iter {
            map.insert(key, val);
        }
        map
    }
}

#[test]
fn map_test() {
    let mut map = BytesTrieMap::new();
    //NOW: map contains an empty ListNode

    map.insert("aaaaa", "aaaaa");
    assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
    //NOW: map contains a ListNode with slot_0 filled by a value

    map.insert("bbbbb", "bbbbb");
    assert_eq!(map.get("bbbbb").unwrap(), &"bbbbb");
    //NOW: map contains a ListNode with slot_0 and slot_1 filled by values

    map.insert("ccccc", "ccccc");
    assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
    assert_eq!(map.get("bbbbb").unwrap(), &"bbbbb");
    assert_eq!(map.get("ccccc").unwrap(), &"ccccc");
    //NOW: map contains a DenseByteNode, with 3 separate ListNodes, each containing one value

    map.insert("ddddd", "ddddd");
    assert_eq!(map.get("ddddd").unwrap(), &"ddddd");
    //NOW: map contains a DenseByteNode, with 4 separate ListNodes, each containing one value

    map.insert("abbbb", "abbbb");
    assert_eq!(map.get("abbbb").unwrap(), &"abbbb");
    //NOW: Dense("a"..) -> List("aaaa", "bbbb")

    map.insert("aaaab", "aaaab");
    assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
    assert_eq!(map.get("bbbbb").unwrap(), &"bbbbb");
    assert_eq!(map.get("abbbb").unwrap(), &"abbbb");
    assert_eq!(map.get("aaaab").unwrap(), &"aaaab");
    //NOW: Dense("a"..) -> List("aaa", "bbbb") -> List("a", "b")

    map.insert("aaaac", "aaaac");
    assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
    assert_eq!(map.get("aaaab").unwrap(), &"aaaab");
    assert_eq!(map.get("aaaac").unwrap(), &"aaaac");
    //NOW: Dense("a"..) -> List("aaa", "bbbb") -> Dense("a", "b", "c")

    map.insert("acaaa", "acaaa");
    assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
    assert_eq!(map.get("aaaab").unwrap(), &"aaaab");
    assert_eq!(map.get("aaaac").unwrap(), &"aaaac");
    assert_eq!(map.get("abbbb").unwrap(), &"abbbb");
    assert_eq!(map.get("acaaa").unwrap(), &"acaaa");
    //NOW: Dense("a"..) -> Dense("a", "b", "c") a-> List("aa") -> Dense("a", "b", "c")
    //                                          b-> List("bbb")
    //                                          c-> List("aaa")
}

#[test]
fn long_key_map_test() {
    let mut map = BytesTrieMap::new();

    map.insert("aaaaaaaaaa01234567890123456789", 30);
    assert_eq!(map.get("aaaaaaaaaa01234567890123456789").unwrap(), &30);

    map.insert("bbbbbbbbbb012345678901234567891", 31);
    assert_eq!(map.get("bbbbbbbbbb012345678901234567891").unwrap(), &31);

    map.insert("cccccccccc012345678901234567890123456789", 40);
    assert_eq!(map.get("cccccccccc012345678901234567890123456789").unwrap(), &40);

    map.insert("dddddddddd01234567890123456789012345678901234", 45);
    assert_eq!(map.get("dddddddddd01234567890123456789012345678901234").unwrap(), &45);

    map.insert("eeeeeeeeee01234567890123456789012345678901234567890123456789012345678901234567890123456789", 90);
    assert_eq!(map.get("eeeeeeeeee01234567890123456789012345678901234567890123456789012345678901234567890123456789").unwrap(), &90);
}

#[test]
fn map_contains_path_test() {
    let mut btm = BytesTrieMap::new();
    let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
    rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

    assert_eq!(btm.contains_path(b"can"), true);
    assert_eq!(btm.contains_path(b"cannon"), true);
    assert_eq!(btm.contains_path(b"cannonade"), false);
    assert_eq!(btm.contains_path(b""), true);
}

#[test]
fn map_update_test() {
    let mut btm = BytesTrieMap::new();
    let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
    rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

    // let zipper = btm.write_zipper_at_path(b"cannon");
    //GOAT, need the `path_exists`, `get_mut`, and `insert` calls and an `get_mut_with_default` convenience
}

//GOAT TODO LIST:
// 3. Re-enable "at_path" API
// 4. Other ops: "join_all"??, "restrict"??, ??