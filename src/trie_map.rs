use core::cell::UnsafeCell;
use std::sync::{Mutex, MutexGuard};

use num_traits::{PrimInt, zero};
use crate::trie_node::*;
use crate::zipper::*;
use crate::ring::{Lattice, DistributiveLattice, PartialDistributiveLattice, PartialQuantale};
use crate::zipper_tracking::*;

/// A map type that uses byte slices `&[u8]` as keys
///
/// This type is implemented using some of the approaches explained in the
/// ["Bitwise trie with bitmap" Wikipedia article](https://en.wikipedia.org/wiki/Bitwise_trie_with_bitmap).
///
/// ```
/// # use pathmap::trie_map::BytesTrieMap;
/// let mut map = BytesTrieMap::<String>::new();
/// map.insert("one", "1".to_string());
/// map.insert("two", "2".to_string());
///
/// assert!(map.contains("one"));
/// assert_eq!(map.get("two"), Some(&"2".to_string()));
/// assert!(!map.contains("three"));
/// ```
pub struct BytesTrieMap<V> {
    root: RootWrapper<V>,
    zipper_tracker: ZipperTracker,
}

/// An internal wrapper to control mutable access to the root node.  Provides zero-overhead for
/// const access, because all mut access is only taken in some very special circumstances.
///
/// WARNING! RootWrapper, by itself, is not safe.  It relies on specific access patterns
///
/// NOTE: This mutex itself is likely a stop-gap, since it doesn't scale.  This design imposes a
/// considerable overhead on making new zippers, even if the zippers themselves are thread-safe
/// after they are created.
struct RootWrapper<V> {
    node: UnsafeCell<TrieNodeODRc<V>>,
    lock: Mutex<()>,
}

unsafe impl<V: Send + Sync> Send for RootWrapper<V> {}
unsafe impl<V: Send + Sync> Sync for RootWrapper<V> {}

impl<V> RootWrapper<V> {
    pub(crate) fn new(node: TrieNodeODRc<V>) -> Self {
        Self {
            node: UnsafeCell::new(node),
            lock: Mutex::new(()),
        }
    }
    #[inline]
    pub(crate) fn get(&self) -> &TrieNodeODRc<V> {
        unsafe{ &*self.node.get() }
    }
    #[inline]
    pub(crate) fn get_mut(&mut self) -> &mut TrieNodeODRc<V> {
        self.node.get_mut()
    }
    pub(crate) fn into_inner(self) -> TrieNodeODRc<V> {
        self.node.into_inner()
    }
    pub(crate) fn exclusive_get_mut(&self) -> (&mut TrieNodeODRc<V>, MutexGuard<()>) {
        let guard = self.lock.lock().unwrap();
        let node = unsafe{ &mut *self.node.get() };
        (node, guard)
    }
}

impl<V: Clone + Send + Sync> Clone for BytesTrieMap<V> {
    fn clone(&self) -> Self {
        Self::new_with_root(self.root().clone())
    }
}

impl<V: Clone + Send + Sync> BytesTrieMap<V> {
    #[inline]
    pub(crate) fn root(&self) -> &TrieNodeODRc<V> {
        self.root.get()
    }
    #[inline]
    pub(crate) fn root_mut(&mut self) -> &mut TrieNodeODRc<V> {
        self.root.get_mut()
    }

    /// Creates a new empty map
    pub fn new() -> Self {
        #[cfg(feature = "all_dense_nodes")]
        let root = TrieNodeODRc::new(crate::dense_byte_node::DenseByteNode::new());
        #[cfg(not(feature = "all_dense_nodes"))]
        let root = TrieNodeODRc::new(crate::line_list_node::LineListNode::new());
        Self::new_with_root(root)
    }

    /// Internal Method.  Creates a new BytesTrieMap with the supplied root node
    #[inline]
    pub(crate) fn new_with_root(root: TrieNodeODRc<V>) -> Self {
        Self {
            root: RootWrapper::new(root),
            zipper_tracker: ZipperTracker::default(),
        }
    }

    pub fn range<const BE : bool, R : PrimInt + std::ops::AddAssign + num_traits::ToBytes + std::fmt::Display>(start: R, stop: R, step: R, value: V) -> BytesTrieMap<V> {
        // #[cfg(feature = "all_dense_nodes")]
        // we can extremely efficiently generate ranges, but currently we're limited to range(0, BASE**j, k < BASE)
        // let root = crate::dense_byte_node::_so_range(step as u8, 4);
        // BytesTrieMap::<()>::new_with_root(root)
        //fallback

        //GOAT, this method is highly sub-optimal.  It should be possible to populate a range in log n time,
        // rather than linear time.  Adam has already written code for this, but it's specific to the DenseByteNode
        // and is commented out in that file
        let mut new_map = Self::new();
        let mut zipper = new_map.write_zipper();

        let mut i = start;
        let positive = step > zero();
        loop {
            if positive { if i >= stop { break } }
            else { if i <= step { break } }
            // println!("{}", i);
            if BE { zipper.descend_to(i.to_be_bytes()); }
            else { zipper.descend_to(i.to_le_bytes()); }
            zipper.set_value(value.clone());
            zipper.reset();

            i += step;
        }
        drop(zipper);

        new_map
    }

    /// Internal Method.  Removes and returns the root from a BytesTrieMap
    #[inline]
    pub(crate) fn into_root(self) -> Option<TrieNodeODRc<V>> {
        if !self.root().borrow().node_is_empty() {
            Some(self.root.into_inner())
        } else {
            None
        }
    }

    /// Creates a new [ReadZipper] starting at the root of a BytesTrieMap
    pub fn read_zipper(&self) -> ReadZipper<V> {
        let zipper_tracker = self.zipper_tracker.new_read_path(&[]);
        ReadZipper::new_with_node_and_path_internal(self.root().borrow().as_tagged(), &[], Some(0), None, zipper_tracker)
    }

    /// Creates a new [ReadZipper] with the specified path from the root of the map
    pub fn read_zipper_at_path<'a, 'k>(&'a self, path: &'k[u8]) -> ReadZipper<'a, 'k, V> {
        let zipper_tracker = self.zipper_tracker.new_read_path(path);
        ReadZipper::new_with_node_and_path(self.root().borrow(), path.as_ref(), Some(path.len()), zipper_tracker)
    }

    /// Creates a new [WriteZipper] starting at the root of a BytesTrieMap
    pub fn write_zipper(&mut self) -> WriteZipper<V> {
        let zipper_tracker = self.zipper_tracker.new_write_path(&[]);
        WriteZipper::new_with_node_and_path_internal(self.root_mut(), &[], zipper_tracker)
    }

    /// Creates a new [WriteZipper] with the specified path from the root of the map
    pub fn write_zipper_at_path<'a, 'k>(&'a mut self, path: &'k[u8]) -> WriteZipper<'a, 'k, V> {
        let zipper_tracker = self.zipper_tracker.new_write_path(path);
        WriteZipper::new_with_node_and_path(self.root_mut(), path, zipper_tracker)
    }

    /// Creates a new [WriteZipper] with the specified path from the root of the map, where the
    /// caller guarantees that no existing zippers may access the specified path
    ///
    /// NOTE: There is no safe version of this method because we don't want to pay the overhead of
    /// tracking every ReadZipper's path in a release build
    ///
    //GOAT!!  I Realized this is unsound because the TrieMap direct methods can still traverse from the
    // root, and potentially read parts of the trie that a WriteZipper is in the process of modifying.
    //Instead I propose a "ZipperMaker" that takes a mutable borrow of the map, and can dispense both read
    // and write zippers
    pub unsafe fn write_zipper_at_exclusive_path_unchecked<'a, 'k>(&'a self, path: &[u8]) -> WriteZipper<'a, 'k, V> {
        let path_len = path.len();
        if path_len == 0 {
            panic!("Fatal Error: Root path cannot be modified without mutable access to the map.  Use TrieMap::write_zipper");
        }
        let zipper_tracker = self.zipper_tracker.new_write_path(path);
        let (map_root_node, root_guard) = self.root.exclusive_get_mut();
        let (_created_node, zipper_root_node) = prepare_exclusive_write_path(map_root_node, &path);
        //GOAT QUESTION: Do we want to pay for pruning the parent of a zipper when the zipper get's dropped?
        // If we do, we can store (_created_node || _created_cf) in the zipper, so we can opt out of trying
        // to prune the zipper's path.

        let zipper = WriteZipper::new_with_node_and_path_internal(zipper_root_node, &[], zipper_tracker);
        drop(root_guard);
        zipper
    }

    /// Returns an iterator over all key-value pairs within the map
    ///
    /// NOTE: This is much less efficient than using the [read_zipper](Self::read_zipper) method
    pub fn iter<'a>(&'a self) -> impl Iterator<Item=(Vec<u8>, &'a V)> + 'a {
        self.read_zipper().into_iter()
    }

    /// Returns a [crate::old_cursor::PathMapCursor] to traverse all key-value pairs within the map. This
    /// is more efficient than using [iter](Self::iter), but is not compatible with the [Iterator] trait
    ///
    /// WARNING: This API will be deprecated in favor of the [read_zipper](Self::read_zipper) method
    pub fn cursor<'a>(&'a self) -> crate::old_cursor::PathMapCursor<'a, V> {
        crate::old_cursor::PathMapCursor::new(self)
    }

    /// Returns an [crate::old_cursor::AllDenseCursor], which behaves exactly like a [crate::old_cursor::PathMapCursor],
    /// but is only available with the `all_dense_nodes` feature.  This is mainly kept for benchmarking.
    pub fn all_dense_cursor<'a>(&'a self) -> crate::old_cursor::AllDenseCursor<'a, V> {
        crate::old_cursor::AllDenseCursor::new(self)
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

//GOAT, in light of PathMap's behavior holistically an a potential collision with WriteZipper::insert_prefix,
// `insert` really should be called set_value
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

    /// Removes the value at `k` from the map and returns it, or returns None if there was no value at `k`
    pub fn remove<K: AsRef<[u8]>>(&mut self, k: K) -> Option<V> {
        let k = k.as_ref();
        //NOTE: we're descending the zipper rather than creating it at the path so it will be allowed to
        // prune the branches.  A WriteZipper can't move above its root, so it couldn't prune otherwise
        let mut zipper = self.write_zipper();
        zipper.descend_to(k);
        zipper.remove_value()
    }

    //GOAT-redo this with the WriteZipper::get_value_or_insert, although I may need an alternate function
    // that consumes the zipper in order to be allowed to return the correct lifetime
    //
    // pub fn update<K: AsRef<[u8]>, F: FnOnce()->V>(&mut self, k: K, default_f: F) -> &mut V {
    //     let k = k.as_ref();

    //     traverse_to_leaf_mut(&mut self.root, k,
    //     |node, remaining_key| node.node_update_val(remaining_key, Box::new(default_f)),
    //     |new_leaf_node, remaining_key| new_leaf_node.node_get_val_mut(remaining_key).unwrap())
    // }

    /// Returns `true` if the map is empty, otherwise returns `false`
    pub fn is_empty(&self) -> bool {
        self.root().borrow().node_is_empty()
    }

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

    /// Returns the total number of values contained within the map
    ///
    /// WARNING: This is not a cheap method. It may have an order-N cost
    pub fn val_count(&self) -> usize {
        return val_count_below_root(self.root().borrow())
    }

    /// Returns a new `BytesTrieMap` where the paths in `self` are restricted by the paths leading to 
    /// values in `other`
    pub fn restrict(&self, other: &Self) -> Self {
        match self.root().borrow().prestrict_dyn(other.root().borrow()) {
            Some(new_root) => Self::new_with_root(new_root),
            None => Self::new()
        }
    }
}

impl<V: Clone + Send + Sync, K: AsRef<[u8]>> FromIterator<(K, V)> for BytesTrieMap<V> {
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> Self {
        let mut map = Self::new();
        for (key, val) in iter {
            map.insert(key, val);
        }
        map
    }
}

impl<V: Clone + Lattice + Send + Sync> Lattice for BytesTrieMap<V> {
    fn join(&self, other: &Self) -> Self {
        Self::new_with_root(self.root().join(other.root()))
    }

    fn join_into(&mut self, other: Self) {
        if let Some(other_root) = other.into_root() {
            self.root_mut().join_into(other_root)
        }
    }

    fn meet(&self, other: &Self) -> Self {
        match self.root().meet(other.root()) {
            Some(new_root) => Self::new_with_root(new_root),
            None => Self::new()
        }
    }

    fn bottom() -> Self {
        BytesTrieMap::new()
    }
}

impl<V: Clone + Send + Sync + PartialDistributiveLattice> DistributiveLattice for BytesTrieMap<V> {
    fn subtract(&self, other: &Self) -> Self {
        Self::new_with_root(self.root().subtract(other.root()))
    }
}

impl<V: Clone + Send + Sync + PartialDistributiveLattice> PartialDistributiveLattice for BytesTrieMap<V> {
    fn psubtract(&self, other: &Self) -> Option<Self> {
        let s = self.root().subtract(other.root());
        if s.borrow().node_is_empty() { None }
        else { Some(Self::new_with_root(s)) }
    }
}

impl<V: Clone + Send + Sync> PartialQuantale for BytesTrieMap<V> {
    fn prestrict(&self, other: &Self) -> Option<Self> where Self: Sized {
        self.root().prestrict(other.root()).map(|r| Self::new_with_root(r) )
    }
}

#[cfg(test)]
mod tests {
    use crate::trie_map::*;
    use crate::ring::Lattice;

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
    fn map_remove_test() {
        let mut map = BytesTrieMap::new();
        map.insert("aaaaa", "aaaaa");
        map.insert("bbbbb", "bbbbb");
        map.insert("ccccc", "ccccc");
        map.insert("ddddd", "ddddd");
        map.insert("abbbb", "abbbb");
        map.insert("aaaab", "aaaab");
        map.insert("aaaac", "aaaac");
        map.insert("acaaa", "acaaa");
        assert_eq!(map.val_count(), 8);

        assert_eq!(map.remove(b"aaaaa"), Some("aaaaa"));
        assert_eq!(map.val_count(), 7);
        assert_eq!(map.remove(b"acaaa"), Some("acaaa"));
        assert_eq!(map.val_count(), 6);
        assert_eq!(map.remove(b"cccccnot-a-real-key"), None);
        assert_eq!(map.val_count(), 6);
        assert_eq!(map.remove(b"aaaac"), Some("aaaac"));
        assert_eq!(map.val_count(), 5);
        assert_eq!(map.remove(b"aaaab"), Some("aaaab"));
        assert_eq!(map.val_count(), 4);
        assert_eq!(map.remove(b"abbbb"), Some("abbbb"));
        assert_eq!(map.val_count(), 3);
        assert_eq!(map.remove(b"ddddd"), Some("ddddd"));
        assert_eq!(map.val_count(), 2);
        assert_eq!(map.remove(b"ccccc"), Some("ccccc"));
        assert_eq!(map.val_count(), 1);
        assert_eq!(map.remove(b"bbbbb"), Some("bbbbb"));
        assert_eq!(map.val_count(), 0);
        assert!(map.is_empty());
    }

    #[test]
    fn map_update_test() {
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let mut btm: BytesTrieMap<u64> = rs.into_iter().enumerate().map(|(i, k)| (k, i as u64)).collect();

        let mut zipper = btm.write_zipper_at_path(b"cannon");
        assert_eq!(zipper.get_value_or_insert(42), &2);
        drop(zipper);

        let mut zipper = btm.write_zipper_at_path(b"dagger");
        assert_eq!(zipper.get_value_or_insert(42), &42);
    }

    #[test]
    fn map_join_test() {
        let mut a = BytesTrieMap::<usize>::new();
        let mut b = BytesTrieMap::<usize>::new();
        let rs = ["Abbotsford", "Abbottabad", "Abcoude", "Abdul Hakim", "Abdulino", "Abdullahnagar", "Abdurahmoni Jomi", "Abejorral", "Abelardo Luz"];
        for (i, path) in rs.into_iter().enumerate() {
            if i % 2 == 0 {
                a.insert(path, i);
            } else {
                b.insert(path, i);
            }
        }

        let joined = a.join(&b);
        for (path, i) in joined.iter() {
            // println!("{} {}", std::str::from_utf8(&path).unwrap(), i);
            assert_eq!(rs[*i].as_bytes(), &path);
        }
        assert_eq!(joined.val_count(), rs.len());
    }

    #[test]
    fn cursor_test() {
        let table = ["A", "Bcdef", "Ghij", "Klmnopqrst"];
        let btm: BytesTrieMap<usize> = table.iter().enumerate().map(|(n, s)| (s, n)).collect();
        let mut cursor = btm.cursor();
        while let Some((k, v)) = cursor.next() {
            // println!("{}, {v}", std::str::from_utf8(k).unwrap());
            assert_eq!(k, table[*v].as_bytes());
        }
    }

    use std::thread::{JoinHandle, spawn};
    use std::sync::Arc;
    use crate::zipper::Zipper;
    #[test]
    fn parallel_insert_test() {

        let thread_cnt = 8;
        let elements = 1024;

        let elements_per_thread = elements / thread_cnt;

        let mut threads: Vec<JoinHandle<()>> = Vec::with_capacity(thread_cnt);
        let map = Arc::new(crate::trie_map::BytesTrieMap::<()>::new());

        //Spawn all the threads
        for n in 0..thread_cnt {
            let map_ref = map.clone();
            let thread = spawn(move || {
                //GOAT, there is currently a bug that means we need 2 unique path bytes instead of 1.
                // The reason is:
                // 1. The first byte maps to a node that is shared, so we can't modify it from code outside a critical
                //   section
                // 2. The WriteZipper currently holds a mutable reference to a node (in case the root node needs to be upgraded).
                //   That means the node the writeZipper points into cannot be accessed outside a critical section.
                //   That node maps to the second byte
                // 3. The third byte of a WriteZipper's path is on account of the fact that the WriteZipper
                //   holds a reference to the parent of the path.  This was originally done so the WriteZipper
                //   could set a value at its root.
                //   *UPDATE* Condition 3 is now addressed, but the tradeoff is that setting a root value on this type of zipper
                //   will cause a problem.
                //
                // To fix this several changes are needed.
                // 1. A WriteZipper should hold a reference to a CoFree, (or to a node and a value individually)
                // 2. We will need a special DenseNode type that wraps each CoFree in its own UnsafeCell
                // 3. maybe I can get rid of RootWrapper, since I won't need the UnsafeCell at the map root anymore,
                //  if I have one at each node.  On the other hand, if I get rid of it, then it means I need to
                //  have one of the special DenseNodes with every CoFree wrapped, at the root.
                let path = [n as u8, 255];

                let mut zipper = unsafe{ map_ref.write_zipper_at_exclusive_path_unchecked(&path) };
                for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                    zipper.descend_to(prefix_key(&(i as u64)));
                    assert!(zipper.set_value(()).is_none());
                    zipper.reset();
                }
            });
            threads.push(thread);
        };

        //Wait for them to finish
        for thread in threads {
            thread.join().unwrap();
        }

        //GOAT TODO
        // * In parallel insert test, make sure the insert did the right thing
        // * GOAT, decide what to do with root values on a zipper...

    }

    fn prefix_key(k: &u64) -> &[u8] {
        let bs = (8 - k.leading_zeros()/8) as u8;
        let kp: *const u64 = k;
        unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
    }
}
