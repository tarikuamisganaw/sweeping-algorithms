
use crate::trie_map::BytesTrieMap;
use crate::trie_node::*;
use crate::zipper::*;
use zipper_priv::*;

/// A [Zipper] type that moves through a space created by extending each value at the end of a path in a
/// primary space with the root of a secondardary space, and doing it recursively for as many spaces as
/// needed
///
/// WARNING: This zipper treats any value in an "outer" factor zipper's trie as a marker to jump to the
/// next zipper's trie.  However, the `descend_to` method will jump over values except for the leaf value.
/// This is a non-issue if the trie only contains values intended as "stitching" points, but will otherwise
/// lead to strange-seeming behavior.
///
/// WHY IS THIS API EXPERIMENTAL?  A: Because the zipper appears to create a new space for the purposes
/// of zipper movement, but the space is an ephemeral projection.  Unlike other space operations, if
/// the user tried to graft this space or materialize it into a map, they would get something that
/// would not match their expectations.
///
/// A more holistic way of performing this kind of transformation is likely desirable, but that has a
/// number of unexplored complications such as the impact to exclusivity (is this de-facto aliasing?)
/// and how the linkages could be parameterized after-the-fact, or re-parameterized en masse (without
/// visiting each node), or when the parameters could be changed and when they would be fixed.
pub struct ProductZipper<'factor_z, 'trie, V> {
    z: read_zipper_core::ReadZipperCore<'trie, 'static, V>,
    secondaries: Vec<TrieRef<'trie, V>>,
    factor_paths: Vec<usize>,
    /// We need to hang onto the zippers for the life of this object, so their trackers stay alive
    source_zippers: Vec<Box<dyn zipper_priv::ZipperReadOnlyPriv<'trie, V> + 'factor_z>>
}

impl<'factor_z, 'trie, V: Clone + Send + Sync + Unpin> ProductZipper<'factor_z, 'trie, V> {
    /// Creates a new `ProductZipper` from the provided zippers
    ///
    /// WARNING: passing `other_zippers` that are not at node roots may lead to a panic.  This is
    /// an implementation issue, but would be very difficult to fix and may not be worth fixing.
    pub fn new<PrimaryZ, OtherZ, ZipperList>(mut primary_z: PrimaryZ, other_zippers: ZipperList) -> Self
        where
        PrimaryZ: ZipperMoving + ZipperReadOnly<'trie, V> + 'factor_z,
        OtherZ: ZipperReadOnly<'trie, V> + 'factor_z,
        ZipperList: IntoIterator<Item=OtherZ>,
    {
        let other_z_iter = other_zippers.into_iter();
        let (mut secondaries, mut source_zippers) = match other_z_iter.size_hint() {
            (_, Some(hint)) => (Vec::with_capacity(hint), Vec::with_capacity(hint+1)),
            (_, None) => (Vec::new(), Vec::new())
        };

        //Get the core out of the primary zipper
        //This unwrap won't fail because all the types that implement `ZipperMoving` have cores
        let core_z = primary_z.take_core().unwrap();
        source_zippers.push(Box::new(primary_z) as Box<dyn zipper_priv::ZipperReadOnlyPriv<V>>);

        //Get TrieRefs for the remaining zippers
        for other_z in other_z_iter {
            let trie_ref = other_z.trie_ref_at_path("");
            secondaries.push(trie_ref);
            source_zippers.push(Box::new(other_z));
        }

        Self{z: core_z, factor_paths: Vec::with_capacity(secondaries.len()), secondaries, source_zippers}
    }
    /// Creates a new `ProductZipper` from a single zipper, with the expectation that more zippers
    /// will be added using [new_factor]
    pub fn new_with_primary<PrimaryZ>(mut primary_z: PrimaryZ) -> Self
        where PrimaryZ: ZipperMoving + ZipperReadOnly<'trie, V> + 'factor_z,
    {
        let mut source_zippers = Vec::new();

        //Get the core out of the primary zipper
        //This unwrap won't fail because all the types that implement `ZipperMoving` have cores
        let core_z = primary_z.take_core().unwrap();
        source_zippers.push(Box::new(primary_z) as Box<dyn zipper_priv::ZipperReadOnlyPriv<V>>);

        Self{z: core_z, factor_paths: Vec::new(), secondaries: vec![], source_zippers}
    }
    /// Appends additional factors to a `ProductZipper`.  This is useful when dealing with
    /// factor zippers of different types
    ///
    /// WARNING: the same warning as above applies about passing other zippers that aren't at node roots
    pub fn new_factors<OtherZ, ZipperList>(&mut self, other_zippers: ZipperList)
        where
        OtherZ: ZipperReadOnly<'trie, V> + 'factor_z,
        ZipperList: IntoIterator<Item=OtherZ>,
    {
        let other_z_iter = other_zippers.into_iter();
        for other_z in other_z_iter {
            let trie_ref = other_z.trie_ref_at_path("");
            self.secondaries.push(trie_ref);
            self.source_zippers.push(Box::new(other_z));
        }
    }
    /// Internal method to descend across the boundary between two factor zippers if the focus is on a value
    #[inline]
    fn ensure_descend_next_factor(&mut self) {
        if self.z.is_value() && self.factor_paths.len() < self.secondaries.len() {
            //If there is a `_secondary_root_val`, it lands at the same path as the value where the
            // paths are joined.  And the value from the earlier zipper takes precedence
            let (secondary_root, partial_path, _secondary_root_val) = self.secondaries[self.factor_paths.len()].borrow_raw_parts();

            //TODO! Dealing with hidden root path in a secondary factor is very nasty.  I'm going to punt
            // on handling this until we move this feature out of the experimental stage.
            //See "WARNING" in ProductZipper creation methods
            assert_eq!(partial_path.len(), 0);

            self.z.push_node(secondary_root.as_tagged());
            self.factor_paths.push(self.path().len());
        }
    }
    /// Internal method to make sure `self.factor_paths` is correct after an ascend method
    #[inline]
    fn fix_after_ascend(&mut self) {
        while let Some(factor_path_start) = self.factor_paths.last() {
            if self.z.path().len() < *factor_path_start {
                self.factor_paths.pop();
            } else {
                break
            }
        }
    }
}

impl<V: Clone + Send + Sync + Unpin> ZipperMoving for ProductZipper<'_, '_, V> {
    fn at_root(&self) -> bool {
        self.path().len() == 0
    }
    fn reset(&mut self) {
        self.factor_paths.clear();
        self.z.reset()
    }
    #[inline]
    fn path(&self) -> &[u8] {
        self.z.path()
    }
    fn val_count(&self) -> usize {
        //GOAT!!!  I think val_count properly belongs in the morphisms module
        unimplemented!()
    }
    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) -> bool {
        let k = k.as_ref();
        let starting_path_len = self.path().len();
        // Descend the full path; we might overshoot this factor
        if self.z.descend_to(k) {
            // We didn't overshoot, so we can return.
            true
        } else {
            // Ascend up to the deepest value along this path, in the current factor
            while !self.z.is_value() {
                if !self.z.ascend_until() {
                    break
                }
            }

            // Even though we had to backtrack, we must still be at or below where we started
            debug_assert!(self.path().len() >= starting_path_len);

            // Construct the part of the path yet-to-be descended
            let remaining_path_start = self.path().len() - starting_path_len;
            let remaining_path = &k[remaining_path_start..];

            // Add the next factor, if there is one
            self.ensure_descend_next_factor();

            //Recursively re-descend within this factor
            self.z.descend_to(remaining_path)
        }
    }
    fn descend_to_byte(&mut self, k: u8) -> bool {
        self.descend_to(&[k])
    }
    fn descend_indexed_branch(&mut self, child_idx: usize) -> bool {
        self.ensure_descend_next_factor();
        self.z.descend_indexed_branch(child_idx)
    }
    fn descend_first_byte(&mut self) -> bool {
        self.ensure_descend_next_factor();
        self.z.descend_first_byte()
    }
    fn descend_until(&mut self) -> bool {
        self.ensure_descend_next_factor();
        self.z.descend_until()
    }
    fn to_sibling(&mut self, next: bool) -> bool {
        self.ensure_descend_next_factor();
        let moved = self.z.to_sibling(next);
        self.fix_after_ascend();
        moved
    }
    fn to_next_sibling_byte(&mut self) -> bool {
        self.ensure_descend_next_factor();
        let moved = self.z.to_next_sibling_byte();
        self.fix_after_ascend();
        moved
    }
    fn to_prev_sibling_byte(&mut self) -> bool {
        self.to_sibling(false)
    }
    fn ascend(&mut self, steps: usize) -> bool {
        let ascended = self.z.ascend(steps);
        self.fix_after_ascend();
        ascended
    }
    fn ascend_byte(&mut self) -> bool {
        self.ascend(1)
    }
    fn ascend_until(&mut self) -> bool {
        let ascended = self.z.ascend_until();
        self.fix_after_ascend();
        ascended
    }
    fn ascend_until_branch(&mut self) -> bool {
        let ascended = self.z.ascend_until_branch();
        self.fix_after_ascend();
        ascended
    }
}

impl<'factor_z, 'trie, V: Clone + Send + Sync + Unpin> ZipperReadOnly<'trie, V> for ProductZipper<'factor_z, 'trie, V>{
    fn get_value(&self) -> Option<&'trie V> { self.z.get_value() }
    fn trie_ref_at_path<K: AsRef<[u8]>>(&self, path: K) -> TrieRef<'trie, V> { self.z.trie_ref_at_path(path) }
}

impl<'factor_z, 'trie, V: Clone + Send + Sync + Unpin> zipper_priv::ZipperReadOnlyPriv<'trie, V> for ProductZipper<'factor_z, 'trie, V> {
    fn borrow_raw_parts<'z>(&'z self) -> (&'trie dyn TrieNode<V>, &'z [u8], Option<&'trie V>) {
        panic!("Making a product zipper from another product zipper no supported.  Use `new_factors` instead.");
    }
    fn take_core(&mut self) -> Option<read_zipper_core::ReadZipperCore<'trie, 'static, V>> {
        panic!("Making a product zipper from another product zipper no supported.  Use `new_factors` instead.");
    }
}

impl<V: Clone + Send + Sync + Unpin> Zipper<V> for ProductZipper<'_, '_, V> {
    type ReadZipperT<'a> = () where Self: 'a;
    fn path_exists(&self) -> bool {
        self.z.path_exists()
    }
    fn value(&self) -> Option<&V> {
        self.z.get_value()
    }
    fn is_value(&self) -> bool {
        self.z.is_value()
    }
    fn child_count(&self) -> usize {
        if self.z.is_value() && self.factor_paths.len() < self.secondaries.len() {
            self.secondaries[self.factor_paths.len()].child_count()
        } else {
            self.z.child_count()
        }
    }
    fn child_mask(&self) -> [u64; 4] {
        if self.z.is_value() && self.factor_paths.len() < self.secondaries.len() {
            self.secondaries[self.factor_paths.len()].child_mask()
        } else {
            self.z.child_mask()
        }
    }
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a> {
        panic!("This won't do what you want it to do.");
    }
    fn make_map(&self) -> Option<BytesTrieMap<Self::V>> {
        panic!("This won't do what you want it to do.");
    }
}

impl<V: Clone + Send + Sync> zipper_priv::ZipperPriv for ProductZipper<'_, '_, V> {
    type V = V;

    fn get_focus(&self) -> AbstractNodeRef<Self::V> { self.z.get_focus() }
    fn try_borrow_focus(&self) -> Option<&dyn TrieNode<Self::V>> { self.z.try_borrow_focus() }
}

impl<V: Clone + Send + Sync> zipper_priv::ZipperMovingPriv for ProductZipper<'_, '_, V> {
    unsafe fn origin_path_assert_len(&self, len: usize) -> &[u8] { unsafe{ self.z.origin_path_assert_len(len) } }
    fn prepare_buffers(&mut self) { self.z.prepare_buffers() }
}

impl<V: Clone + Send + Sync + Unpin> ZipperAbsolutePath for ProductZipper<'_, '_, V> {
    fn origin_path(&self) -> Option<&[u8]> { self.z.origin_path() }
    fn root_prefix_path(&self) -> Option<&[u8]> { self.z.root_prefix_path() }
}

#[cfg(test)]
mod tests {
    use crate::zipper::*;
    use crate::trie_map::BytesTrieMap;
    use crate::experimental::ProductZipper;
    use crate::morphisms::Catamorphism;

    #[test]
    fn product_zipper_test1() {
        let keys = [b"AAa", b"AAb", b"AAc"];
        let keys2 = [b"DDd", b"EEe", b"FFf"];
        let map: BytesTrieMap<u64> = keys.into_iter().enumerate().map(|(i, v)| (v, i as u64)).collect();
        let map2: BytesTrieMap<u64> = keys2.into_iter().enumerate().map(|(i, v)| (v, (i + 1000) as u64)).collect();

        //Make a "trie-squared" product zipper
        let rz = map.read_zipper();
        let mut pz = ProductZipper::new(rz, [map2.read_zipper()]);

        //Descend within the first factor
        assert!(pz.descend_to(b"AA"));
        assert_eq!(pz.path(), b"AA");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 3);
        assert!(pz.descend_to(b"a"));
        assert_eq!(pz.path(), b"AAa");
        assert_eq!(pz.get_value(), Some(&0));
        assert_eq!(pz.child_count(), 3);

        //Step to the next factor
        assert!(pz.descend_to(b"DD"));
        assert_eq!(pz.path(), b"AAaDD");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 1);
        assert!(pz.descend_to(b"d"));
        assert_eq!(pz.path(), b"AAaDDd");
        assert_eq!(pz.get_value(), Some(&1000));
        assert_eq!(pz.child_count(), 0);
        assert!(!pz.descend_to(b"GGg"));
        assert_eq!(pz.path(), b"AAaDDdGGg");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 0);

        //Test Reset, if the zipper was in another factor
        pz.reset();
        assert_eq!(pz.path(), b"");
        assert!(pz.descend_to(b"AA"));
        assert_eq!(pz.path(), b"AA");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 3);

        //Try to descend to a non-existent path that would be within the first factor
        assert!(!pz.descend_to(b"aBBb"));
        assert_eq!(pz.path(), b"AAaBBb");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 0);

        //Now descend to the second factor in one jump
        pz.reset();
        assert!(pz.descend_to(b"AAaDD"));
        assert_eq!(pz.path(), b"AAaDD");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 1);
        pz.reset();
        assert!(pz.descend_to(b"AAaDDd"));
        assert_eq!(pz.path(), b"AAaDDd");
        assert_eq!(pz.get_value(), Some(&1000));
        assert_eq!(pz.child_count(), 0);
        assert!(!pz.descend_to(b"GG"));
        assert_eq!(pz.path(), b"AAaDDdGG");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 0);

        //Make sure we can ascend out of a secondary factor; in this sub-test we'll hit the path middles
        assert!(pz.ascend(1));
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.path(), b"AAaDDdG");
        assert_eq!(pz.child_count(), 0);
        assert!(pz.ascend(3));
        assert_eq!(pz.path(), b"AAaD");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 1);
        assert!(pz.ascend(2));
        assert_eq!(pz.path(), b"AA");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 3);
        assert!(!pz.ascend(3));
        assert_eq!(pz.path(), b"");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 1);
        assert!(pz.at_root());

        assert!(!pz.descend_to(b"AAaDDdGG"));
        assert_eq!(pz.path(), b"AAaDDdGG");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 0);

        //Now try to hit the path transition points
        assert!(pz.ascend(2));
        assert_eq!(pz.path(), b"AAaDDd");
        assert_eq!(pz.get_value(), Some(&1000));
        assert_eq!(pz.child_count(), 0);
        assert!(pz.ascend(3));
        assert_eq!(pz.path(), b"AAa");
        assert_eq!(pz.get_value(), Some(&0));
        assert_eq!(pz.child_count(), 3);
        assert!(pz.ascend(3));
        assert_eq!(pz.path(), b"");
        assert_eq!(pz.get_value(), None);
        assert_eq!(pz.child_count(), 1);
        assert!(pz.at_root());
    }

    #[test]
    fn product_zipper_test2() {
        let lpaths = ["abcdefghijklmnopqrstuvwxyz".as_bytes(), "arrow".as_bytes(), "x".as_bytes(), "arr".as_bytes()];
        let rpaths = ["ABCDEFGHIJKLMNOPQRSTUVWXYZ".as_bytes(), "a".as_bytes(), "bow".as_bytes(), "bo".as_bytes()];
        let epaths = ["foo".as_bytes(), "pho".as_bytes(), "f".as_bytes()];
        let l = BytesTrieMap::from_iter(lpaths.iter().map(|x| (x, ())));
        let r = BytesTrieMap::from_iter(rpaths.iter().map(|x| (x, ())));
        let e = BytesTrieMap::from_iter(epaths.iter().map(|x| (x, ())));
        let mut p = ProductZipper::new(l.read_zipper(), [r.read_zipper(), e.read_zipper()]);

        let paths: Vec<Vec<u8>> = vec![];
        let paths_ptr = (&paths) as *const Vec<Vec<u8>>;
        unsafe {
        p.into_cata_side_effect(
            |_, p| { paths_ptr.cast_mut().as_mut().unwrap().push(p.to_vec()); },
            |_, _, p| { paths_ptr.cast_mut().as_mut().unwrap().push(p.to_vec()); },
            |_, _, _| ());
        }
        for p in paths {
            println!("{:?}", std::str::from_utf8(&p[..]).unwrap());
        }
    }

    #[test]
    fn product_zipper_test2_nested() {
        let lpaths = ["abcdefghijklmnopqrstuvwxyz".as_bytes(), "arrow".as_bytes(), "x".as_bytes(), "arr".as_bytes()];
        let rpaths = ["ABCDEFGHIJKLMNOPQRSTUVWXYZ".as_bytes(), "a".as_bytes(), "bow".as_bytes(), "bo".as_bytes()];
        let epaths = ["foo".as_bytes(), "pho".as_bytes(), "f".as_bytes()];
        let l = BytesTrieMap::from_iter(lpaths.iter().map(|x| (x, ())));
        let r = BytesTrieMap::from_iter(rpaths.iter().map(|x| (x, ())));
        let e = BytesTrieMap::from_iter(epaths.iter().map(|x| (x, ())));
        let mut p = ProductZipper::new(l.read_zipper(), [ProductZipper::new(r.read_zipper(), [e.read_zipper()])]);

        let paths: Vec<Vec<u8>> = vec![];
        let paths_ptr = (&paths) as *const Vec<Vec<u8>>;
        unsafe {
            p.into_cata_side_effect(
                |_, p| { paths_ptr.cast_mut().as_mut().unwrap().push(p.to_vec()); },
                |_, _, p| { paths_ptr.cast_mut().as_mut().unwrap().push(p.to_vec()); },
                |_, _, _| ());
        }
        for p in paths {
            println!("{:?}", std::str::from_utf8(&p[..]).unwrap());
        }
    }
}
