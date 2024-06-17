pub mod ring;
pub mod bytize;
pub mod bytetrie;
pub mod zipper;
//GOAT: Make this a compile-time feature
pub mod counters;

mod dense_byte_node;
mod line_list_node;

/// returns the position of the next/previous active bit in x
/// if there is no next/previous bit, returns the argument position
/// assumes that pos is active in x
fn bit_sibling(pos: u8, x: u64, next: bool) -> u8 {
    debug_assert_ne!((1u64 << pos) & x, 0);
    if next {
        if pos == 0 { return 0 } // resolves overflow in shift
        let succ = !0u64 >> (64 - pos);
        let m = x & succ;
        if m == 0u64 { pos }
        else { (63 - m.leading_zeros()) as u8 }
    } else {
        let prec = !(!0u64 >> (63 - pos));
        let m = x & prec;
        if m == 0u64 { pos }
        else { m.trailing_zeros() as u8 }
    }
}

#[cfg(test)]
mod tests {
    use crate::bit_sibling;
    use crate::bytize::*;
    use crate::ring::*;
    use crate::bytetrie::BytesTrieMap;

    #[test]
    fn btm_prefix() {
        // from https://en.wikipedia.org/wiki/Radix_tree#/media/File:Patricia_trie.svg
        let mut btm = BytesTrieMap::new();
        let rs: Vec<&str> = vec!["romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });
//GOAT, fix this, sub_map
        // assert_eq!(btm.at("rom".as_bytes()).map(|m| m.items().collect::<HashSet<_>>()),
        //            Some(HashSet::from([("ane".as_bytes().to_vec(), &0), ("anus".as_bytes().to_vec(), &1), ("ulus".as_bytes().to_vec(), &2), ("'i".as_bytes().to_vec(), &7)])));

        let mut rz = crate::zipper::ReadZipper::new(&btm);
        rz.child('r' as u8); rz.child('o' as u8); rz.child('m' as u8); // focus = rom
        assert!(rz.child('\'' as u8)); // focus = rom'  (' is the lowest byte)
        assert!(rz.sibling(true)); // focus = roma  (a is the second byte)
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'n']]); // both follow-ups romane and romanus have n following a
        assert!(rz.sibling(true)); // focus = romu  (u is the third byte)
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'l']]); // and romu is followed by lus
        assert!(!rz.sibling(true)); // fails (u is the highest byte)
        assert!(rz.sibling(false)); // focus = roma (we can step back)
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'n']]); // again
        assert!(rz.parent()); // focus = rom
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'\''], [b'a'], [b'u']]); // all three options we visited
        assert!(rz.nth_child(0, true)); // focus = rom'
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'i']]);
        assert!(rz.parent()); // focus = rom
        assert!(rz.nth_child(1, true)); // focus = roma
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'n']]);
        assert!(rz.parent());
        assert!(rz.nth_child(2, true)); // focus = romu
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'l']]);
        assert!(rz.parent());
        assert!(rz.nth_child(1, false)); // focus = roma
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'n']]);
        assert!(rz.parent());
        assert!(rz.nth_child(2, false)); // focus = rom'
        assert_eq!(rz.focus.boxed_node_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![[b'i']]);
        // ' < a < u
        // 39 105 117
    }

    #[test]
    fn bit_siblings() {
        let x = 0b0000000000000000000000000000000000000100001001100000000000000010u64;
        let i = 0b0000000000000000000000000000000000000000000001000000000000000000u64;
        let p = 0b0000000000000000000000000000000000000000001000000000000000000000u64;
        let n = 0b0000000000000000000000000000000000000000000000100000000000000000u64;
        let f = 0b0000000000000000000000000000000000000100000000000000000000000000u64;
        let l = 0b0000000000000000000000000000000000000000000000000000000000000010u64;
        let bit_i = 18;
        let bit_i_onehot = 1u64 << bit_i;
        assert_eq!(i, bit_i_onehot);
        assert_ne!(bit_i_onehot & x, 0);
        assert_eq!(p, 1u64 << bit_sibling(bit_i, x, false));
        assert_eq!(n, 1u64 << bit_sibling(bit_i, x, true));
        assert_eq!(f, 1u64 << bit_sibling(f.trailing_zeros() as u8, x, false));
        assert_eq!(l, 1u64 << bit_sibling(l.trailing_zeros() as u8, x, true));
        assert_eq!(0, bit_sibling(0, 1, false));
        assert_eq!(0, bit_sibling(0, 1, true));
        assert_eq!(63, bit_sibling(63, 1u64 << 63, false));
        assert_eq!(63, bit_sibling(63, 1u64 << 63, true));
    }

    #[test]
    fn btm_value_only_subtract_test() {
        let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
        l.insert(b"0", 0);
        l.insert(b"1", 1);
        l.insert(b"2", 2);
        let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
        r.insert(b"1", 1);
        r.insert(b"3", 3);
        let l_no_r = l.subtract(&r);
        assert_eq!(l_no_r.get(b"0"), Some(&0));
        assert_eq!(l_no_r.get(b"1"), None);
        assert_eq!(l_no_r.get(b"2"), Some(&2));
        assert_eq!(l_no_r.get(b"3"), None);
    }

    #[test]
    fn btm_compound_tree_subtract_test() {
        let mut l: BytesTrieMap<&str> = BytesTrieMap::new();
        l.insert(b"hello", "hello");
        l.insert(b"hello world", "hello world");
        l.insert(b"hell no we won't go", "hell no we won't go");
        let mut r: BytesTrieMap<&str> = BytesTrieMap::new();
        r.insert(b"hello", "hello");
        let l_no_r = l.subtract(&r);

        assert_eq!(l_no_r.get(b"hello"), None);
        assert_eq!(l_no_r.get(b"hello world"), Some(&"hello world"));
        assert_eq!(l_no_r.get(b"hell no we won't go"), Some(&"hell no we won't go"));
    }

    #[test]
    fn btm_many_elements_subtract_test() {
        let n: u64 = 1000; //Arbitrary number of elements
        let overlap = 0.5;
        let o = ((1. - overlap) * n as f64) as u64;

        let mut vnl = BytesTrieMap::new();
        let mut vnr = BytesTrieMap::new();
        for i in 0..n { vnl.insert(prefix_key(&i), i); }
        for i in o..(n+o) { vnr.insert(prefix_key(&i), i); }
        let l_no_r = vnl.subtract(&vnr);

        //Validate the ByteTrieMap::subtract against HashSet::difference
        let vnl_set: std::collections::HashSet<Vec<u8>> = vnl.items().map(|(k, _)| k).collect();
        let vnr_set: std::collections::HashSet<Vec<u8>> = vnr.items().map(|(k, _)| k).collect();
        let mut l_no_r_set: Vec<Vec<u8>> = l_no_r.items().map(|(k, _)| k).collect();
        let mut l_no_r_ref_set: Vec<Vec<u8>> = vnl_set.difference(&vnr_set).cloned().collect();
        l_no_r_set.sort();
        l_no_r_ref_set.sort();
        assert_eq!(l_no_r_set, l_no_r_ref_set);
    }

    /// Tests values that are attached along the paths to other keys, and also tests the absence of keys
    /// after existing values.
    #[test]
    fn path_prefix_test() {
        let mut map = BytesTrieMap::<u64>::new();

        map.insert(&[0u8], 1);
        assert_eq!(map.get(&[0u8]), Some(&1));
        assert_eq!(map.get(&[0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8]), None);

        map.insert(&[0u8, 0u8, 0u8, 0u8], 4);
        assert_eq!(map.get(&[0u8]), Some(&1));
        assert_eq!(map.get(&[0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8]), Some(&4));

        map.insert(&[0u8, 0u8, 0u8, 0u8, 0u8], 5);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8]), Some(&4));
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8]), Some(&5));

        map.insert(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], 9);
        assert_eq!(map.get(&[0u8]), Some(&1));
        assert_eq!(map.get(&[0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8]), Some(&4));
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8]), Some(&5));
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), Some(&9));
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), None);
    }

    #[test]
    fn btm_ops_test() {
        for n in (0..5000).into_iter().step_by(97) {
            // println!("n={n}");

            let overlap = 0.5;
            let o = ((1. - overlap) * n as f64) as u64;
            {
                let mut vnl = BytesTrieMap::new();
                let mut vnr = BytesTrieMap::new();
                for i in 0..n { vnl.insert(prefix_key(&i), i); }
                // println!("{:?}", vnl.root);
                for i in 0..n { assert_eq!(vnl.get(prefix_key(&i)), Some(i).as_ref()); }
                for i in n..2*n { assert_eq!(vnl.get(prefix_key(&i)), None); }
                let mut c: Vec<u64> = Vec::with_capacity(n as usize);
                vnl.items().for_each(|(k, v)| {
                    assert!(*v < n);
                    assert_eq!(k, prefix_key(&v));
                    c.push(from_prefix_key(k.clone()));
                });
                c.sort();
                assert_eq!(c, (0..n).collect::<Vec<u64>>());
                for i in o..(n+o) { vnr.insert(prefix_key(&i), i); }

                let j: BytesTrieMap<u64> = vnl.join(&vnr);
                let m = vnl.meet(&vnr);
                let l_no_r = vnl.subtract(&vnr);

                for i in 0..o { assert_eq!(l_no_r.get(prefix_key(&i)), vnl.get(prefix_key(&i))); }
                for i in o..(n+o) { assert!(!l_no_r.contains(prefix_key(&i))); }

                for i in o..n { assert!(vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i))); }
                for i in 0..o { assert!(vnl.contains(prefix_key(&i)) && !vnr.contains(prefix_key(&i))); }
                for i in n..(n+o) { assert!(!vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i))); }
                for i in 0..(2*n) { assert_eq!(j.contains(prefix_key(&i)), (vnl.contains(prefix_key(&i)) || vnr.contains(prefix_key(&i)))); }
                for i in 0..(2*n) { assert_eq!(m.contains(prefix_key(&i)), (vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i)))); }
                for i in 0..(n+o) { assert_eq!(j.get(prefix_key(&i)), vnl.get(prefix_key(&i)).join(&vnr.get(prefix_key(&i)))); }
                for i in o..n { assert_eq!(m.get(prefix_key(&i)), vnl.get(prefix_key(&i)).meet(&vnr.get(prefix_key(&i)))); }
                // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains(i), vnl.contains(i), vnr.contains(i)); } // assert!(r.contains(i));
            }
        }
    }

    #[test]
    fn btm_cursor_test() {
        let table = ["A", "Bcdef", "Ghij", "Klmnopqrst"];
        let btm: BytesTrieMap<usize> = table.iter().enumerate().map(|(n, s)| (s, n)).collect();
        let mut cursor = btm.item_cursor();
        while let Some((k, v)) = cursor.next() {
            // println!("{}, {v}", std::str::from_utf8(k).unwrap());
            assert_eq!(k, table[*v].as_bytes());
        }
    }
}
