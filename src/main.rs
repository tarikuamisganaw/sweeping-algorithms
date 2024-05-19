use std::time::Instant;
use ringmap::ring::*;
use ringmap::bytize::*;
use ringmap::bytetrie::BytesTrieMap;


fn main() {
    const N: u64 = 1000;
    let overlap = 0.5;
    let o = ((1. - overlap) * N as f64) as u64;
    {
        let mut vnl = BytesTrieMap::new();
        let mut vnr = BytesTrieMap::new();
        for i in 0..N { vnl.insert(prefix_key(&i), i); }
        // println!("{:?}", vnl.root);
        for i in 0..N { assert_eq!(vnl.get(prefix_key(&i)), Some(i).as_ref()); }
        for i in N..2*N { assert_eq!(vnl.get(prefix_key(&i)), None); }
        let mut c: Vec<u64> = Vec::with_capacity(N as usize);
        vnl.items().for_each(|(k, v)| {
            assert!(*v < N);
            assert_eq!(k, prefix_key(&v));
            c.push(from_prefix_key(k.clone()));
        });
        c.sort();
        assert_eq!(c, (0..N).collect::<Vec<u64>>());
        for i in o..(N+o) { vnr.insert(prefix_key(&i), i); }

        let t0 = Instant::now();
        let j = vnl.join(&vnr);
        // 8, 7, 5, 5, 4
        println!("{}", t0.elapsed().as_nanos() as f64/N as f64);
        let m = vnl.meet(&vnr);
        let l_no_r = vnl.subtract(&vnr);
        for i in 0..N { assert_eq!(l_no_r.get(prefix_key(&i)), vnl.get(prefix_key(&i))); }
        for i in N..(2*N) { assert!(!l_no_r.contains(prefix_key(&i))); }

        for i in o..N { assert!(vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i))); }
        for i in 0..o { assert!(vnl.contains(prefix_key(&i)) && !vnr.contains(prefix_key(&i))); }
        for i in N..(N+o) { assert!(!vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i))); }
        for i in 0..(2*N) { assert_eq!(j.contains(prefix_key(&i)), (vnl.contains(prefix_key(&i)) || vnr.contains(prefix_key(&i)))); }
        for i in 0..(2*N) { assert_eq!(m.contains(prefix_key(&i)), (vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i)))); }
        for i in 0..(N+o) { assert_eq!(j.get(prefix_key(&i)), vnl.get(prefix_key(&i)).join(&vnr.get(prefix_key(&i)))); }
        for i in o..N { assert_eq!(m.get(prefix_key(&i)), vnl.get(prefix_key(&i)).meet(&vnr.get(prefix_key(&i)))); }
        // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains(i), vnl.contains(i), vnr.contains(i)); } // assert!(r.contains(i));
    }
}
