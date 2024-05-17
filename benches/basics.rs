
use divan::{Divan, Bencher, black_box};
use ringmap::ring::*;
use ringmap::bytize::*;
use ringmap::bytetrie::BytesTrieMap;

fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(5000);

    divan.main();
}

#[divan::bench()] //Note: args can be provided like: #[divan::bench(args = [1, 2, 4, 8, 16, 32])]
fn join(bencher: Bencher) {
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

        //Benchmark the join operation
        let mut j: BytesTrieMap<u64> = BytesTrieMap::new();
        bencher.bench_local(|| {
            *black_box(&mut j) = vnl.join(black_box(&vnr));
        });

        //Sanity check that we didn't break anything and the benchmarks are valid
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
