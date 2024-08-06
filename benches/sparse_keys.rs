
use rand::{Rng, SeedableRng, rngs::StdRng};
use divan::{Divan, Bencher, black_box};

use ringmap::ring::*;
use ringmap::trie_map::BytesTrieMap;

fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(4000);

    divan.main();
}

#[divan::bench(sample_size = 1, args = [50, 100, 200, 400, 800, 1600])]
fn sparse_insert(bencher: Bencher, n: u64) {

    let mut r = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
    }).collect();

    //Benchmark the insert operation
    let out = bencher.with_inputs(|| {
        BytesTrieMap::new()
    }).bench_local_values(|mut map| {
        for i in 0..n { black_box(&mut map).insert(&keys[i as usize], i); }
        map //Return the map so we don't drop it inside the timing loop
    });
    divan::black_box_drop(out)
}

#[divan::bench(sample_size = 1, args = [50, 100, 200, 400, 800, 1600])]
fn sparse_drop_bench(bencher: Bencher, n: u64) {

    let mut r = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
    }).collect();

    //Benchmark the time taken to drop the map
    bencher.with_inputs(|| {
        let mut map = BytesTrieMap::new();
        for i in 0..n { map.insert(&keys[i as usize], i); }
        map
    }).bench_local_values(|map| {
        drop(map);
    });
}

#[divan::bench(args = [250, 500, 1000, 2000, 4000, 8000])]
fn sparse_get(bencher: Bencher, n: u64) {

    let mut r = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
    }).collect();

    let mut map: BytesTrieMap<u64> = BytesTrieMap::new();
    for i in 0..n { map.insert(&keys[i as usize], i); }

    //Benchmark the get operation
    bencher.bench_local(|| {
        for i in 0..n {
            assert_eq!(map.get(&keys[i as usize]), Some(&i));
        }
    });
}

#[divan::bench(args = [125, 250, 500, 1000, 2000, 4000])]
fn sparse_val_count_bench(bencher: Bencher, n: u64) {

    let mut r = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
    }).collect();

    let mut map: BytesTrieMap<u64> = BytesTrieMap::new();
    for i in 0..n { map.insert(&keys[i as usize], i); }

    //Benchmark the time taken to count the number of values in the map
    let mut sink = 0;
    bencher.bench_local(|| {
        *black_box(&mut sink) = map.val_count()
    });
    assert_eq!(sink, n as usize);
}

#[divan::bench(args = [50, 100, 200, 400, 800, 1600])]
fn sparse_meet(bencher: Bencher, n: u64) {
    let overlap = 0.5;
    let o = ((1. - overlap) * n as f64) as u64;

    let mut rng = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n+o).into_iter().map(|_| {
        let len = (rng.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| rng.gen::<u8>()).collect()
    }).collect();

    let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
    for i in 0..n { l.insert(&keys[i as usize], i); }
    let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
    for i in o..(n+o) { r.insert(&keys[i as usize], i); }

    let mut intersection: BytesTrieMap<u64> = BytesTrieMap::new();
    bencher.bench_local(|| {
        *black_box(&mut intersection) = l.meet(black_box(&r));
    });
}

/// This tests the performance of the meet op when there are already some shared nodes between the maps
#[divan::bench(args = [500, 1000, 2000, 4000, 8000, 16000])]
fn sparse_meet_after_join(bencher: Bencher, n: u64) {

    let mut rng = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (rng.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| rng.gen::<u8>()).collect()
    }).collect();

    let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
    for i in 0..(n/2) { l.insert(&keys[i as usize], i); }
    let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
    for i in (n/2)..n { r.insert(&keys[i as usize], i); }

    let joined = l.join(&r);
    let mut intersection: BytesTrieMap<u64> = BytesTrieMap::new();
    bencher.bench_local(|| {
        *black_box(&mut intersection) = joined.meet(black_box(&l));
    });
}

/// This tests the performance of the meet op when there are already some shared nodes between the maps
#[divan::bench(args = [500, 1000, 2000, 4000, 8000, 16000])]
fn sparse_subtract_after_join(bencher: Bencher, n: u64) {

    let mut rng = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (rng.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| rng.gen::<u8>()).collect()
    }).collect();

    let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
    for i in 0..(n/2) { l.insert(&keys[i as usize], i); }
    let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
    for i in (n/2)..n { r.insert(&keys[i as usize], i); }

    let joined = l.join(&r);
    let mut remaining: BytesTrieMap<u64> = BytesTrieMap::new();
    bencher.bench_local(|| {
        *black_box(&mut remaining) = joined.subtract(black_box(&r));
    });
    assert_eq!(remaining.val_count(), l.val_count())
}

#[divan::bench(args = [50, 100, 200, 400, 800, 1600])]
fn sparse_cursor(bencher: Bencher, n: u64) {

    let mut r = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
    }).collect();
    let map: BytesTrieMap<usize> = keys.iter().enumerate().map(|(n, s)| (s, n)).collect();

    //Benchmark the iterator
    let mut sink = 0;
    bencher.bench_local(|| {
        let mut cursor = map.cursor();
        while let Some((_key, val)) = cursor.next() {
            *black_box(&mut sink) = *val
        }
    });
}

#[divan::bench(args = [50, 100, 200, 400, 800, 1600])]
fn sparse_zipper_cursor(bencher: Bencher, n: u64) {

    let mut r = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
    }).collect();
    let map: BytesTrieMap<usize> = keys.iter().enumerate().map(|(n, s)| (s, n)).collect();

    //Benchmark the zipper's iterator
    let mut sink = 0;
    bencher.bench_local(|| {
        let mut zipper = map.read_zipper();
        while let Some(val) = zipper.to_next_val() {
            *black_box(&mut sink) = *val
        }
    });
}

#[divan::bench(args = [10, 20, 40, 80, 160, 320])]
fn sparse_iter(bencher: Bencher, n: u64) {

    let mut r = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..n).into_iter().map(|_| {
        let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
    }).collect();
    let map: BytesTrieMap<usize> = keys.iter().enumerate().map(|(n, s)| (s, n)).collect();

    //Benchmark the iterator
    let mut sink = 0;
    bencher.bench_local(|| {
        map.iter().for_each(|(_key, val)| *black_box(&mut sink) = *val);
    });
}

#[divan::bench(sample_size = 1, args = [50, 100, 200, 400, 800, 1600])]
fn join_sparse(bencher: Bencher, n: u64) {

    let overlap = 0.5;
    let o = ((1. - overlap) * n as f64) as u64;

    let mut r = StdRng::seed_from_u64(1);
    let keys: Vec<Vec<u8>> = (0..(n+o)).into_iter().map(|_| {
        let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
        (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
    }).collect();

    let mut vnl = BytesTrieMap::new();
    let mut vnr = BytesTrieMap::new();
    for i in 0..n { vnl.insert(&keys[i as usize], i); }
    for i in o..(n+o) { vnr.insert(&keys[i as usize], i); }

    //Benchmark the join operation
    let mut j: BytesTrieMap<u64> = BytesTrieMap::new();
    bencher.bench_local(|| {
        *black_box(&mut j) = vnl.join(black_box(&vnr));
    });
}

//GOAT probably going to deprecate the join_into API
// #[divan::bench(sample_size = 1, args = [50, 100, 200, 400, 800, 1600])]
// fn join_into_sparse(bencher: Bencher, n: u64) {

//     let overlap = 0.5;
//     let o = ((1. - overlap) * n as f64) as u64;

//     let mut r = StdRng::seed_from_u64(1);
//     let keys: Vec<Vec<u8>> = (0..(n+o)).into_iter().map(|_| {
//         let len = (r.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
//         (0..len).into_iter().map(|_| r.gen::<u8>()).collect()
//     }).collect();

//     //Benchmark the join_into operation
//     bencher.with_inputs(|| {
//         let mut vnl = BytesTrieMap::new();
//         let mut vnr = BytesTrieMap::new();
//         for i in 0..n { vnl.insert(&keys[i as usize], i); }
//         for i in o..(n+o) { vnr.insert(&keys[i as usize], i); }
//         (vnl, vnr)
//     }).bench_local_values(|(mut left, right)| {
//         left.join_into(right);
//         left
//     });
// }
