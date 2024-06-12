
use divan::{Divan, Bencher, black_box};
use ringmap::bytetrie::BytesTrieMap;
use ringmap::bytetrie::STATS;

use std::fs::File;
use std::io::prelude::*;
use std::io::BufReader;

fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(5);

    divan.main();
}

/// Call with `as_words == true` for a separate entry for each word, pass false for an entry for each sentence (clause)
fn read_data(as_words: bool) -> Vec<String> {

    //The complete works of Shakespeare can be downloaded as a single file here:
    // https://ocw.mit.edu/ans7870/6/6.006/s08/lecturenotes/files/t8.shakespeare.txt
    // ~200k clauses
    // ~900k words
    let file = File::open("/Users/admin/Desktop/t8.shakespeare.txt").unwrap();

    //Parse the file, with each sentence clause as an expression
    let mut reader = BufReader::new(file);
    let mut line = String::new();
    let mut strings = vec![];
    while reader.read_line(&mut line).unwrap() > 0 {

        const TERMINATORS: &[char] = &[',', '.', ';', '?', '\"', '-', '[', ']'];
        const SEPARATORS: &[char] = &[' ', '\t', '\n'];
        const IGNORE_CHARS: &[char] = &['\''];

        for clause in line.split_inclusive(TERMINATORS) {
            if as_words {
                for sym in clause.split(SEPARATORS) {
                    let ignore_chars = [TERMINATORS, IGNORE_CHARS].concat();
                    let sym = sym.replace(&ignore_chars[..], "");

                    if sym.len() > 0 {
                        strings.push(sym);
                    }
                }
            } else {
                strings.push(clause.to_owned());
            }
        }
        line.clear();
    }

    strings
}

#[divan::bench()]
fn shakespeare_words_insert(bencher: Bencher) {

    let strings = read_data(true);

    bencher.bench_local(|| {
        let mut map = BytesTrieMap::new();
        for (v, k) in strings.iter().enumerate() {
            map.insert(k, v);
        }
    });
}

#[divan::bench()]
fn shakespeare_words_get(bencher: Bencher) {

    let strings = read_data(true);
    let mut map = BytesTrieMap::new();
    for (v, k) in strings.iter().enumerate() {
        map.insert(k, v);
    }

    // STATS.reset();
    // map.items().last();
    // println!("nodes: {}, items: {}, avg children-per-node: {}", STATS.total_nodes(), STATS.total_child_items(), STATS.total_child_items() as f32 / STATS.total_nodes() as f32);

    let mut _map_v = 0;
    bencher.bench_local(|| {
        for k in strings.iter() {
            *black_box(&mut _map_v) = *map.get(k).unwrap();
            //Annoyingly, we can't check for the correct value because so many places share a name
            //assert_eq!(map.get(k), Some(&v));
        }
    });
}

#[divan::bench()]
fn shakespeare_sentences_insert(bencher: Bencher) {

    let strings = read_data(false);

    bencher.bench_local(|| {
        let mut map = BytesTrieMap::new();
        for (v, k) in strings.iter().enumerate() {
            map.insert(k, v);
        }
    });
}

#[divan::bench()]
fn shakespeare_sentences_get(bencher: Bencher) {

    let strings = read_data(false);
    let mut map = BytesTrieMap::new();
    for (v, k) in strings.iter().enumerate() {
        map.insert(k, v);
    }

    // STATS.reset();
    // map.items().last();
    // println!("nodes: {}, items: {}, avg children-per-node: {}", STATS.total_nodes(), STATS.total_child_items(), STATS.total_child_items() as f32 / STATS.total_nodes() as f32);

    let mut _map_v = 0;
    bencher.bench_local(|| {
        for k in strings.iter() {
            *black_box(&mut _map_v) = *map.get(k).unwrap();
            //Annoyingly, we can't check for the correct value because so many places share a name
            //assert_eq!(map.get(k), Some(&v));
        }
    });
}

