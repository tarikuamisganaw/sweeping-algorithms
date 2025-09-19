use pathmap::PathMap;
use pathmap::morphisms::Catamorphism;
use pathmap::zipper::Zipper;
use std::collections::{BinaryHeap, HashMap};
use std::convert::Infallible;

/// A chunk = prefix + list of atom names under it
#[derive(Clone)]
struct Chunk {
    prefix: Vec<u8>,
    atoms: Vec<String>,
    index: usize, // how many atoms we've already visited
}

/// Wrap chunk with score for priority queue
#[derive(Clone)]
struct ScoredChunk {
    score: usize, // number of atoms left (s(c) = atoms left in c)
    chunk: Chunk,
}

// Max-heap ordering: highest score first
impl Ord for ScoredChunk {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.score.cmp(&other.score)
    }
}
impl PartialOrd for ScoredChunk {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq for ScoredChunk {
    fn eq(&self, other: &Self) -> bool {
        self.score == other.score && self.chunk.prefix == other.chunk.prefix
    }
}
impl Eq for ScoredChunk {}

/// Build chunk map via catamorphism at fixed depth
type ChunkMap = HashMap<Vec<u8>, Vec<String>>;

fn build_chunks_catamorphic(map: &PathMap<(String, f64)>, depth: usize) -> ChunkMap {
    let rz = map.read_zipper();

    rz.into_cata_jumping_side_effect_fallible(
        move |_mask, children: &mut [ChunkMap], _jump_len, maybe_v, path| {
            let mut merged: ChunkMap = HashMap::new();

            // Merge results from child subtrees
            for mut child_map in children {
                for (k, mut vs) in child_map.drain() {
                    merged.entry(k).or_default().append(&mut vs);
                }
            }

            // Add current node's value to its chunk
            if let Some((name, _w)) = maybe_v {
                let prefix_len = depth.min(path.len());
                let prefix = path[..prefix_len].to_vec();
                merged.entry(prefix).or_default().push(name.clone());
            }

            Ok::<ChunkMap, Infallible>(merged)
        },
    )
    .expect("catamorphism failed")
}

/// A priority-queue-based uniform sweep
struct ChunkedPriorityQueue {
    heap: BinaryHeap<ScoredChunk>,
}

impl ChunkedPriorityQueue {
    fn new(chunk_map: ChunkMap) -> Self {
        let mut heap = BinaryHeap::new();

        // Convert each chunk group into a ScoredChunk
        for (prefix, atoms) in chunk_map {
            let count = atoms.len();
            heap.push(ScoredChunk {
                score: count,
                chunk: Chunk {
                    prefix,
                    atoms,
                    index: 0,
                },
            });
        }

        Self { heap }
    }

    /// Pop the highest-score chunk, return one atom from it, then push it back
    /// Returns None when all atoms are exhausted
    fn next_atom(&mut self) -> Option<String> {
        if let Some(mut scored_chunk) = self.heap.pop() {
            // If all atoms in this chunk are done, don't reinsert
            if scored_chunk.chunk.index >= scored_chunk.chunk.atoms.len() {
                return None;
            }

            // Pick next atom in round-robin order within the chunk
            let atom = scored_chunk.chunk.atoms[scored_chunk.chunk.index].clone();
            scored_chunk.chunk.index += 1;

            // Update score: atoms left
            let remaining = scored_chunk.chunk.atoms.len() - scored_chunk.chunk.index;
            if remaining > 0 {
                self.heap.push(ScoredChunk {
                    score: remaining,
                    chunk: scored_chunk.chunk,
                });
            }

            Some(atom)
        } else {
            None
        }
    }
}

fn main() {
    // Example data
    let mut map = PathMap::<(String, f64)>::new();
    map.set_val_at("atoms/a", ("Atom A".to_string(), 5.0));
    map.set_val_at("atoms/b", ("Atom B".to_string(), 2.0));
    map.set_val_at("atoms/c", ("Atom C".to_string(), 8.0));
    map.set_val_at("molecules/x", ("Mol X".to_string(), 3.0));
    map.set_val_at("molecules/y", ("Mol Y".to_string(), 7.0));

    let depth = 1; // partition at first byte

    // 1) Catamorphically build chunks
    let chunk_map = build_chunks_catamorphic(&map, depth);

    // 2) Create priority-based sweep
    let mut sweep = ChunkedPriorityQueue::new(chunk_map);

    println!("Uniform Sweep with Priority Queue (s(c) = atoms left), depth = {}:", depth);
    for i in 1..=10 {
        if let Some(name) = sweep.next_atom() {
            println!("  [{}] visited: {}", i, name);
        } else {
            println!("  [{}] No more atoms to visit", i);
            break;
        }
    }
}