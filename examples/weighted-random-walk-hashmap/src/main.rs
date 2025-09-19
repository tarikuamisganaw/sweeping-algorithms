use pathmap::PathMap;
use rand::Rng;
use std::collections::HashMap;

/// A wrapper around PathMap that maintains cached aggregate weights
/// for each prefix in the trie. This enables efficient weighted random
/// walks that respect the trie hierarchy:
/// - Each atom has a weight.
/// - Each node stores the sum of weights in its subtree.
/// - A random walk descends from the root, choosing branches
///   with probability proportional to their aggregate weights,
///   until a leaf atom is reached.
struct WeightedPathMap {
    map: PathMap<(String, f64)>,
    agg_weights: HashMap<Vec<u8>, f64>,
}

impl WeightedPathMap {
    /// Create a new weighted PathMap with empty trie and no weights.
    fn new() -> Self {
        Self {
            map: PathMap::new(),
            agg_weights: HashMap::new(),
        }
    }

    /// Insert an atom at the given path with its value and weight.
    /// The atom’s weight is also propagated upward into all prefix
    /// nodes so that aggregate weights can be used for random walks.
    fn insert_with_weight(&mut self, path: &str, value: &str, weight: f64) {
        self.map.set_val_at(path, (value.to_string(), weight));

        let path_bytes = path.as_bytes();
        for i in 0..=path_bytes.len() {
            let prefix = path_bytes[..i].to_vec();
            *self.agg_weights.entry(prefix).or_insert(0.0) += weight;
        }
    }

    /// Perform a weighted random walk down the trie.
    /// Starting from the root, a random number in [0, total_weight)
    /// is generated. At each node, we choose a child subtree based
    /// on its aggregate weight, subtracting until the number falls
    /// in that subtree’s range. Children are sorted in descending
    /// order of their aggregate weights before being compared.
    fn weighted_random_walk_trie(&self) -> Option<String> {
        let total_weight = *self.agg_weights.get(&vec![]).unwrap_or(&0.0);
        if total_weight == 0.0 {
            return None;
        }

        let mut r = rand::thread_rng().gen_range(0.0..total_weight);
        let mut prefix: Vec<u8> = vec![];

        loop {
            // Collect children (next byte) with their weights
            let mut child_weights: Vec<(u8, f64)> = self
                .map
                .iter()
                .filter_map(|(p, _)| {
                    if p.starts_with(&prefix) && p.len() > prefix.len() {
                        let child_byte = p[prefix.len()];
                        let mut child_prefix = prefix.clone();
                        child_prefix.push(child_byte);
                        let w = *self.agg_weights.get(&child_prefix).unwrap_or(&0.0);
                        Some((child_byte, w))
                    } else {
                        None
                    }
                })
                .collect();

            // Sort children by descending aggregate weight
            child_weights.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
            child_weights.dedup_by_key(|k| k.0);

            if child_weights.is_empty() {
                if let Some((val, _w)) = self.map.get(&prefix) {
                    return Some(val.clone());
                }
                return None;
            }

            let mut chosen_child: Option<u8> = None;
            for (child, w) in child_weights {
                if r < w {
                    chosen_child = Some(child);
                    break;
                } else {
                    r -= w;
                }
            }

            if let Some(c) = chosen_child {
                prefix.push(c);
            } else {
                return None;
            }
        }
    }
}

fn main() {
    let mut weighted_map = WeightedPathMap::new();

    // Insert atoms with their weights
    weighted_map.insert_with_weight("atoms/a", "Atom A", 5.0);
    weighted_map.insert_with_weight("atoms/b", "Atom B", 2.0);
    weighted_map.insert_with_weight("atoms/c", "Atom C", 8.0);

    let total_weight = *weighted_map.agg_weights.get(&vec![]).unwrap_or(&0.0);
    println!("Total weight: {:.1}\n", total_weight);

    let atoms = vec![
        ("atoms/a", "Atom A", 5.0),
        ("atoms/b", "Atom B", 2.0),
        ("atoms/c", "Atom C", 8.0),
    ];

    // Expected probabilities
    let expected_probs: HashMap<&str, f64> = atoms
        .iter()
        .map(|(path, _, w)| (*path, w / total_weight))
        .collect();

    // Sample many walks
    let num_samples = 10_000;
    let mut counts: HashMap<String, usize> = HashMap::new();

    println!("Example picks:");
    for _ in 0..10 {
        if let Some(val) = weighted_map.weighted_random_walk_trie() {
            println!("  Picked atom: {}", val);
        }
    }

    for _ in 0..num_samples {
        if let Some(val) = weighted_map.weighted_random_walk_trie() {
            *counts.entry(val).or_insert(0) += 1;
        }
    }

    // Final report
    println!("\nFinal Report ({} samples):", num_samples);
    // Prints a nice table header
    println!("{:<10} {:<8} {:<12} {:<12} {:<10}",
        "Atom", "Weight", "Expected %", "Actual %", "Count");
    println!("{}", "-".repeat(60));

    for (path, name, weight) in atoms {
        let expected = expected_probs[path];
        let actual_count = *counts.get(name).unwrap_or(&0);
        let actual = actual_count as f64 / num_samples as f64;

        println!(
            "{:<10} {:<8.1} {:<12.1} {:<12.1} {:<10}",
            name,
            weight,
            expected * 100.0,
            actual * 100.0,
            actual_count
        );
    }
}