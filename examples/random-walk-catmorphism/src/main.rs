use pathmap::PathMap;
use pathmap::morphisms::Catamorphism;
 use pathmap::zipper::ZipperAbsolutePath;
use pathmap::zipper::{ReadZipperUntracked, Zipper, ZipperMoving, ZipperValues};
use rand::Rng;
use std::collections::HashMap;
use std::convert::Infallible;

/// Compute aggregate weight = node’s own + sum(children)
fn node_agg_w(z: &ReadZipperUntracked<f64>) -> f64 {
    z.clone()
        .into_cata_jumping_side_effect_fallible(
            |_mask, children, _jump_len, maybe_v, _path| {
                let child_sum: f64 = children.iter().copied().sum();
                let here = maybe_v.copied().unwrap_or(0.0);
                Ok::<f64, Infallible>(here + child_sum)
            },
        )
        .unwrap_or(0.0)
}

/// Weighted random walk following the Weighted Atom Sweep logic
fn weighted_random_walk_catamorphism(map: &PathMap<f64>) -> Option<String> {
    let mut z = map.read_zipper();
    let mut rng = rand::rng();

    loop {
        let total = node_agg_w(&z);
        if total <= 0.0 {
            return None;
        }

        let mut r: f64 = rng.random_range(0.0..total);

        // Step 1: pick this node if within its own weight
        if let Some(w) = z.val() {
            if r < *w {
                // The atom is represented by the full path (converted to UTF-8 string)
                let bytes = z.origin_path().to_vec();
                let atom = String::from_utf8_lossy(&bytes).to_string();
                return Some(atom);
            }
            r -= *w;
        }

        // Step 2: otherwise descend into children by aggregate weight
        let mut chosen: Option<u8> = None;
        for b in z.child_mask().iter() {
            let mut child = z.clone();
            child.descend_to_byte(b);
            let child_total = node_agg_w(&child);

            if r < child_total {
                chosen = Some(b);
                break;
            } else {
                r -= child_total;
            }
        }

        if let Some(b) = chosen {
            z.descend_to_byte(b);
        } else {
            return None;
        }
    }
}

fn main() {
    // Build a trie of weights
    let mut p: PathMap<f64> = PathMap::new();
    p.set_val_at("h", 20.0);
    p.set_val_at("hell", 12.0);
    p.set_val_at("hello", 10.0);

    let keys = ["h", "hell", "hello"];
    let num_samples = 10_000;

    let mut counts = HashMap::new();
    let mut successes = 0;
    while successes < num_samples {
        if let Some(atom) = weighted_random_walk_catamorphism(&p) {
            *counts.entry(atom).or_insert(0) += 1;
            successes += 1;
        }
    }

    println!("\n✅ Sampling Results ({} successful walks):", num_samples);
    println!("{:<8} {:<8} {:<12}", "Atom", "Count", "Observed%");
    println!("----------------------------------------");

    for k in keys {
        let count = *counts.get(k).unwrap_or(&0);
        let obs = (count as f64 / num_samples as f64) * 100.0;
        println!("{:<8} {:<8} {:<12.3}", k, count, obs);
    }
}
