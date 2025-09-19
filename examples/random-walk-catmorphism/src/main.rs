use pathmap::PathMap;
use pathmap::morphisms::Catamorphism;
use pathmap::zipper::{ReadZipperUntracked, Zipper, ZipperValues, ZipperMoving};
use std::convert::Infallible;
use rand::Rng;

/// Compute aggregate weight = this node’s weight + sum(children)
fn node_agg_w(z: &ReadZipperUntracked<(String, f64)>) -> f64 {
    z.clone()
        .into_cata_jumping_side_effect_fallible(
            |_mask, children, _jump_len, maybe_v, _path| {
                let child_sum: f64 = children.iter().copied().sum();
                let here = maybe_v.map(|(_, w)| *w).unwrap_or(0.0);
                Ok::<f64, Infallible>(here + child_sum)
            },
        )
        .unwrap_or(0.0)
}

/// Weighted random walk using catamorphism
fn weighted_random_walk_catamorphism(map: &PathMap<(String, f64)>) -> Option<String> {
    let mut z = map.read_zipper();
    let mut rng = rand::thread_rng();

    loop {
        let total = node_agg_w(&z);
        if total <= 0.0 {
            return None;
        }

        let mut r = rng.gen_range(0.0..total);

        // Step 1: maybe take this node’s own value
        if let Some((name, w)) = z.val() {
            if r < *w {
                return Some(name.clone());
            }
            r -= *w;
        }

        // Step 2: iterate over children, subtracting aggregate weights
        let mut chosen: Option<u8> = None;
        for b in z.child_mask().iter() {
            z.descend_to_byte(b);
            let child_total = node_agg_w(&z);
            z.ascend_byte();

            if r < child_total {
                chosen = Some(b);
                break;
            } else {
                r -= child_total;
            }
        }

        // Step 3: descend into chosen child or terminate
        if let Some(b) = chosen {
            z.descend_to_byte(b);
        } else {
            return None;
        }
    }
}

fn main() {
    // Build the trie
    let mut p: PathMap<(String, f64)> = PathMap::new();
    p.set_val_at("h", ("h".to_string(), 20.0));
    p.set_val_at("hell", ("hell".to_string(), 10.0));
    p.set_val_at("hello", ("hello".to_string(), 12.0));
  

    // True weights
    let weights = [
        ("h", 20.0),
        ("hell", 10.0),
        ("hello", 12.0),
     
    ];
    let total: f64 = weights.iter().map(|(_, w)| w).sum();

    println!("=== Expected Weights ===");
    for (name, w) in &weights {
        println!("{:>8} → weight {:.1}, expected {:.1}%", name, w, w / total * 100.0);
    }
    println!("  {:>8} → total {:.1}\n", "SUM", total);

    // Run experiment
    let num_samples = 10_000;
    let mut counts = std::collections::HashMap::new();

    for _ in 0..num_samples {
        if let Some(atom) = weighted_random_walk_catamorphism(&p) {
            *counts.entry(atom).or_insert(0) += 1;
        }
    }

    println!("\n✅ Sampling Results ({} walks):", num_samples);
    println!("{:<8} {:<8} {:<10} {:<10}", "Atom", "Count", "Observed%", "Expected%");
    println!("------------------------------------------------");
    for (name, w) in weights {
        let count = *counts.get(name).unwrap_or(&0);
        let obs = (count as f64 / num_samples as f64) * 100.0;
        let exp = (w / total) * 100.0;
        println!("{:<8} {:<8} {:<10.1} {:<10.1}", name, count, obs, exp);
    }
}
