use pathmap::PathMap;
use pathmap::morphisms::Catamorphism;
use pathmap::zipper::{ReadZipperUntracked, Zipper, ZipperValues, ZipperMoving};
use rand::Rng;
use std::collections::HashMap;
use std::convert::Infallible;

/// Compute aggregate weight = this node’s weight + sum(children)
/// Uses JUMPING catamorphism 
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

/// Weighted random walk sampler
fn weighted_random_walk_catamorphism(map: &PathMap<(String, f64)>) -> Option<String> {
    let mut z = map.read_zipper();
    let mut rng = rand::thread_rng();

    loop {
        let total = node_agg_w(&z);
        if total <= 0.0 {
            return None;
        }

        let mut r = rng.gen_range(0.0..total);

        if let Some((name, w)) = z.val() {
            if r < *w {
                return Some(name.clone());
            }
            r -= *w;
        }

        if z.child_count() == 0 {
            return None;
        }

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

        if let Some(b) = chosen {
            z.descend_to_byte(b);
        } else {
            return None;
        }
    }
}

fn main() {
    let mut p: PathMap<(String, f64)> = PathMap::new();
    p.set_val_at("h", ("h".to_string(), 20.0));
    p.set_val_at("hell", ("hell".to_string(), 12.0));
    p.set_val_at("hello", ("hello".to_string(), 10.0));

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

    println!("\n Sampling Results ({} successful walks):", num_samples);
    println!("{:<8} {:<8} {:<12}", "Atom", "Count", "Observed%");
    println!("----------------------------------------");
    for k in keys {
        let count = *counts.get(&k.to_string()).unwrap_or(&0);
        let obs = (count as f64 / num_samples as f64) * 100.0;
        println!("{:<8} {:<8} {:<12.3}", k, count, obs);
    }
}