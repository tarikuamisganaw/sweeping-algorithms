#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    /// ------------------------------------------------------------
    /// Computes the expected probability of each node in the trie
    /// based on aggregate weights (node weight + subtree weights).
    /// ------------------------------------------------------------
    fn calculate_expected_distribution(map: &PathMap<f64>) -> HashMap<String, f64> {
        let mut probs = HashMap::new();
        let root = map.read_zipper();

        fn traverse(
            node: &ReadZipperUntracked<f64>,
            reach_prob: f64,
            result: &mut HashMap<String, f64>,
        ) {
            let total = node_agg_w(node);
            if total <= 0.0 {
                return;
            }

            // Probability of selecting this node directly
            if let Some(w) = node.val() {
                let local_prob = reach_prob * (*w / total);
                let atom = String::from_utf8_lossy(&node.origin_path().to_vec()).to_string();
                *result.entry(atom).or_insert(0.0) += local_prob;
            }

            // Recurse into children proportionally to their aggregate weight
            for b in node.child_mask().iter() {
                let mut child = node.clone();
                child.descend_to_byte(b);
                let child_total = node_agg_w(&child);
                if child_total > 0.0 {
                    let child_prob = reach_prob * (child_total / total);
                    traverse(&child, child_prob, result);
                }
            }
        }

        traverse(&root, 1.0, &mut probs);
        probs
    }

    /// ------------------------------------------------------------
    /// Runs the random walk N times and returns observed frequencies.
    /// ------------------------------------------------------------
    fn sample_distribution(map: &PathMap<f64>, num_samples: usize) -> HashMap<String, f64> {
        let mut counts = HashMap::new();

        for _ in 0..num_samples {
            if let Some(atom) = weighted_random_walk_catamorphism(map) {
                *counts.entry(atom).or_insert(0usize) += 1;
            }
        }

        counts
            .into_iter()
            .map(|(k, v)| (k, v as f64 / num_samples as f64))
            .collect()
    }

    /// ------------------------------------------------------------
    /// Compares observed and expected distributions within tolerance.
    /// ------------------------------------------------------------
    fn assert_distributions_close(
        observed: &HashMap<String, f64>,
        expected: &HashMap<String, f64>,
        tolerance: f64,
    ) {
        println!("{:<8} {:>10} {:>12} {:>10}", "Atom", "Observed%", "Expected%", "Δ%");
        println!("-----------------------------------------------------");

        for (atom, exp) in expected {
            let obs = observed.get(atom).copied().unwrap_or(0.0);
            let diff = (obs - exp).abs();

            println!(
                "{:<8} {:>10.3} {:>12.3} {:>10.3}",
                atom,
                obs * 100.0,
                exp * 100.0,
                diff * 100.0
            );

            assert!(
                diff < tolerance,
                "Atom '{}' diverged too much: observed {:.3}, expected {:.3}",
                atom,
                obs,
                exp
            );
        }
    }

    // ================================================================
    //                     TEST SUITES
    // ================================================================

    #[test]
    fn test_deep_trie_distribution() {
        println!("\n=== Deep Trie Test ===");
        let mut p: PathMap<f64> = PathMap::new();
        p.set_val_at("h", 20.0);
        p.set_val_at("hell", 12.0);
        p.set_val_at("hello", 10.0);

        let expected = calculate_expected_distribution(&p);
        let observed = sample_distribution(&p, 50_000);
        assert_distributions_close(&observed, &expected, 0.05);
    }

    #[test]
    fn test_flat_trie_distribution() {
        println!("\n=== Flat Trie Test ===");
        let mut p: PathMap<f64> = PathMap::new();
        p.set_val_at("a", 10.0);
        p.set_val_at("b", 30.0);
        p.set_val_at("c", 60.0);

        let expected = calculate_expected_distribution(&p);
        let observed = sample_distribution(&p, 50_000);
        assert_distributions_close(&observed, &expected, 0.03);
    }

    #[test]
    fn test_mixed_depth_trie_distribution() {
        println!("\n=== Mixed Depth Trie Test ===");
        let mut p: PathMap<f64> = PathMap::new();
        p.set_val_at("cat", 20.0);
        p.set_val_at("car", 10.0);
        p.set_val_at("cart", 15.0);
        p.set_val_at("dog", 25.0);
        p.set_val_at("door", 30.0);

        let expected = calculate_expected_distribution(&p);
        let observed = sample_distribution(&p, 80_000);
        assert_distributions_close(&observed, &expected, 0.05);
    }
}
