#!/usr/bin/env python3
import numpy as np


def simulate_tree(rng, n_stem=18, n_crown=18, dims=10, side_rate=0.75):
    trunk_drift = rng.normal(0.0, 0.22, size=dims)
    lca = trunk_drift
    stem_taxa = []
    stem_times = rng.uniform(0.05, 0.95, size=n_stem)
    for t in stem_times:
        trunk_state = t * trunk_drift + rng.normal(0.0, 0.05, size=dims)
        side_duration = rng.exponential(0.9)
        specialization = rng.normal(0.0, side_rate * side_duration, size=dims)
        stem_taxa.append(trunk_state + specialization)
    crown_taxa = []
    for _ in range(n_crown):
        branch_duration = rng.exponential(0.35)
        crown_taxa.append(lca + rng.normal(0.0, 0.35 * branch_duration, size=dims))
    return lca, np.array(stem_taxa), np.array(crown_taxa)


def summarize(side_rate, replicates=1200):
    rng = np.random.default_rng(20260621 + int(side_rate * 1000))
    stem_closer_than_crown = []
    closest_is_stem = []
    median_stem_dist = []
    median_crown_dist = []
    stem_range = []
    for _ in range(replicates):
        lca, stem, crown = simulate_tree(rng, side_rate=side_rate)
        d_stem = np.linalg.norm(stem - lca, axis=1)
        d_crown = np.linalg.norm(crown - lca, axis=1)
        stem_closer_than_crown.append(float(np.median(d_stem) < np.median(d_crown)))
        closest_is_stem.append(float(np.min(d_stem) < np.min(d_crown)))
        median_stem_dist.append(float(np.median(d_stem)))
        median_crown_dist.append(float(np.median(d_crown)))
        stem_range.append(float(np.quantile(d_stem, 0.9) / (np.quantile(d_stem, 0.1) + 1e-12)))
    return {
        "side_rate": side_rate,
        "stem_median_lt_crown_frac": float(np.mean(stem_closer_than_crown)),
        "closest_tip_is_stem_frac": float(np.mean(closest_is_stem)),
        "median_stem_distance": float(np.mean(median_stem_dist)),
        "median_crown_distance": float(np.mean(median_crown_dist)),
        "stem_distance_q90_q10_ratio": float(np.mean(stem_range)),
    }


def main():
    print("NODE: stem taxa do not necessarily resemble the last common ancestor")
    print("side_rate stem_median_lt_crown_frac closest_tip_is_stem_frac median_stem_distance median_crown_distance stem_distance_q90_q10_ratio")
    for side_rate in [0.0, 0.15, 0.35, 0.75, 1.25, 2.00]:
        row = summarize(side_rate)
        print(
            f"{row['side_rate']:.2f} {row['stem_median_lt_crown_frac']:.6f} "
            f"{row['closest_tip_is_stem_frac']:.6f} {row['median_stem_distance']:.6f} "
            f"{row['median_crown_distance']:.6f} {row['stem_distance_q90_q10_ratio']:.6f}"
        )


if __name__ == "__main__":
    main()
