#!/usr/bin/env python3
"""THE-MACHINE Step 11: small-case identifiability after histogram matching.

Method #9:
    Test small cases.

Metaphor:
    The NODE says endpoint count data are not enough; hidden event structure is
    needed. Here the endpoint data are phase-defect histograms. After forcing
    controls to have the same histogram as true zeta, ask how many ordered
    samples are needed before hidden sequence structure separates.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def load_step8_module():
    path = Path(__file__).with_name("2026-06-21-hgt-STEP8-propensity-identifiability-phasehist.py")
    spec = importlib.util.spec_from_file_location("phasehist_step8", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def hidden_features(module, vals: np.ndarray, true_vals: np.ndarray) -> dict[str, float]:
    threshold = float(np.median(true_vals))
    runs = module.run_lengths(vals > threshold)
    acf1 = float(np.corrcoef(vals[:-1], vals[1:])[0, 1]) if len(vals) > 4 and np.std(vals) > 1e-12 else 0.0
    acf4 = float(np.corrcoef(vals[:-4], vals[4:])[0, 1]) if len(vals) > 12 and np.std(vals) > 1e-12 else 0.0
    qs = np.quantile(true_vals, [0.25, 0.50, 0.75])
    states = np.digitize(vals, qs)
    return {
        "run_q90": float(np.quantile(runs, 0.90)) if runs else 0.0,
        "run_max": float(max(runs)) if runs else 0.0,
        "acf1": acf1,
        "acf4": acf4,
        "trans_entropy": module.transition_entropy(states),
    }


def feature_distance(a: dict[str, float], b: dict[str, float]) -> float:
    return (
        abs(a["acf1"] - b["acf1"])
        + abs(a["acf4"] - b["acf4"])
        + abs(a["trans_entropy"] - b["trans_entropy"])
        + abs(a["run_q90"] - b["run_q90"]) / max(1.0, b["run_q90"])
        + abs(a["run_max"] - b["run_max"]) / max(1.0, b["run_max"])
    )


def run_small_cases(samples_list: list[int], prime_count: int) -> None:
    module = load_step8_module()
    primes = module.first_primes(prime_count)
    rng = np.random.default_rng(260621092)
    print("STEP11 small-case hidden-order identifiability")
    print(f"prime_count={prime_count}")
    print("sigma samples control hist_js hidden_distance run_q90 acf1 acf4 trans_entropy")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for samples in samples_list:
            window = (100.0, 170.0)
            true_vals = module.phase_series("true", sigma, window, samples, primes, rng)
            finite_vals = module.phase_series("finite", sigma, window, samples, primes, rng)
            random_vals = module.phase_series("random", sigma, window, samples, primes, rng)
            controls = {
                "finite_histmatched": module.quantile_map(finite_vals, true_vals),
                "random_histmatched": module.quantile_map(random_vals, true_vals),
                "true_shuffled": rng.permutation(true_vals),
            }
            base = hidden_features(module, true_vals, true_vals)
            for name, vals in controls.items():
                feat = hidden_features(module, vals, true_vals)
                dist = feature_distance(feat, base)
                hist_js = module.js_hist(vals, true_vals, 16)
                print(
                    f"{sigma:.1f} {samples:3d} {name:20s} {hist_js:.4f} {dist:.4f} "
                    f"{feat['run_q90']:.1f} {feat['acf1']:+.3f} {feat['acf4']:+.3f} "
                    f"{feat['trans_entropy']:.3f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-count", type=int, default=180)
    args = parser.parse_args()
    run_small_cases([60, 120, 240, 420], args.prime_count)


if __name__ == "__main__":
    main()
