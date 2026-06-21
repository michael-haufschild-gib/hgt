#!/usr/bin/env python3
"""STEP11 split-subclaim test for weld-density normalization."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_base(path: str):
    spec = importlib.util.spec_from_file_location("biofilm_density_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def coeffs(base, kind: str, sigma: float, window, threshold: float, samples: int, primes, rng):
    tr = base.trace(kind, sigma, window, samples, primes, rng)
    defect = tr[:, 0]
    excess = np.maximum(defect - threshold, 0.0)
    mask = excess > 0.0
    bound = float(np.sum(excess))
    free = float(np.sum(tr[:, 1]) + 1e-12)
    component_count = max(float(base.component_count(mask)), 1.0)
    event_count = max(float(np.sum(mask)), 1.0)
    # A non-tautological "binding-site" candidate: phase-opportunity density is the available
    # opposing amplitude product, independent of the thresholded excess mass.
    phase_opportunity = float(np.sum(np.sqrt(np.maximum(tr[:, 2] * tr[:, 3], 0.0))) + 1e-12)
    normalizers = {
        "time": float(len(excess)),
        "event": event_count,
        "component": component_count,
        "prime_amp": float(np.sum(tr[:, 2]) + 1e-12),
        "weld_amp": free,
        "phase_opportunity": phase_opportunity,
    }
    return {name: bound / (free * norm) for name, norm in normalizers.items()}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module-path", default="computations/2026-06-21-conway-biofilm-density-normalization.py")
    parser.add_argument("--samples", type=int, default=140)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    module_path = args.module_path
    if not Path(module_path).exists() and Path("/tmp/2026-06-21-conway-biofilm-density-normalization.py").exists():
        module_path = "/tmp/2026-06-21-conway-biofilm-density-normalization.py"
    base = load_base(module_path)
    primes = base.first_primes(args.prime_count)
    windows = [(14.0, 84.0), (100.0, 170.0), (260.0, 330.0), (500.0, 570.0)]
    sigmas = [0.3, 0.5, 0.7]
    thresholds = [0.6, 0.8, 1.0]
    normalizers = ["time", "event", "component", "prime_amp", "weld_amp", "phase_opportunity"]
    stats = {
        name: {
            "left_pass": 0,
            "left_total": 0,
            "transition_pass": 0,
            "transition_total": 0,
            "false_flip": 0,
            "true_values": [],
        }
        for name in normalizers
    }
    for threshold in thresholds:
        for window in windows:
            for sigma in sigmas:
                rows = {}
                for kind in ["true", "finite", "random"]:
                    seed = (
                        2211000
                        + int(10 * window[0])
                        + int(1000 * threshold)
                        + int(100 * sigma)
                        + {"true": 1, "finite": 2, "random": 3}[kind]
                    )
                    rows[kind] = coeffs(base, kind, sigma, window, threshold, args.samples, primes, np.random.default_rng(seed))
                for name in normalizers:
                    true_v = rows["true"][name]
                    max_control = max(rows["finite"][name], rows["random"][name])
                    if sigma in [0.3, 0.5]:
                        stats[name]["left_total"] += 1
                        stats[name]["left_pass"] += int(true_v > 1.25 * max_control)
                    else:
                        stats[name]["transition_total"] += 1
                        stats[name]["transition_pass"] += int(true_v > 1.25 * max_control)
                        stats[name]["false_flip"] += int(rows["finite"][name] > true_v)
                    if true_v > 0:
                        stats[name]["true_values"].append(true_v)

    print("STEP11 split-subclaim battery: weld-density normalization")
    print(f"samples_per_window={args.samples} prime_count={args.prime_count}")
    print("Subclaims:")
    print("S1 separation should survive the density basis in left-strip lanes.")
    print("S2 a binding-site-like phase-opportunity basis should stabilize true coefficients across windows.")
    print("S3 wrong bases should expose false flips in the transition lane instead of manufacturing a finding.")
    print("normalizer left_pass transition_pass transition_false_flips true_cv verdict")
    for name in normalizers:
        vals = np.asarray(stats[name]["true_values"], dtype=float)
        cv = float(np.std(vals) / max(np.mean(vals), 1e-12)) if len(vals) else 0.0
        left_pass = f"{stats[name]['left_pass']}/{stats[name]['left_total']}"
        trans_pass = f"{stats[name]['transition_pass']}/{stats[name]['transition_total']}"
        if stats[name]["left_pass"] == stats[name]["left_total"] and cv < 0.85:
            verdict = "candidate"
        elif stats[name]["false_flip"] > 0:
            verdict = "normalization_fragile"
        else:
            verdict = "weak"
        print(
            f"{name:18s} {left_pass:9s} {trans_pass:15s} "
            f"{stats[name]['false_flip']:4d} {cv:8.4f} {verdict}"
        )


if __name__ == "__main__":
    main()
