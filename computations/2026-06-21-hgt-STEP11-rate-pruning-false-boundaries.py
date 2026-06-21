#!/usr/bin/env python3
"""THE-MACHINE Step 11: false-boundary sweep for uncertain pruning.

Method #22:
    Compare nearby false statements.

False statements under attack:
    F1. Nominally low prime groups are safe to prune.
    F2. Robust uncertainty-aware pruning recovers the true analytic carrier.
    F3. The uncertainty-tail boundary is phase-specific rather than a generic
        finite-group sensitivity effect.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def load_step8_module():
    path = Path(__file__).with_name("2026-06-21-hgt-STEP8-rate-uncertainty-prime-pruning.py")
    spec = importlib.util.spec_from_file_location("rate_pruning_step8", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def summarize_sweep(
    module,
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    groups: list[tuple[int, ...]],
    coeff_sigmas: list[float],
    thresholds: list[float],
    trials: int,
    rng: np.random.Generator,
) -> None:
    gamma_vals, true_p, finite_contrib = module.build_arrays(sigma, window, samples, groups)
    true_delta = module.phase_defect_vec(gamma_vals, true_p)
    contrib = finite_contrib if kind == "finite" else module.random_phase_groups(finite_contrib, rng)
    full_p = np.ones(contrib.shape[0]) @ contrib
    full_err = float(np.median(np.abs(module.phase_defect_vec(gamma_vals, full_p) - true_delta)))
    print(f"\nCASE kind={kind} sigma={sigma} window=[{window[0]:.0f},{window[1]:.0f}] full_err={full_err:.4f}")
    print("coeff_sigma threshold keep_nom keep_robust err_nom err_robust robust_gain false_F1 false_F2")
    for coeff_sigma in coeff_sigmas:
        nominal, q95, _fail, _full_delta = module.group_importance(
            gamma_vals, contrib, 0.0, coeff_sigma, trials, rng
        )
        for threshold in thresholds:
            nominal_keep = nominal >= threshold
            robust_keep = q95 >= threshold
            nominal_p = nominal_keep.astype(float) @ contrib
            robust_p = robust_keep.astype(float) @ contrib
            err_nom = float(np.median(np.abs(module.phase_defect_vec(gamma_vals, nominal_p) - true_delta)))
            err_robust = float(np.median(np.abs(module.phase_defect_vec(gamma_vals, robust_p) - true_delta)))
            robust_gain = err_nom - err_robust
            false_f1 = int(err_nom > full_err + 0.05)
            false_f2 = int(err_robust > 0.8 * full_err)
            print(
                f"{coeff_sigma:.2f} {threshold:.3f} {int(np.sum(nominal_keep)):2d} "
                f"{int(np.sum(robust_keep)):2d} {err_nom:.4f} {err_robust:.4f} "
                f"{robust_gain:+.4f} {false_f1:d} {false_f2:d}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=180)
    parser.add_argument("--groups", type=int, default=12)
    parser.add_argument("--trials", type=int, default=120)
    args = parser.parse_args()
    module = load_step8_module()
    primes = module.first_primes(args.prime_count)
    group_size = len(primes) // args.groups
    groups = [tuple(primes[i * group_size : (i + 1) * group_size]) for i in range(args.groups)]
    rng = np.random.default_rng(260621220)
    coeff_sigmas = [0.25, 0.85, 1.40]
    thresholds = [0.010, 0.025, 0.035, 0.060, 0.100]
    print("STEP11 false-boundary sweep: uncertain prime-pruning metaphor")
    print(
        f"samples={args.samples} prime_count={args.prime_count} groups={args.groups} "
        f"trials={args.trials}"
    )
    print("false_F1=nominal pruning materially worse than full finite; false_F2=robust pruning still fails to recover true.")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["finite", "random-phase"]:
            summarize_sweep(
                module,
                kind,
                sigma,
                (100.0, 170.0),
                args.samples,
                groups,
                coeff_sigmas,
                thresholds,
                args.trials,
                rng,
            )


if __name__ == "__main__":
    main()
