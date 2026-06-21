#!/usr/bin/env python3
"""STEP 11 boundary cases for residual compactness -> Weld.

Classify whether the apparent noncompact Hankel rank is a relative-threshold
artifact when the true-minus-finite residual amplitude collapses on the
Euler-convergent side.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-residual-compactness-weld.py")

first_primes = BASE["first_primes"]
weld_trace = BASE["weld_trace"]
hankel = BASE["hankel"]


def absolute_ranks(svals: np.ndarray) -> tuple[int, int, int]:
    return (
        int(np.sum(svals > 10.0)),
        int(np.sum(svals > 1.0)),
        int(np.sum(svals > 0.1)),
    )


def main() -> None:
    rng = np.random.default_rng(2606212258)
    primes = first_primes(160)
    print("STEP 11 METHOD 23: CLASSIFY BOUNDARY CASES")
    print("Boundary test: relative rank can saturate on tiny residuals; absolute singular thresholds test amplitude collapse.")
    print("sigma length residual mean_abs top_sv rank_gt10 rank_gt1 rank_gt0.1 boundary_class")
    for sigma in [0.5, 0.8, 1.2, 1.5]:
        for length in [40.0, 80.0, 160.0]:
            true = weld_trace("true", sigma, 100.0, length, 0.25, primes, rng)
            finite = weld_trace("finite", sigma, 100.0, length, 0.25, primes, rng)
            residual = true - finite
            x = residual - float(np.mean(residual))
            rows = min(64, len(x) // 3)
            svals = np.linalg.svd(hankel(x, rows), compute_uv=False)
            r10, r1, r01 = absolute_ranks(svals)
            mean_abs = float(np.mean(np.abs(x)))
            if mean_abs < 0.01 and r1 == 0:
                bclass = "amplitude-collapsed"
            elif mean_abs < 0.1 and r1 > 0:
                bclass = "small-but-structured"
            else:
                bclass = "large-residual"
            print(
                f"{sigma:.1f} {length:6.1f} true_minus_finite {mean_abs:.6f} "
                f"{svals[0]:.6f} {r10:3d} {r1:3d} {r01:3d} {bclass}"
            )
    print()
    print(
        "Interpretation: if right-side residuals are amplitude-collapsed under "
        "absolute thresholds while critical residuals remain large, the main "
        "rank saturation was a relative-threshold artifact, not a compactness "
        "finding."
    )


if __name__ == "__main__":
    main()
