#!/usr/bin/env python3
"""
R32 STEP 11 wild metaphor check.

Method #4: change viewpoint.
Instead of asking how close sigma is to 1/2, view a finite Fisher cutoff
through u=(2*sigma-1)*log(X). The "wall" is then an apparent moving
resolution front rather than a fixed pole.
"""

from __future__ import annotations

import math

import numpy as np


def finite_fisher(delta: float, X: int) -> float:
    n = np.arange(1, X + 1, dtype=float)
    logs = np.log(n)
    weights = np.exp(-(1.0 + delta) * logs)
    weights /= weights.sum()
    mean = float(np.sum(weights * logs))
    second = float(np.sum(weights * logs * logs))
    return max(0.0, second - mean * mean)


def ratio(delta: float, X: int) -> float:
    return finite_fisher(delta, X) * delta * delta


def find_delta_for_ratio(X: int, target: float) -> float:
    lo, hi = 1e-5, 0.95
    for _ in range(50):
        mid = 0.5 * (lo + hi)
        if ratio(mid, X) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def fisher_length(X: int, delta_min: float, delta_max: float) -> float:
    grid = np.geomspace(delta_min, delta_max, 160)
    vals = np.array([math.sqrt(finite_fisher(float(d), X)) for d in grid])
    return float(np.trapezoid(vals, grid))


def main() -> None:
    Xs = [200, 800, 3200, 12800, 51200]
    targets = [0.1, 0.5, 0.8]

    print("Apparent wall front: solve g_X(delta)*delta^2 = q")
    print("X        q       delta_q     delta_q*logX")
    for X in Xs:
        logX = math.log(X)
        for q in targets:
            d = find_delta_for_ratio(X, q)
            print(f"{X:<8d} {q:4.1f}  {d:10.6f}  {d*logX:12.6f}")

    print("\nFinite Fisher arclength to the seam-side cutoff")
    print("X        delta_min=1/logX^2   length_to_0.4   true_log_length")
    for X in Xs:
        logX = math.log(X)
        dmin = 1.0 / (logX * logX)
        length = fisher_length(X, dmin, 0.4)
        true = math.log(0.4 / dmin)
        print(f"{X:<8d} {dmin:17.8f} {length:14.6f} {true:17.6f}")

    print("\nInterpretation")
    print(
        "Changing viewpoint turns the fixed Fisher wall into a moving finite-resolution "
        "front with nearly constant delta_q*logX. This is a useful warning for finite "
        "source-built approximations, but it is still the same cutoff asymptotic, not "
        "a new non-reducing Fisher-wall fact."
    )


if __name__ == "__main__":
    main()
