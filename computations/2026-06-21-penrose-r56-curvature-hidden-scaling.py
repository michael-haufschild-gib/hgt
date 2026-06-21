#!/usr/bin/env python3
"""R56: hidden nondimensionalization in off-line curvature-window detection.

NODE: pattern onset in reaction-diffusion systems can be sensitive to
nondimensionalization choices and hidden parameter scalings.

Target: the off-line FE-quartet convex window in the zeta landscape:
    C_a(tau) = 2(a^2 - tau^2)/(a^2 + tau^2)^2 > 0 for |tau| < a.

The test asks whether raw curvature sampling has a hidden onset parameter.
"""

from __future__ import annotations

from math import pi
from random import Random
from typing import Iterable, Tuple

import numpy as np


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def swift_hohenberg_threshold(domain_length: float, q0: float, nmax: int = 80) -> Tuple[float, int, float]:
    """Toy pattern onset: lambda_n = mu - (k_n^2 - q0^2)^2."""
    best_mu = float("inf")
    best_n = -1
    best_k = 0.0
    for n in range(1, nmax + 1):
        k = 2.0 * pi * n / domain_length
        mu_c = (k * k - q0 * q0) ** 2
        if mu_c < best_mu:
            best_mu = mu_c
            best_n = n
            best_k = k
    return best_mu, best_n, best_k


def node_validation() -> None:
    print("\nNODE validation: hidden length scaling changes onset")
    physical_L = 9.7
    physical_q0 = 2.0
    true_mu, true_n, true_k = swift_hohenberg_threshold(physical_L, physical_q0)
    # Wrong nondimensionalization: set L'=1 but forget q0' = q0*L.
    wrong_mu, wrong_n, wrong_k = swift_hohenberg_threshold(1.0, physical_q0)
    # Correct nondimensionalization in x'=x/L: q0' = q0*L.
    correct_mu_dimless, correct_n, correct_k_dimless = swift_hohenberg_threshold(1.0, physical_q0 * physical_L)
    print(f"  physical L={physical_L:.2f}, q0={physical_q0:.2f}: n*={true_n}, k*={true_k:.4f}, mu_c={true_mu:.6f}")
    print(f"  wrong L'=1, q0'=q0         : n*={wrong_n}, k'={wrong_k:.4f}, mu_c'={wrong_mu:.6f}")
    print(
        f"  correct L'=1, q0'=q0 L     : n*={correct_n}, k'={correct_k_dimless:.4f}, "
        f"mu_c'={correct_mu_dimless:.6f}"
    )


def curvature(a: float, tau: np.ndarray) -> np.ndarray:
    return 2.0 * (a * a - tau * tau) / ((a * a + tau * tau) ** 2)


def sampled_detection(a: float, h: float, trials: int = 20_000, seed: int = 56) -> Tuple[float, float, float]:
    rng = Random(seed)
    detections = 0
    max_raw = []
    max_scaled = []
    span = 6
    for _ in range(trials):
        offset = rng.random() * h
        grid = np.arange(-span, span + 1, dtype=float) * h + offset
        vals = curvature(a, grid)
        positive = vals > 0
        if np.any(positive):
            detections += 1
            m = float(np.max(vals))
            max_raw.append(m)
            max_scaled.append(a * a * m)
    p = detections / trials
    mean_raw = float(np.mean(max_raw)) if max_raw else 0.0
    mean_scaled = float(np.mean(max_scaled)) if max_scaled else 0.0
    return p, mean_raw, mean_scaled


def curvature_scaling_extremes() -> None:
    print("\nTarget test: fixed raw grid h=1, varying off-line half-width a")
    h = 1.0
    for a in [0.01, 0.025, 0.05, 0.10, 0.25, 0.50, 1.00]:
        p, raw, scaled = sampled_detection(a, h)
        theory = min(1.0, 2.0 * a / h)
        print(
            f"  a/h={a/h:5.3f}: detect={p:6.4f}, theory={theory:6.4f}, "
            f"mean_raw_hit={raw:11.3e}, mean_a2_hit={scaled:8.5f}"
        )

    print("\nDimensionless check: hold h/a=q fixed, compare different a")
    for q in [0.25, 0.50, 1.00, 2.50]:
        rows = []
        for a in [0.02, 0.10, 0.40]:
            p, raw, scaled = sampled_detection(a, q * a, seed=560 + int(100 * q))
            rows.append((p, scaled))
        packed = "; ".join(f"p={p:.4f}, a2max={scaled:.5f}" for p, scaled in rows)
        print(f"  q=h/a={q:4.2f}: {packed}")


def main() -> None:
    node = "the sensitivity of pattern onset to nondimensionalization choices and hidden parameter scalings"
    attempts = [
        "off-line convex-window onset depends on dimensionless grid h/a",
        "raw curvature thresholds hide the quartet scale a",
        "nondimensionalizing by zero distance reveals universal convex window",
    ]
    print("R56 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    curvature_scaling_extremes()

    print("\nInterpretation:")
    print("  The hidden parameter is q=h/a: fixed raw grids miss narrow off-line windows")
    print("  with probability 1-2a/h when a<h/2, while a^2 C_a(tau) is scale-free")
    print("  after tau/a nondimensionalization. This is target-correct but overlaps the")
    print("  existing localization-width and grid-stability cards.")


if __name__ == "__main__":
    main()
