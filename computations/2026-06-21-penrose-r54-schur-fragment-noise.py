#!/usr/bin/env python3
"""R54: discreteness fragments as a G-C19 Schur-signature warning.

NODE: warm dark matter N-body simulations can form artificial filament
fragments from discreteness noise.

Target: G-C19 primitive Schur/Hodge equivalence.  Weakened test only:
finite Schur-style inside/outside signatures near the unit-circle boundary can
be dominated by tiny cutoff/noise fragments, so a fake-family failure theorem
is mandatory.
"""

from __future__ import annotations

from random import Random
from statistics import mean
from typing import List, Tuple

import numpy as np


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def node_filament_demo(seed: int = 54) -> None:
    rng = Random(seed)
    bins = [0] * 80
    for _ in range(500):
        # Smooth underlying filament plus particle discreteness.
        x = min(0.999, max(0.0, rng.random()))
        bins[int(x * len(bins))] += 1
    avg = mean(bins)
    peaks = 0
    for i in range(1, len(bins) - 1):
        if bins[i] > bins[i - 1] and bins[i] > bins[i + 1] and bins[i] > 1.8 * avg:
            peaks += 1
    print("\nNODE validation: 1D filament shot-noise fragments")
    print(f"  bins={len(bins)}, particles=500, mean_count={avg:.3f}, artificial_peak_count={peaks}")


def noisy_unit_circle_poly(degree: int, eps: float, seed: int) -> np.ndarray:
    """Return coefficients for z^degree - 1 with small coefficient noise."""
    rng = np.random.default_rng(seed)
    coeffs = np.zeros(degree + 1, dtype=np.complex128)
    coeffs[0] = 1.0
    coeffs[-1] = -1.0
    noise = eps * (rng.standard_normal(degree) + 1j * rng.standard_normal(degree))
    coeffs[1:] += noise
    return coeffs


def schur_inside_count(coeffs: np.ndarray) -> Tuple[int, float, float]:
    roots = np.roots(coeffs)
    radii = np.abs(roots)
    inside = int(np.sum(radii < 1.0))
    min_margin = float(np.min(np.abs(radii - 1.0)))
    max_margin = float(np.max(np.abs(radii - 1.0)))
    return inside, min_margin, max_margin


def main() -> None:
    node = "warm dark matter simulations often form artificial filament fragments from discreteness noise"
    attempts = [
        "finite Schur signatures can contain artificial cutoff fragments",
        "primitive Pick signature needs fake-family resolution stress",
        "near-boundary Schur roots fragment under discreteness noise",
    ]
    print("R54 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_filament_demo()
    degree = 36
    print("\nNoisy Schur-boundary toy: z^d-1 plus coefficient fragments")
    for eps in [1e-12, 1e-10, 1e-8, 1e-6, 1e-4]:
        inside_counts: List[int] = []
        min_margins: List[float] = []
        for seed in range(20):
            coeffs = noisy_unit_circle_poly(degree, eps, seed)
            inside, min_margin, _ = schur_inside_count(coeffs)
            inside_counts.append(inside)
            min_margins.append(min_margin)
        print(
            f"  eps={eps:.0e}: inside_count range={min(inside_counts)}..{max(inside_counts)}, "
            f"mean={mean(inside_counts):.2f}, mean_min_margin={mean(min_margins):.3e}"
        )

    print("\nInterpretation:")
    print("  Tiny coefficient-scale fragments can move many near-boundary roots inside/outside.")
    print("  This is a fake-family/noise stress for G-C19, not a Hodge comparison theorem.")


if __name__ == "__main__":
    main()
