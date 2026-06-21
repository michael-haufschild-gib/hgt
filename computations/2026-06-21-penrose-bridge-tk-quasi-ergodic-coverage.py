#!/usr/bin/env python3
"""Bridge {T_k} versus quasi-ergodic coverage.

Research node:
    {T_k}, the reciprocal seam-moment sequence from bridge-theorem.md.

Random NODE:
    Ehrenfest quasi-ergodicity was a substitute notion because actual
    trajectories do not simply fill the energy surface.

Constraint:
    Geometric coverage of the state space is not the same datum as the
    invariant/time-average measure. A path can visit every coarse cell while
    spending very unequal time in them.

Method 18:
    Look for the right theorem. Here the right theorem is the
    Hamburger-Stieltjes moment theorem, not a coverage criterion.
"""

from __future__ import annotations

from math import cos, pi
from typing import Iterable

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        cur = [i]
        for j, cb in enumerate(b, start=1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def coverage(xs: np.ndarray, bins: int = 100) -> float:
    idx = np.clip((xs * bins).astype(int), 0, bins - 1)
    return len(set(idx.tolist())) / bins


def observables(xs: np.ndarray) -> dict[str, float]:
    return {
        "coverage_100_bins": coverage(xs),
        "mean_x": float(np.mean(xs)),
        "mean_cos": float(np.mean(np.cos(2 * pi * xs))),
        "mean_indicator_first_tenth": float(np.mean(xs < 0.1)),
    }


def quasi_coverage_sequences(cycles: int = 30, bins: int = 100, linger: int = 400) -> tuple[np.ndarray, np.ndarray]:
    centers = (np.arange(bins) + 0.5) / bins
    uniform = np.tile(centers, cycles)

    biased_blocks: list[np.ndarray] = []
    alpha = (5**0.5 - 1) / 2
    for c in range(cycles):
        biased_blocks.append(centers)
        linger_points = (0.005 + 0.09 * ((np.arange(linger) * alpha + c * alpha) % 1.0))
        biased_blocks.append(linger_points)
    return uniform, np.concatenate(biased_blocks)


def bridge_moments(max_k: int, eps: float, a: float = 0.1, gamma: float = 1.0, bulk_n: int = 80) -> list[float]:
    """Positive-axis bulk plus a small FE-symmetric off-axis pair in y."""
    xs = np.linspace(0.02, 1.0, bulk_n)
    weights = np.ones(bulk_n) / bulk_n
    w = complex(a, gamma)
    z = -1.0 / (w * w)
    moments: list[float] = []
    for k in range(max_k + 1):
        bulk = float(np.sum(weights * (xs**k)))
        off_axis = eps * ((z**k) + (z.conjugate() ** k)).real
        moments.append(bulk + off_axis)
    return moments


def shifted_hankel_min_eig(moments: list[float], degree: int, shift: int) -> float:
    h = np.array(
        [[moments[i + j + shift] for j in range(degree + 1)] for i in range(degree + 1)],
        dtype=float,
    )
    return float(np.linalg.eigvalsh(h)[0])


def first_shifted_failure(eps: float, max_degree: int = 35, tol: float = -1e-10) -> tuple[int, int, float] | None:
    moments = bridge_moments(2 * max_degree + 3, eps=eps)
    for degree in range(max_degree + 1):
        for shift in (1, 2):
            mineig = shifted_hankel_min_eig(moments, degree, shift)
            if mineig < tol:
                return degree, shift, mineig
    return None


def min_eigs_prefix(eps: float, max_degree: int = 6) -> Iterable[tuple[int, float, float]]:
    moments = bridge_moments(2 * max_degree + 3, eps=eps)
    for degree in range(max_degree + 1):
        yield (
            degree,
            shifted_hankel_min_eig(moments, degree, 1),
            shifted_hankel_min_eig(moments, degree, 2),
        )


def print_header(title: str) -> None:
    print("\n" + title)
    print("-" * len(title))


def main() -> None:
    node_constraint = "dense trajectory coverage does not imply correct time averages"
    attempts = [
        "dense y support does not certify reciprocal moment averages",
        "low order T_k windows do not replace all order shifted Hankel tests",
        "time average bias becomes atom weight bias in the T_k sequence",
    ]

    print_header("Step 8 transfer attempts")
    scored = []
    for label, attempt in zip("ABC", attempts):
        d = levenshtein(node_constraint, attempt)
        scored.append((d, label, attempt))
        print(f"{label}: distance={d:2d} :: {attempt}")
    distance, label, chosen = min(scored)
    print(f"chosen={label}, distance={distance}")

    print_header("NODE test: coverage is not averaging")
    uniform, biased = quasi_coverage_sequences()
    for name, xs in [("uniform_coverage", uniform), ("biased_full_coverage", biased)]:
        obs = observables(xs)
        print(
            f"{name:22s} coverage={obs['coverage_100_bins']:.3f} "
            f"mean_x={obs['mean_x']:.6f} "
            f"mean_cos={obs['mean_cos']:.6f} "
            f"mass_x_lt_0.1={obs['mean_indicator_first_tenth']:.6f}"
        )
    print(
        "constraint_check: both paths visit every coarse cell, but the time-average "
        "measure is different."
    )

    print_header("Bridge transfer: low-degree windows can miss a small off-axis atom")
    print("positive bulk: 80 atoms on [0.02,1.0]; off-axis pair: y=-1/(0.1+i)^2 and conjugate")
    for eps in (1e-1, 1e-2, 1e-3, 1e-4):
        failure = first_shifted_failure(eps)
        print(f"eps={eps:.0e} first_failure={failure}")

    eps = 1e-2
    print(f"\nlow-degree prefix for eps={eps:.0e}:")
    for degree, q0, q1 in min_eigs_prefix(eps, max_degree=6):
        print(f"degree={degree:2d} min_eig_Q0={q0:+.3e} min_eig_Q1={q1:+.3e}")

    print_header("Right theorem")
    print(
        "Coverage/density is the wrong theorem. The bridge node {T_k} needs the "
        "Hamburger-Stieltjes all-order square-test: Q_0[p]>=0 and Q_1[p]>=0 "
        "for every polynomial p."
    )
    print(
        "The experiment reproduces the bridge-theorem guardrail: finite or "
        "coverage-like evidence can miss a small off-axis contribution, while "
        "all-order shifted moment positivity is faithful."
    )
    print("verdict_hint: reduce-to-known unless a new source-built all-order positivity mechanism appears.")


if __name__ == "__main__":
    main()
