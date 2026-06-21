#!/usr/bin/env python3
"""
Attempt 5 transfer experiment.

ResearchNode: Conjecture A / prime-log algebraic independence.
NODE constraint: hidden anisotropy from rectangular finite averaging windows.

Transfer:
  Finite searches for polynomial relations among {log p} use finite monomial
  exponent windows.  A rectangular coordinate cutoff is not direction-neutral
  in the monomial exponent lattice.  This script measures which exponent
  directions are exposed or hidden by common finite windows.
"""

from __future__ import annotations

from itertools import product
from math import log, sqrt

import numpy as np


Exponent = tuple[int, int, int]


def rectangular(D: int) -> list[Exponent]:
    return [(a, b, c) for a, b, c in product(range(D + 1), repeat=3)]


def total_degree(K: int) -> list[Exponent]:
    return [(a, b, c) for a, b, c in product(range(K + 1), repeat=3) if a + b + c <= K]


def l2_ball(R: float) -> list[Exponent]:
    n = int(R)
    return [(a, b, c) for a, b, c in product(range(n + 1), repeat=3) if a * a + b * b + c * c <= R * R]


def support(window: list[Exponent], direction: np.ndarray) -> float:
    return max(float(np.dot(np.array(alpha, dtype=float), direction)) for alpha in window)


def first_exposure(alpha: Exponent, max_D: int = 20) -> tuple[int, int, int]:
    rect = next(D for D in range(max_D + 1) if alpha in rectangular(D))
    degree = next(K for K in range(max_D * 3 + 1) if alpha in total_degree(K))
    ball = next(R for R in range(max_D * 3 + 1) if alpha in l2_ball(float(R)))
    return rect, degree, ball


def monomial_value(alpha: Exponent) -> float:
    logs = [log(2.0), log(3.0), log(5.0)]
    out = 1.0
    for e, x in zip(alpha, logs):
        out *= x**e
    return out


def summarize_window(name: str, window: list[Exponent]) -> None:
    dirs = []
    for a, b, c in product(range(0, 7), repeat=3):
        if (a, b, c) != (0, 0, 0):
            v = np.array([a, b, c], dtype=float)
            dirs.append(v / np.linalg.norm(v))
    supports = np.array([support(window, d) for d in dirs])
    values = np.array([abs(monomial_value(alpha)) for alpha in window])
    print(f"{name}: count={len(window)}")
    print(
        f"  directional support min/median/max="
        f"{supports.min():.3f}/{np.median(supports):.3f}/{supports.max():.3f}; "
        f"ratio={supports.max()/supports.min():.2f}"
    )
    print(
        f"  monomial |value| min/median/max="
        f"{values.min():.3e}/{np.median(values):.3e}/{values.max():.3e}"
    )
    if supports.max() / supports.min() > 1.2:
        print("  verdict: direction-neutral cutoff is FALSE")
    else:
        print("  verdict: approximately direction-neutral at this radius")


def main() -> None:
    print("FINITE MONOMIAL WINDOW ANISOTROPY FOR PRIME-LOG RELATION SEARCH")
    print("constants are log 2, log 3, log 5; no zeta(n) values are used")
    print()

    windows = [
        ("rectangular D=4", rectangular(4)),
        ("total-degree K=8", total_degree(8)),
        ("l2-ball R=6", l2_ball(6.0)),
    ]
    for name, window in windows:
        summarize_window(name, window)
    print()

    probes = [
        (8, 0, 0),
        (4, 4, 0),
        (3, 3, 3),
        (0, 0, 8),
    ]
    print("first exposure thresholds for selected exponent directions:")
    for alpha in probes:
        rect, deg, ball = first_exposure(alpha)
        print(
            f"  alpha={alpha}, |alpha|2={sqrt(sum(x*x for x in alpha)):.3f}, "
            f"value={monomial_value(alpha):.3e}: "
            f"rectD={rect}, totalK={deg}, ballR={ball}"
        )
    print()
    print("nearby false statements tested:")
    print("  false A: rectangular monomial cutoff is direction-neutral -> rejected")
    print("  false B: total-degree monomial cutoff is direction-neutral -> rejected")
    print("  qualified C: L2 exponent ball is nearly direction-neutral -> supported here, not a theorem")


if __name__ == "__main__":
    main()
