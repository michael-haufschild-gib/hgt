#!/usr/bin/env python3
"""R44: small-system temperature ambiguity at the Fisher signature wall.

NODE: temperature is not always a sharply defined state variable for a small
nonequilibrium system.

Target: Fisher signature wall, where the analytic norm zeta(2 sigma) changes
sign at sigma=1/2 while finite positive cutoffs cannot.

The experiment compares raw finite norms

    Z_X(a) = sum_{n <= X} n^{-a}, a = 2 sigma

with two simple Euler-Maclaurin renormalizations that subtract the finite bath:

    R0_X(a) = Z_X(a) - X^{1-a}/(1-a)
    R1_X(a) = R0_X(a) - 0.5 X^{-a}

near a=1.  The raw finite "temperature" is always positive; the signature
wall only appears after a chosen reservoir subtraction.
"""

from __future__ import annotations

from math import log
from typing import Iterable, List, Sequence, Tuple

import mpmath as mp

mp.mp.dps = 50


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


def partial_zeta(a: float, x: int) -> float:
    return float(mp.nsum(lambda k: k ** (-a), [1, x]))


def renormalized(a: float, x: int) -> Tuple[float, float]:
    raw = partial_zeta(a, x)
    reservoir = float(mp.power(x, 1 - a) / (1 - a))
    r0 = raw - reservoir
    r1 = r0 - 0.5 * float(mp.power(x, -a))
    return r0, r1


def sign(v: float) -> str:
    if v > 0:
        return "+"
    if v < 0:
        return "-"
    return "0"


def table() -> None:
    xs = [100, 1000, 10000]
    sigmas = [0.45, 0.48, 0.49, 0.495, 0.505, 0.51, 0.52, 0.55]
    print("\nSignature table near sigma=1/2:")
    for x in xs:
        print(f"  X={x}")
        for sigma in sigmas:
            a = 2 * sigma
            raw = partial_zeta(a, x)
            r0, r1 = renormalized(a, x)
            analytic = float(mp.zeta(a))
            print(
                f"    sigma={sigma:.3f} a={a:.3f}: "
                f"raw={raw: .6f}({sign(raw)}), "
                f"R0={r0: .6f}({sign(r0)}), "
                f"R1={r1: .6f}({sign(r1)}), "
                f"zeta={analytic: .6f}({sign(analytic)})"
            )


def crossing_estimates() -> None:
    xs = [100, 300, 1000, 3000, 10000]
    grid = [0.45 + j * 0.0005 for j in range(201)]
    print("\nFirst positive finite-renormalized sign after the wall:")
    for x in xs:
        first_r0 = None
        first_r1 = None
        for sigma in grid:
            a = 2 * sigma
            if abs(a - 1.0) < 1e-12:
                continue
            r0, r1 = renormalized(a, x)
            if sigma > 0.5 and first_r0 is None and r0 > 0:
                first_r0 = sigma
            if sigma > 0.5 and first_r1 is None and r1 > 0:
                first_r1 = sigma
        print(
            f"  X={x:5d}: R0 first positive sigma={first_r0}, "
            f"R1 first positive sigma={first_r1}, "
            f"1/log(X)={1/log(x):.6f}"
        )


def main() -> None:
    node = "temperature is not always a sharply defined state variable for a small nonequilibrium system"
    attempts = [
        "finite Fisher temperature depends on reservoir subtraction",
        "raw finite norm cannot see the zeta signature wall",
        "small cutoff Fisher wall is a renormalization-choice ambiguity",
    ]
    print("R44 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")
    table()
    crossing_estimates()
    print("\nInterpretation:")
    print("  A finite positive cutoff has no negative signature at all.")
    print("  The wall appears only after subtracting an environment/reservoir term.")
    print("  Near sigma=1/2 the apparent finite wall is therefore a cutoff/renormalization diagnostic, not a new RH signal.")


if __name__ == "__main__":
    main()
