#!/usr/bin/env python3
"""Workflow test for IV7 through boundary steady states.

ResearchNode formula:
    |p^{-s}| = p^{-1/2} iff Re(s)=1/2.

Random NODE:
    Boundary steady states where one or more species concentrations approach zero.
"""

from __future__ import annotations

import cmath
import math

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        cur = [i]
        for j, cb in enumerate(b, start=1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def logistic_boundary(x0: float, steps: int = 20) -> list[float]:
    xs = [x0]
    x = x0
    for _ in range(steps):
        x = x + 0.2 * x * (1 - x) - 0.4 * x
        xs.append(x)
    return xs


def main() -> None:
    base_test = "test boundary steady state where concentration approaches zero"
    attempts = [
        ("A", "test compactified Bohr coordinate boundary x_p equals zero"),
        ("B", "test critical modulus shell after boundary unit normalization"),
        ("C", "test nearby false statements with x_p not in C-star"),
    ]
    print("STEP 8 Levenshtein transfer attempts")
    print("=" * 42)
    scored = [(tag, levenshtein(base_test, text), text) for tag, text in attempts]
    for tag, score, text in scored:
        print(f"{tag}: distance={score}, attempt={text}")
    chosen = min(scored, key=lambda row: row[1])
    print(f"chosen={chosen[0]} by minimum distance")
    print()

    print("NODE toy: boundary steady state at zero")
    print("=" * 44)
    xs = logistic_boundary(0.05)
    print(f"x0={xs[0]:.6f}, x_end={xs[-1]:.6f}, min={min(xs):.6f}")
    print("The boundary state x=0 is invariant but not an interior positive state.")
    print()

    print("STEP 9 method 22: nearby false statements")
    print("=" * 54)
    p = 3.0
    samples = [0.25 + 4j, 0.5 + 4j, 0.75 + 4j]
    for s in samples:
        x = p ** (-s)
        lhs = abs(x)
        target = p ** (-0.5)
        print(
            f"s={s}: |p^-s|={lhs:.12f}, target={target:.12f}, "
            f"Re(s)={s.real:.2f}"
        )
    print()
    boundary_points = [0j, complex(np.inf, 0), complex(np.nan, np.nan)]
    for x in boundary_points:
        try:
            s_rec = -cmath.log(x) / math.log(p)
            status = f"recovered s={s_rec}"
        except Exception as exc:
            status = f"no logarithmic coordinate ({type(exc).__name__})"
        print(f"compactified x={x}: {status}")

    print()
    print("Interpretation:")
    print(
        "IV7 is an interior C* statement for x_p=p^{-s}. Boundary or "
        "compactified states such as x_p=0 do not supply counterexamples; "
        "they leave the logarithmic s-coordinate chart. This is the existing "
        "boundary-modulus critical-line lemma, not new content."
    )


if __name__ == "__main__":
    main()
