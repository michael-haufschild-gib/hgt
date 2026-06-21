#!/usr/bin/env python3
"""R66: screened off-line curvature as a positivity/localization detector.

NODE: substrate friction screens hydrodynamic interactions between active
matter defects.

Target: positivity/localization axis.  Strengthened test: apply an exponential
screening length to the off-line quartet curvature kernel.  Screening should
suppress negative wings and leave a positive localized mass if the core is a
real off-line defect signal.
"""

from __future__ import annotations

from math import exp

import numpy as np


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_validation() -> None:
    print("\nNODE validation: screened interaction length")
    for friction in [0.1, 0.2, 0.5, 1.0, 2.0]:
        screening_len = 1.0 / friction
        interaction_at_5 = exp(-5.0 / screening_len)
        print(f"  friction={friction:4.1f}: screening_len={screening_len:5.2f}, interaction(r=5)={interaction_at_5:.5f}")


def curvature(a: float, tau: np.ndarray) -> np.ndarray:
    return 2.0 * (a * a - tau * tau) / ((a * a + tau * tau) ** 2)


def screened_mass(a: float, lam: float) -> float:
    # integrate over a large symmetric window; scaling by a makes rows comparable.
    span = 80 * max(a, lam)
    xs = np.linspace(-span, span, 240_001)
    vals = curvature(a, xs) * np.exp(-np.abs(xs) / lam)
    return float(np.trapezoid(vals, xs))


def target_test() -> None:
    print("\nTarget test: exponential screening of off-line curvature C_a")
    print("  lambda/a     a*screened_mass(a=.1)   a*screened_mass(a=.2)")
    for q in [0.10, 0.20, 0.50, 1.00, 2.00, 5.00, 10.00, 50.00]:
        row = []
        for a in [0.1, 0.2]:
            mass = screened_mass(a, q * a)
            row.append(a * mass)
        print(f"   {q:7.2f}        {row[0]:14.8f}        {row[1]:14.8f}")
    print("  unscreened whole-line mass: 0 (analytic zero-area kernel)")


def main() -> None:
    node = "the role of substrate friction in screening hydrodynamic interactions between defects"
    attempts = [
        "screening suppresses negative curvature wings and reveals positive core",
        "positivity localization depends on screening length relative to defect width",
        "friction turns zero-area off-line curvature into a localized positive mass",
    ]
    print("R66 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    target_test()

    print("\nInterpretation:")
    print("  Exponential screening creates a positive localized mass from the")
    print("  sign-changing off-line curvature kernel, with scale set by lambda/a.")
    print("  This is a useful detector family but overlaps the existing localization")
    print("  width/passport results.")


if __name__ == "__main__":
    main()
