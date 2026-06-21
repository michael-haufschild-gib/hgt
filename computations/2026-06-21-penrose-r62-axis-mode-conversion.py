#!/usr/bin/env python3
"""R62: interface mode conversion as a two-axis orthogonality warning.

NODE: mode conversion at interfaces and defects.

Target: the landscape's two orthogonal axes: weld/constraint versus
positivity/localization.  Dependency-chain test: an FE-symmetric off-line
zero quartet preserves the weld axis while creating a positivity defect.
"""

from __future__ import annotations

from math import exp
from typing import Tuple

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
    print("\nNODE validation: two-mode interface conversion")
    # Coupled-mode scattering at an interface. kappa=0 means no conversion.
    for kappa in [0.0, 0.05, 0.20, 0.50, 1.00]:
        conversion = (kappa * kappa) / (1.0 + kappa * kappa)
        transmission_same = 1.0 / (1.0 + kappa * kappa)
        print(f"  interface coupling={kappa:4.2f}: same-mode={transmission_same:.4f}, converted={conversion:.4f}")


def quartet_poly(s: complex, a: float, gamma: float) -> complex:
    roots = [
        complex(0.5 + a, gamma),
        complex(0.5 + a, -gamma),
        complex(0.5 - a, gamma),
        complex(0.5 - a, -gamma),
    ]
    out = 1 + 0j
    for root in roots:
        out *= s - root
    return out


def log_abs_second_on_line(t: float, a: float, gamma: float, h: float = 1e-4) -> float:
    def y(x: float) -> float:
        return np.log(abs(quartet_poly(complex(0.5, x), a, gamma)))

    return float((y(t + h) - 2 * y(t) + y(t - h)) / (h * h))


def target_test() -> None:
    print("\nTarget test: FE-symmetric off-line quartet separates axes")
    print("  a      FE_residual_max    center_curvature    expected_curvature")
    gamma = 20.0
    for a in [0.03, 0.06, 0.12, 0.24]:
        ts = np.linspace(gamma - 1.0, gamma + 1.0, 21)
        fe_residuals = []
        for t in ts:
            s = complex(0.5 + 0.17, t)
            fe_residuals.append(abs(quartet_poly(s, a, gamma) - quartet_poly(1 - s, a, gamma)))
        curvature = log_abs_second_on_line(gamma, a, gamma)
        expected = 2.0 / (a * a)
        print(f"  {a:4.2f}     {max(fe_residuals):12.3e}     {curvature:14.6f}     {expected:14.6f}")


def main() -> None:
    node = "mode conversion at interfaces and defects"
    attempts = [
        "defects convert weld-symmetric modes into positivity failures",
        "interface conversion separates constraint and localization axes",
        "off-line quartet preserves FE weld while changing positivity mode",
    ]
    print("R62 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    target_test()

    print("\nDependency chain:")
    print("  FE symmetry of the quartet is exact; positivity failure is read by")
    print("  the positive center curvature 2/a^2. This is the existing two-axis")
    print("  orthogonality witness, not a new bridge between the axes.")


if __name__ == "__main__":
    main()
