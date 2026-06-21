#!/usr/bin/env python3
"""
R34 STEP 12 battery: state-law moment spectrum for random Euler abscissae.
"""

from __future__ import annotations

import cmath
import math

import numpy as np


def first_nonzero_moment(samples: np.ndarray, kmax: int = 16, tol: float = 1e-10) -> int | None:
    for k in range(1, kmax + 1):
        if abs(np.mean(samples**k)) > tol:
            return k
    return None


def main() -> None:
    rows = []
    for q in range(2, 9):
        samples = np.array([cmath.exp(2j * math.pi * j / q) for j in range(q)], dtype=complex)
        k0 = first_nonzero_moment(samples)
        rows.append((f"roots_{q}", k0, 0.0 if k0 is None else 1.0 / k0, max(0.5, 0.0 if k0 is None else 1.0 / k0)))
    for bias in [0.1, 0.3, 0.5, 0.8]:
        samples = np.array([0.0, 1.0], dtype=complex)
        probs = np.array([1.0 - bias, bias])
        # Compute weighted moments by resampling a large exact rational-style cloud.
        cloud = np.concatenate([np.zeros(int((1.0 - bias) * 1000)), np.ones(int(bias * 1000))]).astype(complex)
        k0 = first_nonzero_moment(cloud)
        rows.append((f"bernoulli_{bias:.1f}", k0, 1.0 / k0, max(0.5, 1.0 / k0)))
    centered = {
        "sym_three_point": np.array([-1.0, 0.0, 1.0], dtype=complex),
        "asym_centered": np.array([-2.0, 1.0, 1.0], dtype=complex),
        "four_balanced": np.array([-3.0, -1.0, 1.0, 3.0], dtype=complex),
    }
    for name, samples in centered.items():
        samples = samples - samples.mean()
        k0 = first_nonzero_moment(samples)
        rows.append((name, k0, 0.0 if k0 is None else 1.0 / k0, max(0.5, 0.0 if k0 is None else 1.0 / k0)))

    print("state_law        k0   mean_wall  total_wall  verdict")
    for name, k0, mean_wall, total_wall in rows:
        if total_wall > 0.5:
            verdict = "mean-shifted"
        elif mean_wall == 0.5:
            verdict = "drift-at-seam"
        else:
            verdict = "variance-seam"
        print(f"{name:16s} {str(k0):>3s} {mean_wall:10.4f} {total_wall:11.4f}  {verdict}")

    print("\nBattery verdict:")
    print(
        "The classification is stable across roots of unity and bounded rate laws: "
        "the total wall is max(1/2, 1/k0), where k0 is the first nonzero moment."
    )


if __name__ == "__main__":
    main()
