#!/usr/bin/env python3
"""
Attempt 9 NODE experiment.

NODE: +1/2 and -1/2 nematic defects differ geometrically and dynamically.

Constraint tested:
  Absolute defect magnitude |q| is not enough.  The signed half-charge changes
  the director-field symmetry: +1/2 defects carry a polar first harmonic,
  while -1/2 defects carry a threefold harmonic.
"""

from __future__ import annotations

import math

import numpy as np


def q_tensor_phase(theta: np.ndarray, q: float, psi: float = 0.0) -> np.ndarray:
    angle = q * theta + psi
    return np.exp(2j * angle)


def harmonic_moment(theta: np.ndarray, qphase: np.ndarray, k: int) -> complex:
    return complex(np.mean(qphase * np.exp(-1j * k * theta)))


def winding(theta: np.ndarray, q: float) -> float:
    angle = q * theta
    unwrapped = np.unwrap(angle)
    return float((unwrapped[-1] - unwrapped[0]) / (2 * math.pi))


def summarize(q: float) -> None:
    theta = np.linspace(0, 2 * math.pi, 720, endpoint=False)
    qphase = q_tensor_phase(theta, q)
    m_plus = harmonic_moment(theta, qphase, 1)
    m_minus = harmonic_moment(theta, qphase, -1)
    print(f"q={q:+.1f}")
    print(f"  abs_charge={abs(q):.1f}, winding≈{winding(theta, q):+.3f}")
    print(f"  |Q harmonic +1|={abs(m_plus):.6f}")
    print(f"  |Q harmonic -1|={abs(m_minus):.6f}")
    print()


def main() -> None:
    print("HALF-DEFECT SIGN: SAME DENSITY, DIFFERENT GEOMETRY")
    print()
    summarize(+0.5)
    summarize(-0.5)


if __name__ == "__main__":
    main()
