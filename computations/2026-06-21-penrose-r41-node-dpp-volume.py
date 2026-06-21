#!/usr/bin/env python3
"""
R41 NODE validation: determinant probability is squared volume, suppressed by near-linear dependence.
"""

from __future__ import annotations

import numpy as np


def main() -> None:
    print("epsilon  det_gram  squared_area")
    e1 = np.array([1.0, 0.0])
    for eps in [1.0, 0.5, 0.2, 0.1, 0.05, 0.01]:
        v2 = np.array([1.0, eps])
        gram = np.array([[np.dot(e1, e1), np.dot(e1, v2)], [np.dot(v2, e1), np.dot(v2, v2)]])
        print(f"{eps:7.3f} {np.linalg.det(gram):9.6f} {eps*eps:13.6f}")
    print("\nNODE verdict: the determinant suppresses near-collinear selections quadratically.")


if __name__ == "__main__":
    main()
