#!/usr/bin/env python3
"""
R35 NODE validation: Parisi order parameter is a function q(x), not one scalar.
"""

from __future__ import annotations

import numpy as np


def profile(kind: str, x: np.ndarray) -> np.ndarray:
    if kind == "replica_symmetric":
        return np.full_like(x, 0.62)
    if kind == "one_step":
        return np.where(x < 0.55, 0.25, 0.62)
    if kind == "full_rsb":
        y = 0.18 + 0.44 * x**1.7
        return np.minimum(y, 0.62)
    if kind == "delayed_full_rsb":
        y = 0.08 + 0.54 / (1 + np.exp(-12 * (x - 0.62)))
        return np.minimum(y, 0.62)
    raise ValueError(kind)


def main() -> None:
    x = np.linspace(0, 1, 501)
    print("profile              q_EA     mean_q    var_q     int_q2    max_slope")
    for kind in ["replica_symmetric", "one_step", "full_rsb", "delayed_full_rsb"]:
        q = profile(kind, x)
        slope = np.max(np.abs(np.diff(q) / np.diff(x)))
        print(
            f"{kind:20s} {q[-1]:7.4f} {np.trapezoid(q, x):9.4f} {np.var(q):8.5f} "
            f"{np.trapezoid(q * q, x):9.4f} {slope:10.4f}"
        )
    print("\nNODE verdict:")
    print(
        "Several profiles share the same endpoint q_EA=0.62 but have different means, "
        "variance, q^2 mass, and hierarchy/slope structure. The functional profile is "
        "the order parameter; the scalar endpoint is not enough."
    )


if __name__ == "__main__":
    main()
