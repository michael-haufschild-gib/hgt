#!/usr/bin/env python3
"""
Attempt 10 NODE experiment.

NODE: full Hessian versus Gauss-Newton/Fisher approximations near saddles.

Constraint tested:
  For L(x)=1/2 r(x)^2, the full Hessian is r'(x)^2 + r(x) r''(x).
  Gauss-Newton keeps only r'(x)^2, so it is PSD and can miss negative
  curvature carried by the residual-curvature term.
"""

from __future__ import annotations

import numpy as np


def r(x: np.ndarray) -> np.ndarray:
    return x * x - 1.0


def rp(x: np.ndarray) -> np.ndarray:
    return 2.0 * x


def rpp(x: np.ndarray) -> np.ndarray:
    return np.full_like(x, 2.0)


def full_hessian(x: np.ndarray) -> np.ndarray:
    return rp(x) ** 2 + r(x) * rpp(x)


def gauss_newton(x: np.ndarray) -> np.ndarray:
    return rp(x) ** 2


def main() -> None:
    xs = np.linspace(-1.5, 1.5, 301)
    H = full_hessian(xs)
    G = gauss_newton(xs)
    neg = H < 0
    print("FULL HESSIAN VS GAUSS-NEWTON")
    print("loss L=1/2*(x^2-1)^2")
    print(f"  negative full-Hessian samples={int(np.sum(neg))}/{len(xs)}")
    print(f"  negative Gauss-Newton samples={int(np.sum(G < 0))}/{len(xs)}")
    print(f"  full Hessian min={float(np.min(H)):+.3f} at x={float(xs[np.argmin(H)]):+.3f}")
    print(f"  Gauss-Newton at that x={float(G[np.argmin(H)]):+.3f}")
    for x in [-0.8, -0.4, 0.0, 0.4, 0.8]:
        xx = np.array([x])
        print(
            f"  x={x:+.1f}: full_H={float(full_hessian(xx)[0]):+.3f}, "
            f"GN={float(gauss_newton(xx)[0]):+.3f}, "
            f"dropped={float((r(xx)*rpp(xx))[0]):+.3f}"
        )


if __name__ == "__main__":
    main()
