#!/usr/bin/env python3
"""
Workflow NODE: hard-edge beta/Bessel limits depend on boundary conditions.

Proof-route transfer: attack the false claim "the source-built bulk form alone
determines kappa_-".  In a finite hard-edge model the same positive bulk
operator acquires different negative index after changing only a rank-one
boundary extension.  The exact threshold is the rank-one inertia formula:

    B + alpha vv^T is PSD iff 1 + alpha <v, B^{-1}v> >= 0.

So any source-built kappa_- construction must include the archimedean/pole
boundary extension as part of the object; a bulk explicit-formula kernel alone
does not define the faithful index.
"""

from __future__ import annotations

import numpy as np


def hard_edge_bulk(n: int, bessel_g: float) -> np.ndarray:
    """Positive finite-difference inverse-square hard-edge bulk on (0, 1]."""
    h = 1.0 / (n + 1)
    main = np.full(n, 2.0 / (h * h))
    off = np.full(n - 1, -1.0 / (h * h))
    mat = np.diag(main) + np.diag(off, 1) + np.diag(off, -1)
    x = h * np.arange(1, n + 1)
    mat += np.diag(bessel_g / (x * x))
    return mat


def inertia(a: np.ndarray, tol: float = 1e-9) -> tuple[int, int, int, float]:
    vals = np.linalg.eigvalsh(a)
    neg = int(np.sum(vals < -tol))
    zero = int(np.sum(np.abs(vals) <= tol))
    pos = int(np.sum(vals > tol))
    return neg, zero, pos, float(vals[0])


def main() -> None:
    n = 80
    bessel_g = 0.75
    bulk = hard_edge_bulk(n, bessel_g)
    v = np.zeros((n, 1))
    v[0, 0] = 1.0

    q = float((v.T @ np.linalg.solve(bulk, v))[0, 0])
    alpha_critical = -1.0 / q

    print("=== hard-edge boundary-extension kappa stress test ===")
    print(f"bulk size n={n}, inverse-square g={bessel_g}")
    print(f"bulk inertia (neg,zero,pos,min) = {inertia(bulk)}")
    print(f"rank-one boundary vector v=e_1, q=<v,B^-1v>={q:.10e}")
    print(f"critical alpha = -1/q = {alpha_critical:.10e}")
    print()
    print("same bulk, only boundary extension alpha*v*v^T changes:")
    for scale in [0.50, 0.90, 0.99, 1.00, 1.01, 1.10, 1.50]:
        alpha = scale * alpha_critical
        extended = bulk + alpha * (v @ v.T)
        print(
            f"  alpha={scale:4.2f}*alpha_c -> "
            f"inertia={inertia(extended)}"
        )

    print()
    print("interpretation:")
    print("- The interior hard-edge expression is unchanged.")
    print("- The faithful negative index changes solely through the boundary extension.")
    print("- For source-built kappa_-, the Γ/pole/edge boundary condition is load-bearing.")
    print("- A source bulk kernel without its boundary domain does not define an index.")


if __name__ == "__main__":
    main()
