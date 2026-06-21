#!/usr/bin/env python3
"""Admissible-domain check for the reciprocal-seam T0 obstruction.

Toy support y_n = 1/n^2 has infinite total mass but finite positive
moments T_k for k >= 1. The script checks three facts relevant to the
shifted proof route:

1. An unshifted form on all polynomials needs an arbitrary T0 finite part.
2. The raw unshifted form is finite on the canonical ideal y R[y].
3. On that ideal, p(y)=y q(y), the raw unshifted form is exactly Q1[q].
"""

from __future__ import annotations

import numpy as np


def moments(n_terms: int, max_k: int) -> np.ndarray:
    n = np.arange(1, n_terms + 1, dtype=np.float64)
    y = 1.0 / (n * n)
    out = np.empty(max_k + 1)
    out[0] = float(n_terms)
    for k in range(1, max_k + 1):
        out[k] = float(np.sum(y**k))
    return out


def hankel(ts: np.ndarray, shift: int, d: int) -> np.ndarray:
    return np.array([[ts[i + j + shift] for j in range(d + 1)] for i in range(d + 1)])


def inertia(a: np.ndarray, tol: float = 1e-10) -> tuple[int, int, int]:
    vals = np.linalg.eigvalsh(a)
    return (
        int(np.sum(vals < -tol)),
        int(np.sum(np.abs(vals) <= tol)),
        int(np.sum(vals > tol)),
    )


def main() -> None:
    d = 3
    ns = [20, 100, 500, 5000]
    print("Toy divisor: y_n=1/n^2, counting measure")
    print("T0(N) diverges; shifted T_k, k>=1, converge.")
    for n_terms in ns:
        ts = moments(n_terms, 2 * d + 4)
        h_q0 = hankel(ts, shift=1, d=d)
        h_q1 = hankel(ts, shift=2, d=d)

        # The unshifted form restricted to the ideal y R[y], basis
        # y, y^2, ..., y^(d+1), has entries T_{i+j+2}.
        h_unshifted_on_ideal = np.array(
            [[ts[(i + 1) + (j + 1)] for j in range(d + 1)] for i in range(d + 1)]
        )

        print()
        print(f"N={n_terms}")
        print(f"  T0={ts[0]:.0f}, T1={ts[1]:.12f}, T2={ts[2]:.12f}")
        print(f"  max|unshifted ideal - Q1|={np.max(np.abs(h_unshifted_on_ideal - h_q1)):.3e}")
        print(f"  inertia Q0={inertia(h_q0)}, inertia Q1={inertia(h_q1)}")

    print()
    print("Renormalized T0 finite part is extra data.")
    ts = moments(5000, 4)
    threshold = ts[1] * ts[1] / ts[2]
    for finite_part in [0.0, 0.5 * threshold, threshold, 2.0 * threshold]:
        h = np.array([[finite_part, ts[1]], [ts[1], ts[2]]])
        print(
            f"  T0^ren={finite_part:.12f}, det={np.linalg.det(h): .12e}, inertia={inertia(h)}"
        )

    print()
    print("Conclusion:")
    print("  Full unshifted tests require a chosen T0 finite part.")
    print("  The canonical finite raw domain is y R[y].")
    print("  Under p=y q, that domain-restricted form is exactly Q1[q].")


if __name__ == "__main__":
    main()
