#!/usr/bin/env python3
"""Schur thresholds for finite T0 repairs of an infinite-mass tower.

For moments m_k = sum_{n>=1} (1/n^2)^k = zeta(2k), k>=1, ask:

    What finite value a=m_0 would make the unshifted Hankel block
    [m_{i+j}]_{i,j=0}^d positive semidefinite?

If the lower-right block is positive definite, the answer is the Schur
threshold a_d = b_d^T C_d^{-1} b_d. Any finite T0 repair must satisfy
a >= a_d for every d. The thresholds diverge, so no finite T0 can repair
the full unshifted tower.
"""

from __future__ import annotations

import mpmath as mp
import sympy as sp


def exact_thresholds(max_d: int) -> None:
    print("Exact symbolic Schur thresholds for m_k=zeta(2k):")
    for d in range(1, max_d + 1):
        c = sp.Matrix([[sp.zeta(2 * ((i + 1) + (j + 1))) for j in range(d)] for i in range(d)])
        b = sp.Matrix([sp.zeta(2 * (i + 1)) for i in range(d)])
        a_d = sp.simplify((b.T * c.inv() * b)[0])
        formula = sp.Rational(d * (2 * d + 3), 2)
        print(f"  d={d:2d}: a_d={a_d}, formula={formula}, match={sp.simplify(a_d-formula)==0}")


def numeric_thresholds(max_d: int) -> None:
    mp.mp.dps = 90
    print()
    print("High-precision continuation:")
    for d in range(1, max_d + 1):
        c = mp.matrix(d)
        b = mp.matrix(d, 1)
        for i in range(d):
            b[i] = mp.zeta(2 * (i + 1))
            for j in range(d):
                c[i, j] = mp.zeta(2 * ((i + 1) + (j + 1)))
        x = mp.lu_solve(c, b)
        a_d = (b.T * x)[0]
        print(f"  d={d:2d}: a_d={mp.nstr(a_d, 25)}")


def failure_degree_for_finite_part(a: float) -> int:
    d = 1
    while d * (2 * d + 3) / 2 <= a:
        d += 1
    return d


def main() -> None:
    exact_thresholds(8)
    numeric_thresholds(18)
    print()
    print("Finite T0 repairs fail once the Schur threshold exceeds them:")
    for a in [10.0, 50.0, 100.0, 500.0]:
        d = failure_degree_for_finite_part(a)
        threshold = d * (2 * d + 3) / 2
        print(f"  T0^ren={a:6.1f}: first forced failure d={d}, threshold={threshold:.1f}")


if __name__ == "__main__":
    main()
