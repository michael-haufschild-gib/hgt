#!/usr/bin/env python3
"""Shifted Hankel minors for an FE-symmetric off-line quartet.

The quartet in seam coordinates is w = +/- a +/- i gamma. In reciprocal
coordinates y = -1/w^2. This script symbolically computes the first shifted
moments and the 2x2 determinants for

    H_0 = [[T1,T2],[T2,T3]]
    H_1 = [[T2,T3],[T3,T4]]

showing that both determinants are strictly negative whenever a*gamma != 0.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    a, gamma = sp.symbols("a gamma", positive=True, real=True)
    ws = [
        a + sp.I * gamma,
        -a + sp.I * gamma,
        a - sp.I * gamma,
        -a - sp.I * gamma,
    ]
    ys = [-1 / (w * w) for w in ws]
    t = [sum(sp.simplify(y**k) for y in ys) for k in range(1, 5)]

    print("Quartet: w = +/- a +/- i gamma, y=-1/w^2")
    for i, value in enumerate(t, start=1):
        print(f"T_{i} = {sp.factor(sp.simplify(value))}")

    h0 = sp.Matrix([[t[0], t[1]], [t[1], t[2]]])
    h1 = sp.Matrix([[t[1], t[2]], [t[2], t[3]]])
    det_h0 = sp.factor(sp.simplify(h0.det()))
    det_h1 = sp.factor(sp.simplify(h1.det()))

    print()
    print(f"det H_0(1) = {det_h0}")
    print(f"det H_1(1) = {det_h1}")
    print()
    print("For a>0 and gamma>0 both determinants are strictly negative.")
    print("At a=0 the quartet collapses to on-line duplicated atoms and the minors are PSD-rank-one.")


if __name__ == "__main__":
    main()
