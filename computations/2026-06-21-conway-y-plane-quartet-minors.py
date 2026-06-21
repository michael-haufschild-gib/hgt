#!/usr/bin/env python3
"""Coordinate-free y-plane form of the off-line quartet shifted minors."""

from __future__ import annotations

import sympy as sp


u, v, mu, a, g = sp.symbols("u v mu a g", nonzero=True, real=True)
y = u + sp.I * v
yb = u - sp.I * v


def moment(k: int) -> sp.Expr:
    return sp.expand(mu * (y**k + yb**k))


def main() -> None:
    T = {k: moment(k) for k in range(1, 5)}
    d0 = sp.factor(T[1] * T[3] - T[2] ** 2)
    d1 = sp.factor(T[2] * T[4] - T[3] ** 2)
    print("y-plane conjugate-pair shifted minors")
    print("=" * 48)
    print("T_k = mu * (y^k + conjugate(y)^k), y = u + i v")
    print(f"det H_1^(0) = {d0}")
    print(f"det H_1^(1) = {d1}")
    print()

    y_ag = -1 / (a + sp.I * g) ** 2
    u_ag = sp.simplify(sp.re(y_ag))
    v_ag = sp.simplify(sp.im(y_ag))
    r2_ag = sp.simplify(u_ag**2 + v_ag**2)
    d0_ag = sp.factor(d0.subs({u: u_ag, v: v_ag, mu: 2}))
    d1_ag = sp.factor(d1.subs({u: u_ag, v: v_ag, mu: 2}))
    print("For a simple FE/conjugation quartet w = ±a ± i gamma, mu=2:")
    print(f"Re(y) = {u_ag}")
    print(f"Im(y) = {v_ag}")
    print(f"|y|^2 = {r2_ag}")
    print(f"det H_1^(0) = {d0_ag}")
    print(f"det H_1^(1) = {d1_ag}")
    print()
    print("Read: for a genuine off-line quartet with a*gamma != 0, Im(y) != 0,")
    print("so both shifted degree-one minors are strictly negative.")


if __name__ == "__main__":
    main()
