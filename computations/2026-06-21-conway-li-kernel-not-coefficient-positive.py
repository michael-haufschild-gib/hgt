#!/usr/bin/env python3
"""First Li reciprocal-kernel coefficients.

For L_n(y)=2-2*T_n((4-y)/(4+y)), the Taylor coefficients at y=0 begin

    c_{n,1} = n^2
    c_{n,2} = -n^2 (n^2+2) / 12.

Thus every Li kernel with n>=1 has a negative coefficient in the
reciprocal moment basis. The Li chart is not a coefficientwise-positive
linear transform of the T_k chart.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    n, y = sp.symbols("n y", integer=True, positive=True)
    c1 = n**2
    c2 = -n**2 * (n**2 + 2) / 12
    print(f"c[n,1] = {sp.factor(c1)}")
    print(f"c[n,2] = {sp.factor(c2)}")
    print()
    print("Checks against direct Taylor expansion:")
    for n0 in range(1, 9):
        expr = 2 - 2 * sp.chebyshevt(n0, (4 - y) / (4 + y))
        series = sp.series(expr, y, 0, 3).removeO()
        direct_c1 = sp.simplify(series.coeff(y, 1))
        direct_c2 = sp.simplify(series.coeff(y, 2))
        print(
            f"n={n0}: c1={direct_c1}, formula={c1.subs(n,n0)}, "
            f"c2={direct_c2}, formula={sp.simplify(c2.subs(n,n0))}"
        )


if __name__ == "__main__":
    main()
