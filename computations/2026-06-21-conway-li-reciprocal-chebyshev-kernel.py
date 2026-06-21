#!/usr/bin/env python3
"""Li coefficient kernel in reciprocal seam coordinates.

For an FE pair rho=1/2+w and 1-rho=1/2-w, set y=-1/w^2.
The pair contribution to Li's lambda_n is

    L_n(y) = 2 - (q^n + q^(-n)),
    q = (w-1/2)/(w+1/2).

This script verifies

    L_n(y) = 2 - 2 * ChebyshevT(n, (4-y)/(4+y)),

and prints the Taylor kernel coefficients in y. Hence lambda_n is an
infinite, exponentially decaying kernel transform of the reciprocal seam
moments T_k, not a finite triangular transform in the T_k chart.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    w, y = sp.symbols("w y")
    q = (w - sp.Rational(1, 2)) / (w + sp.Rational(1, 2))
    y_of_w = -1 / (w * w)
    x_of_y = (4 - y) / (4 + y)

    print("FE-pair Li contribution in y=-w^-2")
    for n in range(1, 8):
        li_pair_w = 2 - (q**n + q**(-n))
        cheb_y = 2 - 2 * sp.chebyshevt(n, x_of_y)
        pulled = sp.simplify(cheb_y.subs(y, y_of_w))
        ok = sp.simplify(li_pair_w - pulled) == 0
        print(f"n={n}: formula_ok={ok}")

    print()
    print("Taylor coefficients L_n(y)=sum_{k>=1} c[n,k] y^k at y=0:")
    for n in range(1, 7):
        expr = 2 - 2 * sp.chebyshevt(n, x_of_y)
        coeffs = [sp.simplify(sp.series(expr, y, 0, 9).removeO().coeff(y, k)) for k in range(1, 9)]
        print(f"n={n}: {coeffs}")

    print()
    print("All displayed kernels have zero constant term and denominator singularity at y=-4.")
    print("For xi, |y_rho|=|rho-1/2|^-2 << 4, so the Taylor kernel is the reciprocal-moment chart.")


if __name__ == "__main__":
    main()
