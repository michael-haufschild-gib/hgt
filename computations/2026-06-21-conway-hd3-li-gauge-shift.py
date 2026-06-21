"""HD3 zero-free gauge contribution to Li-style coefficients."""

from __future__ import annotations

import sympy as sp


s, c = sp.symbols("s c")


def li_delta_for_Q(Q: sp.Expr, n: int) -> sp.Expr:
    expr = s ** (n - 1) * Q
    return sp.simplify(sp.diff(expr, s, n).subs(s, 1) / sp.factorial(n - 1))


def main() -> None:
    w = s - sp.Rational(1, 2)
    Q = c * w**2
    print("FORMULA: HD3 zero-free FE gauge F=e^{c(s-1/2)^2} xi")
    print("Li-style additive contribution:")
    print("  delta_lambda_n(Q) = 1/(n-1)! d^n/ds^n [s^(n-1) Q(s)] at s=1")
    print()
    print("n symbolic_delta expected_c_n^2 match")
    for n in range(1, 11):
        delta = sp.expand(li_delta_for_Q(Q, n))
        expected = c * n * n
        print(f"{n:2d} {str(delta):>18s} {str(expected):>14s} {delta == expected}")

    print()
    print("VERDICT")
    print("  The quadratic HD3 gauge adds c*n^2 to every Li-style coefficient.")
    print("  The zero divisor is unchanged, so unnormalized log-defined Li coefficients are gauge-dependent.")


if __name__ == "__main__":
    main()
