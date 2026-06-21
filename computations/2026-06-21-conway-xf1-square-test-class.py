#!/usr/bin/env python3
"""Exponent audit for XF1 versus reciprocal seam square tests.

For the shifted square-test forms under the on-line coordinate y = gamma^-2,
the zero-side test functions have the shape

    h_{r,p}(t) = t^(-2r) p(t^(-2))^2,  r = 1 or 2.

This script records the two endpoint exponents.  It is not a numerical
experiment; it is an audit trail for the elementary obstruction.
"""

from __future__ import annotations


def degree(coeffs: list[int]) -> int:
    for i in range(len(coeffs) - 1, -1, -1):
        if coeffs[i] != 0:
            return i
    raise ValueError("zero polynomial")


def order_at_zero(coeffs: list[int]) -> int:
    for i, coeff in enumerate(coeffs):
        if coeff != 0:
            return i
    raise ValueError("zero polynomial")


def audit(name: str, coeffs: list[int]) -> None:
    deg = degree(coeffs)
    ord0 = order_at_zero(coeffs)
    print(f"p(u) = {name}")
    print(f"  degree(p) = {deg}; order_0(p) = {ord0}")
    for r in (1, 2):
        hard_edge_alpha = 2 * r + 4 * deg
        infinity_alpha = 2 * r + 4 * ord0
        print(f"  r={r}:")
        print(f"    t -> 0:        h(t) ~ C |t|^(-{hard_edge_alpha})")
        print("                   not locally integrable at the hard edge")
        print(f"    |t| -> infinity: h(t) ~ C |t|^(-{infinity_alpha})")
        print("                   only polynomial decay, hence not Schwartz")
    print()


def main() -> None:
    print("XF1 reciprocal square-test admissibility audit")
    print("=" * 52)
    print("h_{r,p}(t) = t^(-2r) p(t^(-2))^2, r in {1,2}")
    print()
    audit("1", [1])
    audit("1 + 2u + u^2", [1, 2, 1])
    audit("u - 3u^3", [0, 1, 0, -3])
    print("General nonzero p:")
    print("  If deg(p)=d, then h(t) has hard-edge order 2r+4d >= 2.")
    print("  If ord_0(p)=j, then h(t) decays at infinity like |t|^-(2r+4j).")
    print("  Therefore direct standard explicit-formula substitution is invalid.")


if __name__ == "__main__":
    main()
