#!/usr/bin/env python3
"""Exact symbolic route-selection calculations for two modular seam gates.

Outputs are research diagnostics only.  They must not be imported into Lean proofs.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp


H, Z, R, P = sp.symbols("H Z R P")
U, B, Q = sp.symbols("U B Q")
X, Y = sp.symbols("X Y")


def rational_json(value: sp.Expr) -> str:
    return str(sp.factor(value))


def poly_record(poly: sp.Expr, var: sp.Symbol) -> dict:
    p = sp.Poly(sp.factor(poly), var, domain=sp.QQ)
    return {
        "degree": p.degree(),
        "factor": str(sp.factor(p.as_expr())),
        "coefficients_descending": [str(c) for c in p.all_coeffs()],
        "positive_coefficients": all(c > 0 for c in p.all_coeffs()),
        "nonnegative_coefficients": all(c >= 0 for c in p.all_coeffs()),
        "negative_coefficients": all(c < 0 for c in p.all_coeffs()),
        "nonpositive_coefficients": all(c <= 0 for c in p.all_coeffs()),
        "real_root_intervals": [str(v) for v in sp.intervals(p.as_expr(), eps=sp.Rational(1, 10**20))],
    }


def bernstein_record(poly: sp.Expr, var: sp.Symbol, left: sp.Rational, right: sp.Rational) -> dict:
    p = sp.Poly(sp.expand(poly.subs(var, left + (right - left) * Y)), Y, domain=sp.QQ)
    degree = p.degree()
    power = [p.nth(j) for j in range(degree + 1)]
    coeffs = [
        sp.factor(sum(power[j] * sp.binomial(k, j) / sp.binomial(degree, j) for j in range(k + 1)))
        for k in range(degree + 1)
    ]
    reconstructed = sum(
        coeffs[k] * sp.binomial(degree, k) * Y**k * (1 - Y) ** (degree - k)
        for k in range(degree + 1)
    )
    assert sp.expand(reconstructed - p.as_expr()) == 0
    return {
        "interval": [str(left), str(right)],
        "coefficients": [str(c) for c in coeffs],
        "positive_coefficients": all(c > 0 for c in coeffs),
        "minimum_coefficient": str(min(coeffs)),
        "reconstruction_verified": True,
    }


def lie4(expr: sp.Expr) -> sp.Expr:
    vf = {
        H: -sp.Rational(1, 6) * H * (P + R * Z),
        Z: -R * (1 - Z**2),
        R: -sp.Rational(2, 3) * R * (P + R * Z),
        P: 3 - sp.Rational(1, 3) * P**2 + sp.Rational(1, 12) * R**2 * (3 + Z**2),
    }
    return sp.expand(sum(sp.diff(expr, v) * vf[v] for v in (H, Z, R, P)))


def modular_source_seam_data() -> dict:
    hjet = [H]
    for _ in range(10):
        hjet.append(lie4(hjet[-1]))
    fjet = [sp.expand((hjet[n + 2] - sp.Rational(1, 4) * hjet[n]) / 2) for n in range(9)]
    seam = {H: 1, Z: 0, P: 0, R**2: X}
    # Substitute R first through even-polynomial collection to avoid ambiguous sqrt choices.
    even_f = []
    for n in range(0, 9, 2):
        value = sp.expand(fjet[n].subs({H: 1, Z: 0, P: 0}))
        value_x = sp.Poly(value, R).as_dict()
        assert all(k[0] % 2 == 0 for k in value_x)
        even_f.append(sp.expand(sum(c * X ** (k[0] // 2) for k, c in value_x.items())))

    f0, f2, f4, f6, f8 = even_f
    m2, m4, m6, m8 = [sp.cancel(v / f0) for v in (f2, f4, f6, f8)]
    l2 = m2
    l4 = sp.cancel(m4 - 3 * m2**2)
    l6 = sp.cancel(m6 - 15 * m4 * m2 + 30 * m2**3)
    l8 = sp.cancel(m8 - 28 * m6 * m2 - 35 * m4**2 + 420 * m4 * m2**2 - 630 * m2**4)
    a, b, c, d = (-l2, -l4, -l6, -l8)
    old_k = sp.cancel(2 * b**2 - a * c)
    q_block = sp.cancel(a**2 * d - 5 * a * b * c + 4 * b**3)
    total = sp.cancel(a**2 * d - 18 * a**3 * c + 36 * a**2 * b**2 - 5 * a * b * c + 4 * b**3)
    assert sp.cancel(total - (18 * a**2 * old_k + q_block)) == 0

    total_num, total_den = map(sp.factor, sp.fraction(total))
    q_num, q_den = map(sp.factor, sp.fraction(q_block))
    old_num, old_den = map(sp.factor, sp.fraction(old_k))
    shift = sp.Rational(191, 10)
    return {
        "source_even_jets": {str(2 * i): rational_json(v) for i, v in enumerate(even_f)},
        "log_sign_coordinates": {
            "A_minus_L2": rational_json(a),
            "B_minus_L4": rational_json(b),
            "C_minus_L6": rational_json(c),
            "D_minus_L8": rational_json(d),
        },
        "reverse_minor": {
            "expression": rational_json(old_k),
            "numerator": poly_record(old_num, X),
            "denominator": rational_json(old_den),
            "shift_191_10": poly_record(sp.expand(old_num.subs(X, shift + Y)), Y),
        },
        "new_Q_block": {
            "expression": rational_json(q_block),
            "numerator": poly_record(q_num, X),
            "denominator": rational_json(q_den),
            "shift_191_10": poly_record(sp.expand(q_num.subs(X, shift + Y)), Y),
        },
        "c5_jacobian_first_seam_coefficient": {
            "expression": rational_json(total),
            "numerator": poly_record(total_num, X),
            "denominator": rational_json(total_den),
            "shift_191_10": poly_record(sp.expand(total_num.subs(X, shift + Y)), Y),
            "bernstein_191_10_to_20": bernstein_record(
                total_num, X, sp.Rational(191, 10), sp.Rational(20)
            ),
            "decomposition_verified": True,
        },
    }


def lie3(expr: sp.Expr) -> sp.Expr:
    gap = 16 * Q + 6 - 6 * B**2
    vf = {
        U: sp.Rational(9, 2) + 4 * Q + sp.Rational(3, 2) * B**2 + 2 * B * U,
        B: sp.Rational(1, 2) + 4 * Q - sp.Rational(1, 2) * B**2,
        Q: sp.Rational(3, 4) * B * (sp.Rational(1, 2) + 4 * Q - sp.Rational(1, 2) * B**2)
        - sp.Rational(1, 8) * gap * (U + B),
    }
    return sp.expand(sum(sp.diff(expr, v) * vf[v] for v in (U, B, Q)))


def source_positive_drift_data() -> dict:
    def cov_lie(expr: sp.Expr) -> sp.Expr:
        return sp.expand(lie3(expr) + sp.Rational(1, 2) * B * expr)

    f = [Q]
    for _ in range(8):
        f.append(cov_lie(f[-1]))
    p0 = f[0] ** 2
    p2 = 2 * (f[0] * f[2] - f[1] ** 2)
    p4 = 2 * f[0] * f[4] - 8 * f[1] * f[3] + 6 * f[2] ** 2
    p6 = 2 * f[0] * f[6] - 12 * f[1] * f[5] + 30 * f[2] * f[4] - 20 * f[3] ** 2
    p8 = 2 * f[0] * f[8] - 16 * f[1] * f[7] + 56 * f[2] * f[6] - 112 * f[3] * f[5] + 70 * f[4] ** 2
    d1 = sp.expand(p0 * p4 * p8 - p0 * p6**2 - p2**2 * p8 + 2 * p2 * p4 * p6 - p4**3)
    lq = lie3(Q)
    drift = sp.expand(Q * lie3(d1) - 6 * d1 * lq)
    seam_sub = {U: 0, B: 0, Q: (X - 6) / 16}
    drift_seam = sp.factor(drift.subs(seam_sub))
    assert drift_seam == 0
    seam_derivative = sp.factor(lie3(drift).subs(seam_sub))
    num, den = map(sp.factor, sp.fraction(seam_derivative))
    shift = sp.Rational(191, 10)
    seam_odd_derivatives = {}
    derivative = drift
    for order in range(1, 6):
        derivative = lie3(derivative)
        value = sp.factor(derivative.subs(seam_sub))
        if order % 2 == 0:
            assert value == 0
            continue
        value_num, value_den = map(sp.factor, sp.fraction(value))
        seam_odd_derivatives[str(order)] = {
            "expression": rational_json(value),
            "denominator": rational_json(value_den),
            "numerator_degree": sp.Poly(value_num, X).degree(),
            "shift_191_10": poly_record(sp.expand(value_num.subs(X, shift + Y)), Y),
            "bernstein_191_10_to_20": bernstein_record(
                value_num, X, sp.Rational(191, 10), sp.Rational(20)
            ),
        }
    return {
        "d1_total_degree": sp.Poly(d1, U, B, Q).total_degree(),
        "d1_term_count": len(sp.Poly(d1, U, B, Q).terms()),
        "drift_total_degree": sp.Poly(drift, U, B, Q).total_degree(),
        "drift_term_count": len(sp.Poly(drift, U, B, Q).terms()),
        "drift_on_seam": str(drift_seam),
        "physical_flow_derivative_at_seam": {
            "expression": rational_json(seam_derivative),
            "numerator": poly_record(num, X),
            "denominator": rational_json(den),
            "shift_191_10": poly_record(sp.expand(num.subs(X, shift + Y)), Y),
        },
        "physical_flow_odd_derivatives_at_seam": seam_odd_derivatives,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    args = parser.parse_args()
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "sympy": sp.__version__,
        "c5_fixed_action_seam": modular_source_seam_data(),
        "s6f_projective_drift_seam": source_positive_drift_data(),
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "c5_shift_positive": result["c5_fixed_action_seam"]["c5_jacobian_first_seam_coefficient"]["shift_191_10"]["positive_coefficients"],
        "c5_q_shift_positive": result["c5_fixed_action_seam"]["new_Q_block"]["shift_191_10"]["positive_coefficients"],
        "s6f_seam_shift_positive": result["s6f_projective_drift_seam"]["physical_flow_derivative_at_seam"]["shift_191_10"]["positive_coefficients"],
    }, indent=2))


if __name__ == "__main__":
    main()
