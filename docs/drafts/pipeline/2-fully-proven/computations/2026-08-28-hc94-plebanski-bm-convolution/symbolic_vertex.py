#!/usr/bin/env python3
"""Exact SymPy classification of profile-independent Plebanski-kernel annihilation.

Computational route-selection evidence only. Not imported or cited as a Lean proof.
"""

import json
from pathlib import Path

import sympy as sp


def main() -> None:
    t, h, r, curvature = sp.symbols("t h r curvature")
    k = r * h
    p2 = (h + k) ** 2
    p1 = -2 * h * (h + k) - curvature * (h - k) * (h + k)
    p0 = h**2 + curvature * (h - k) * h
    kernel = sp.expand(p2 * t**2 + p1 * t + p0)
    normalized = sp.factor(kernel / h**2)
    opposite = sp.factor(normalized.subs(r, -1))
    same = sp.factor(normalized.subs(r, 1))
    coefficient_system = [
        sp.factor(sp.expand(normalized).coeff(t, degree)) for degree in (2, 1, 0)
    ]
    universal_solutions = sp.solve(coefficient_system, (r, curvature), dict=True)
    result = {
        "purpose": "route-selection evidence only; forbidden in Lean proofs",
        "normalized_kernel": str(normalized),
        "coefficients_t2_t1_t0": [str(x) for x in coefficient_system],
        "opposite_charge_kernel": str(opposite),
        "same_charge_kernel": str(same),
        "universal_profile_independent_annihilators": [
            {str(key): str(value) for key, value in solution.items()}
            for solution in universal_solutions
        ],
        "verification_opposite_at_minus_half": str(
            sp.simplify(normalized.subs({r: -1, curvature: -sp.Rational(1, 2)}))
        ),
    }
    Path("symbolic-vertex.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
