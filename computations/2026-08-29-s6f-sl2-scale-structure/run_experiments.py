#!/usr/bin/env python3
"""Exact structural attack on the S6F scale-velocity matrix.

Diagnostic only. No output from this script may be imported into a Lean proof.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
JACOBI_PATH = HERE.parent / "2026-08-29-s6f-jacobi-variation" / "run_experiments.py"
spec = importlib.util.spec_from_file_location("jacobi", JACOBI_PATH)
jacobi = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = jacobi
spec.loader.exec_module(jacobi)

core = jacobi.contact.core
U, B, Q = core.U, core.B, core.Q
S, T, ETA, W = core.S, core.T, jacobi.contact.ETA, jacobi.contact.W
COORDS = (U, B, Q)
UNIT_MATRIX: sp.Matrix | None = None


def vf_apply(vector: dict[sp.Symbol, sp.Expr], expr: sp.Expr) -> sp.Expr:
    return sp.expand(sum(vector[x] * sp.diff(expr, x) for x in COORDS))


def bracket(
    left: dict[sp.Symbol, sp.Expr], right: dict[sp.Symbol, sp.Expr]
) -> dict[sp.Symbol, sp.Expr]:
    return {
        x: sp.factor(vf_apply(left, right[x]) - vf_apply(right, left[x]))
        for x in COORDS
    }


def add_vectors(
    left: dict[sp.Symbol, sp.Expr], right: dict[sp.Symbol, sp.Expr]
) -> dict[sp.Symbol, sp.Expr]:
    return {x: sp.expand(left[x] + right[x]) for x in COORDS}


def scale_vector(c: sp.Expr, vector: dict[sp.Symbol, sp.Expr]) -> dict[sp.Symbol, sp.Expr]:
    return {x: sp.expand(c * vector[x]) for x in COORDS}


def source_vector_field() -> dict[sp.Symbol, sp.Expr]:
    gap = 16 * Q + 6 - 6 * B**2
    return {
        U: sp.Rational(9, 2) + 4 * Q + sp.Rational(3, 2) * B**2 + 2 * B * U,
        B: sp.Rational(1, 2) + 4 * Q - sp.Rational(1, 2) * B**2,
        Q: sp.Rational(3, 4) * B
        * (sp.Rational(1, 2) + 4 * Q - sp.Rational(1, 2) * B**2)
        - sp.Rational(1, 8) * gap * (U + B),
    }


def scale_cartan() -> dict[sp.Symbol, sp.Expr]:
    return {U: U / 2, B: B / 2, Q: Q + sp.Rational(3, 8)}


def lowering_opposite() -> dict[sp.Symbol, sp.Expr]:
    # This is -W in the paper notation; W=(-3,1,3B/4).
    return {U: 3, B: -1, Q: -3 * B / 4}


def vector_equal(
    left: dict[sp.Symbol, sp.Expr], right: dict[sp.Symbol, sp.Expr]
) -> bool:
    return all(sp.expand(left[x] - right[x]) == 0 for x in COORDS)


def source_scale_velocity() -> sp.Matrix:
    jets = jacobi.signed_reflected_jets()
    d = scale_cartan()
    moments = [vf_apply(d, jet) for jet in jets]
    return sp.Matrix(
        ((moments[0], moments[1], moments[2]),
         (moments[1], moments[2], moments[3]),
         (moments[2], moments[3], moments[4]))
    )


def normalized_scale_velocity() -> sp.Matrix:
    jets = [jacobi.normalized_component(jet) for jet in jacobi.signed_reflected_jets()]
    hankel = sp.Matrix(
        ((jets[0], jets[1], jets[2]),
         (jets[1], jets[2], jets[3]),
         (jets[2], jets[3], jets[4]))
    )
    return hankel.diff(core.X)


def bernstein_value(
    poly: sp.Poly, degree_t: int, degree_eta: int, kt: int, ke: int
) -> sp.Rational:
    value = sp.Rational(0)
    for a in range(kt + 1):
        for b in range(ke + 1):
            value += (
                poly.coeff_monomial(T**a * ETA**b)
                * sp.binomial(kt, a) / sp.binomial(degree_t, a)
                * sp.binomial(ke, b) / sp.binomial(degree_eta, b)
            )
    return sp.factor(value)


def matrix_bernstein_layer(scale_exponent: int) -> tuple[int, dict]:
    assert UNIT_MATRIX is not None
    coefficients = [
        [sp.Poly(UNIT_MATRIX[i, j], S).coeff_monomial(S**scale_exponent)
         for j in range(3)]
        for i in range(3)
    ]
    degree_t = max(sp.Poly(coefficients[i][j], T, ETA).degree(T)
                   for i in range(3) for j in range(3))
    degree_eta = max(sp.Poly(coefficients[i][j], T, ETA).degree(ETA)
                     for i in range(3) for j in range(3))
    polys = [[sp.Poly(coefficients[i][j], T, ETA, domain=sp.QQ)
              for j in range(3)] for i in range(3)]
    negative = [0, 0, 0]
    zero = [0, 0, 0]
    signatures: list[str] = []
    for kt in range(degree_t + 1):
        for ke in range(degree_eta + 1):
            matrix = sp.Matrix(3, 3, lambda i, j:
                bernstein_value(polys[i][j], degree_t, degree_eta, kt, ke))
            pivots = (
                matrix[0, 0],
                sp.factor(matrix.extract((0, 1), (0, 1)).det()),
                sp.factor(matrix.det()),
            )
            for index, pivot in enumerate(pivots):
                negative[index] += int(bool(pivot < 0))
                zero[index] += int(bool(pivot == 0))
            signatures.append(",".join("-" if p < 0 else "0" if p == 0 else "+"
                                       for p in pivots))
    return scale_exponent, {
        "degrees": [degree_t, degree_eta],
        "count": (degree_t + 1) * (degree_eta + 1),
        "negative_leading_pivots": negative,
        "zero_leading_pivots": zero,
        "signature_sha256": hashlib.sha256(
            "\n".join(signatures).encode("ascii")
        ).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(6, os.cpu_count() or 1))
    args = parser.parse_args()

    vector = source_vector_field()
    d = scale_cartan()
    f = lowering_opposite()
    w = scale_vector(-1, f)
    e = add_vectors(vector, w)
    h = scale_vector(4, d)
    sl2 = {
        "[h,e]=2e": vector_equal(bracket(h, e), scale_vector(2, e)),
        "[h,f]=-2f": vector_equal(bracket(h, f), scale_vector(-2, f)),
        "[e,f]=h": vector_equal(bracket(e, f), h),
    }

    r, b, k = sp.symbols("r b k")
    source_change = {U: r - 3 * b, B: b, Q: k + 3 * b**2 / 8 - sp.Rational(3, 8)}
    coordinate_actions = {
        "V_r": sp.factor(vf_apply(vector, U + 3 * B).subs(source_change)),
        "V_b": sp.factor(vf_apply(vector, B).subs(source_change)),
        "V_k": sp.factor(vf_apply(vector, Q + sp.Rational(3, 8) - 3 * B**2 / 8)
                         .subs(source_change)),
        "W_r": sp.factor(vf_apply(w, U + 3 * B).subs(source_change)),
        "W_b": sp.factor(vf_apply(w, B).subs(source_change)),
        "W_k": sp.factor(vf_apply(w, Q + sp.Rational(3, 8) - 3 * B**2 / 8)
                         .subs(source_change)),
    }

    source_matrix = source_scale_velocity()
    m0_factor = str(sp.factor(source_matrix[0, 0].subs(source_change)))
    normalized = normalized_scale_velocity()
    physical_sub = {
        U: core.R * core.Z * core.Y,
        B: core.R * core.Z * (1 - core.Y) / 3,
        Q: (core.R**2 * (1 - core.Z**2
            + sp.Rational(2, 3) * core.Z**2 * (1 - core.Y)**2) - 6) / 16,
    }
    # Exact chain-rule check before eliminating even powers of R.
    source_physical = source_matrix.applyfunc(lambda x: sp.expand(x.subs(physical_sub)))
    normalized_physical = normalized.subs({core.X: core.R**2, W: core.Z**2})
    chain_rule_identity = all(
        sp.expand(source_physical[i, j] - core.R**2 * normalized_physical[i, j]) == 0
        for i in range(3) for j in range(3)
    )

    refined = normalized.applyfunc(jacobi.refined_prism)
    global UNIT_MATRIX
    UNIT_MATRIX = refined.subs(W, jacobi.contact.WMAX * T).applyfunc(sp.expand)
    max_scale_degree = max(sp.Poly(UNIT_MATRIX[i, j], S).degree()
                           for i in range(3) for j in range(3))
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        layers = dict(pool.map(matrix_bernstein_layer, range(max_scale_degree + 1)))

    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers": args.workers,
        "source_scale_identity": "X*d/dX = (U/2)dU + (B/2)dB + (Q+3/8)dQ",
        "chain_rule_identity_exact": chain_rule_identity,
        "sl2_relations_exact": sl2,
        "source_coordinates": {
            "r": "U+3B",
            "b": "B",
            "k": "Q+3/8-3B^2/8 = gap/16",
            "actions": {name: str(value) for name, value in coordinate_actions.items()},
            "scale_velocity_m0_factor": m0_factor,
        },
        "coefficientwise_matrix_bernstein": {
            "question": "is H_X a nonnegative scalar combination of PSD Bernstein coefficient matrices?",
            "layers": {str(key): value for key, value in sorted(layers.items())},
            "survives": all(
                not any(record["negative_leading_pivots"])
                for record in layers.values()
            ),
        },
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
