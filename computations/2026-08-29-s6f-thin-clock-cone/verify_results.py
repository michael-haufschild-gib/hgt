#!/usr/bin/env python3
"""Independent exact verifier for S6F thin-clock-cone diagnostics."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
from pathlib import Path

import numpy as np
import sympy as sp


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("experiment", HERE / "run_experiments.py")
experiment = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = experiment
spec.loader.exec_module(experiment)
core = experiment.core


def independent_bernstein(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> dict:
    power = sp.Poly(sp.expand(poly), *variables, domain=sp.QQ)
    degrees = tuple(power.degree(var) for var in variables)
    shape = tuple(degree + 1 for degree in degrees)
    table = {index: sp.Rational(0) for index in np.ndindex(*shape)}
    for powers, value in power.terms():
        table[powers] = value
    for axis, degree in enumerate(degrees):
        converted = {}
        for index in np.ndindex(*shape):
            k = index[axis]
            value = sp.Rational(0)
            for i in range(k + 1):
                source = list(index)
                source[axis] = i
                value += table[tuple(source)] * sp.binomial(k, i) / sp.binomial(degree, i)
            converted[index] = sp.factor(value)
        table = converted
    flat = [table[index] for index in np.ndindex(*shape)]
    minimum = min(flat)
    minimum_index = next(index for index in np.ndindex(*shape) if table[index] == minimum)
    return {
        "degrees": list(degrees),
        "count": len(flat),
        "negative_count": sum(bool(value < 0) for value in flat),
        "zero_count": sum(bool(value == 0) for value in flat),
        "positive": all(bool(value > 0) for value in flat),
        "nonnegative": all(bool(value >= 0) for value in flat),
        "minimum": str(minimum),
        "minimum_index": list(minimum_index),
        "maximum": str(max(flat)),
        "coefficient_sha256": hashlib.sha256(
            "\n".join(str(value) for value in flat).encode("ascii")
        ).hexdigest(),
    }


def compare(actual: dict, recorded: dict) -> None:
    for key in (
        "degrees", "count", "negative_count", "zero_count", "positive", "nonnegative",
        "minimum", "minimum_index", "maximum", "coefficient_sha256",
    ):
        assert actual[key] == recorded[key], (key, actual[key], recorded[key])


def independent_half_ray(expr: sp.Expr) -> dict:
    poly = sp.Poly(sp.expand(expr), core.S, domain=sp.QQ.frac_field(core.T, core.Y))
    records = []
    for k in range(poly.degree() + 1):
        coeff = sp.cancel(poly.nth(k))
        assert sp.denom(coeff) == 1
        records.append(independent_bernstein(sp.expand(coeff), (core.T, core.Y)))
    return {
        "S_degree": poly.degree(),
        "coefficient_records": records,
        "all_coefficients_nonnegative_on_TY_cube": all(r["nonnegative"] for r in records),
        "all_coefficients_positive_on_TY_cube": all(r["positive"] for r in records),
        "nested_hash": hashlib.sha256(
            "\n".join(r["coefficient_sha256"] for r in records).encode("ascii")
        ).hexdigest(),
    }


def compare_half(actual: dict, recorded: dict) -> None:
    assert actual["S_degree"] == recorded["S_degree"]
    assert actual["all_coefficients_nonnegative_on_TY_cube"] == recorded[
        "all_coefficients_nonnegative_on_TY_cube"
    ]
    assert actual["all_coefficients_positive_on_TY_cube"] == recorded[
        "all_coefficients_positive_on_TY_cube"
    ]
    assert actual["nested_hash"] == recorded["nested_hash"]
    assert len(actual["coefficient_records"]) == len(recorded["coefficient_records"])
    for a, b in zip(actual["coefficient_records"], recorded["coefficient_records"], strict=True):
        compare(a, b)


def main() -> None:
    payload = json.loads((HERE / "results.json").read_text())
    assert payload["scope"] == "diagnostic only; forbidden as Lean input"
    base = experiment.certificate()
    cube = sp.expand(base.subs({
        core.X: sp.Rational(191, 10) + sp.Rational(9, 10) * core.S,
        core.Z: sp.Rational(3, 10) * core.T,
        core.Y: sp.Rational(2, 5) + sp.Rational(1, 10) * core.Y,
    }))
    compare(
        independent_bernstein(-sp.diff(cube, core.Y, 2), (core.S, core.T, core.Y)),
        payload["records"]["minus_d2C_dY2"]["bernstein"],
    )

    half = sp.expand(base.subs({
        core.X: sp.Rational(191, 10) + core.S,
        core.Z: sp.Rational(3, 10) * core.T,
        core.Y: sp.Rational(2, 5) + sp.Rational(1, 10) * core.Y,
    }))
    expressions = {
        "C": half,
        "dC_dS": sp.diff(half, core.S),
        "minus_dC_dT": -sp.diff(half, core.T),
        "minus_d2C_dY2": -sp.diff(half, core.Y, 2),
        "lower_y_wall": half.subs(core.Y, 0),
        "upper_y_wall": half.subs(core.Y, 1),
    }
    for name, expr in expressions.items():
        compare_half(independent_half_ray(expr), payload["half_ray_X_ge_191_over_10"][name])
    assert payload["half_ray_X_ge_191_over_10"]["C"][
        "all_coefficients_positive_on_TY_cube"
    ]
    assert payload["half_ray_X_ge_191_over_10"]["minus_d2C_dY2"][
        "all_coefficients_nonnegative_on_TY_cube"
    ]
    print("verified: exact thin-cone concavity and half-ray positivity for X >= 191/10")


if __name__ == "__main__":
    main()
