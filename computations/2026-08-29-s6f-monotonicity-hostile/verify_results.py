#!/usr/bin/env python3
"""Independent exact verifier for S6F monotonicity-reduction diagnostic."""

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
                value += (
                    table[tuple(source)]
                    * sp.binomial(k, i)
                    / sp.binomial(degree, i)
                )
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
        "minimum": str(minimum),
        "minimum_index": list(minimum_index),
        "maximum": str(max(flat)),
        "coefficient_sha256": hashlib.sha256(
            "\n".join(str(value) for value in flat).encode("ascii")
        ).hexdigest(),
    }


def compare(actual: dict, recorded: dict) -> None:
    for key in (
        "degrees",
        "count",
        "negative_count",
        "zero_count",
        "minimum",
        "minimum_index",
        "maximum",
        "coefficient_sha256",
    ):
        assert actual[key] == recorded[key]


def main() -> None:
    payload = json.loads((HERE / "results.json").read_text())
    assert payload["scope"] == "diagnostic only; forbidden as Lean input"
    base = experiment.certificate()
    cube = sp.expand(
        base.subs(
            {
                core.X: sp.Rational(191, 10) + sp.Rational(9, 10) * core.S,
                core.Z: sp.Rational(3, 10) * core.T,
            }
        )
    )

    d_s = independent_bernstein(sp.diff(cube, core.S), (core.S, core.T, core.Y))
    d_t = independent_bernstein(-sp.diff(cube, core.T), (core.S, core.T, core.Y))
    d_y = independent_bernstein(-sp.diff(cube, core.Y), (core.S, core.T, core.Y))
    compare(d_s, payload["derivatives"]["d_dS"]["bernstein"])
    compare(d_t, payload["derivatives"]["minus_d_dT"]["bernstein"])
    compare(d_y, payload["derivatives"]["minus_d_dY"]["bernstein"])
    assert d_s["negative_count"] == d_s["zero_count"] == 0
    assert d_t["negative_count"] == 0
    assert d_y["negative_count"] > 0

    boundary = sp.expand(cube.subs({core.S: 0, core.T: 1}))
    boundary_certificate = independent_bernstein(boundary, (core.Y,))
    compare(boundary_certificate, payload["boundary_y"]["bernstein"])
    assert boundary_certificate["count"] == 28
    assert boundary_certificate["negative_count"] == 0
    assert boundary_certificate["zero_count"] == 0
    assert sp.factor(boundary.subs(core.Y, 1)) == sp.Rational(payload["corner_value"])
    print(
        "verified: exact X-increase, z-decrease, failure of y-monotonicity, "
        "and 28-term positive univariate boundary certificate"
    )


if __name__ == "__main__":
    main()
