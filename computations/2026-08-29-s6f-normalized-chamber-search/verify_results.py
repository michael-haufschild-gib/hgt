#!/usr/bin/env python3
"""Independent exact verifier for the S6F normalized-chamber diagnostic."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
from pathlib import Path

import numpy as np
import sympy as sp


ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("experiment", ROOT / "run_experiments.py")
experiment = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = experiment
spec.loader.exec_module(experiment)


def independent_bernstein(poly: sp.Expr) -> dict:
    """Power-to-Bernstein conversion, written independently as axiswise dictionaries."""
    variables = (experiment.S, experiment.T, experiment.Y)
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
        "degrees": degrees,
        "count": len(flat),
        "negative_count": sum(bool(value < 0) for value in flat),
        "zero_count": sum(bool(value == 0) for value in flat),
        "minimum": str(minimum),
        "minimum_index": minimum_index,
        "maximum": str(max(flat)),
        "coefficient_sha256": hashlib.sha256(
            "\n".join(str(value) for value in flat).encode("ascii")
        ).hexdigest(),
    }


def verify_scale_elimination(drift: sp.Expr) -> None:
    """Compare normalized expression with literal source drift at exact rational states."""
    r = sp.Rational(22, 5)
    x = r**2
    z = sp.Rational(1, 5)
    y = sp.Rational(2, 3)
    v = z * y
    u = r * v
    b = r * (z - v) / 3
    q = (x * (1 - z**2 + sp.Rational(2, 3) * (z - v) ** 2) - 6) / 16
    literal = experiment.source_positive_drift().subs(
        {experiment.U: u, experiment.B: b, experiment.Q: q}
    )
    normalized = drift.subs(
        {experiment.X: x, experiment.V: v, experiment.Z: z}
    )
    assert sp.cancel(literal / r - normalized) == 0


def main() -> None:
    payload = json.loads((ROOT / "results.json").read_text())
    assert payload["scope"] == "diagnostic only; forbidden as Lean input"

    drift = experiment.normalized_drift()
    verify_scale_elimination(drift)
    triangle = sp.expand(drift.subs(experiment.V, experiment.Z * experiment.Y))
    assert sp.Poly(triangle, experiment.Z).nth(0) == 0
    base = sp.expand(sp.cancel(triangle / experiment.Z))
    assert sp.denom(base) == 1
    assert len(sp.Poly(base, experiment.X, experiment.Z, experiment.Y).terms()) == 1120

    cube = sp.expand(
        base.subs(
            {
                experiment.X: sp.Rational(191, 10) + sp.Rational(9, 10) * experiment.S,
                experiment.Z: sp.Rational(3, 10) * experiment.T,
            }
        )
    )
    verified = independent_bernstein(cube)
    recorded = next(row["bernstein"] for row in payload["caps"] if row["z_cap"] == "3/10")
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
        assert list(verified[key]) == recorded[key] if key in ("degrees", "minimum_index") else verified[key] == recorded[key]
    assert verified["negative_count"] == 0
    assert verified["zero_count"] == 0

    # An exact rational hostile point confirms that positivity on the full simplex is false.
    hostile = {
        experiment.X: sp.Rational(199989, 10000),
        experiment.Z: sp.Rational(465, 1000),
        experiment.Y: sp.Rational(999, 1000),
    }
    v = hostile[experiment.Z] * hostile[experiment.Y]
    qfactor = hostile[experiment.X] * (
        1 - hostile[experiment.Z] ** 2
        + sp.Rational(2, 3) * (hostile[experiment.Z] - v) ** 2
    ) - 6
    assert qfactor > 0
    assert base.subs(hostile) < 0

    endpoint = payload["actual_endpoint_ode"]
    assert sp.Rational(endpoint["endpoint_z"]) < sp.Rational(3, 10)
    print(
        "verified: exact scale elimination, z factor, independent tensor-Bernstein "
        "positivity at z <= 3/10, and an exact full-simplex counterexample"
    )


if __name__ == "__main__":
    main()
