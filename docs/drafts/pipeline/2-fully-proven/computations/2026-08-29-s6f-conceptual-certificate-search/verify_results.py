#!/usr/bin/env python3
"""Independent exact verifier for S6F conceptual-certificate search.

Diagnostic only. Nothing verified here is admissible in a Lean proof.
"""

from __future__ import annotations

import concurrent.futures
import importlib.util
import itertools
import json
import os
import sys
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
CORE_PATH = HERE.parent / "2026-08-29-s6f-normalized-chamber-search" / "run_experiments.py"
spec = importlib.util.spec_from_file_location("s6f_core_verify", CORE_PATH)
core = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = core
spec.loader.exec_module(core)


def certificate() -> sp.Expr:
    drift = core.normalized_drift()
    triangle = sp.Poly(sp.expand(drift.subs(core.V, core.Z * core.Y)), core.Z)
    assert triangle.nth(0) == 0
    quotient, remainder = sp.div(triangle, sp.Poly(core.Z, core.Z))
    assert remainder.is_zero
    return sp.expand(quotient.as_expr())


def independent_bernstein(expr: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[sp.Rational]:
    """Direct multi-index power-to-Bernstein formula, independent of run scripts."""
    poly = sp.Poly(sp.expand(expr), *variables, domain=sp.QQ)
    degrees = tuple(poly.degree(variable) for variable in variables)
    power = {powers: value for powers, value in poly.terms()}
    values = []
    for target in itertools.product(*(range(degree + 1) for degree in degrees)):
        total = sp.Rational(0)
        for source in itertools.product(*(range(index + 1) for index in target)):
            value = power.get(source, sp.Rational(0))
            if value == 0:
                continue
            weight = sp.Rational(1)
            for axis in range(len(variables)):
                weight *= (
                    sp.binomial(target[axis], source[axis])
                    / sp.binomial(degrees[axis], source[axis])
                )
            total += value * weight
        values.append(total)
    return values


def hybrid_signs(expr: sp.Expr) -> dict:
    poly = sp.Poly(sp.expand(expr), core.S, domain=sp.QQ.frac_field(core.T, core.Y))
    values = []
    for k in range(poly.degree() + 1):
        coefficient = sp.cancel(poly.nth(k))
        assert sp.denom(coefficient) == 1
        values.extend(independent_bernstein(sp.expand(coefficient), (core.T, core.Y)))
    return {
        "count": len(values),
        "negative": sum(bool(value < 0) for value in values),
        "zero": sum(bool(value == 0) for value in values),
        "positive": sum(bool(value > 0) for value in values),
    }


def verify_job(task: tuple[str, sp.Expr]) -> tuple[str, dict]:
    name, expr = task
    return name, hybrid_signs(expr)


def main() -> None:
    sharp_results = json.loads((HERE / "sharp-cone-results.json").read_text())
    intrinsic_results = json.loads((HERE / "intrinsic-attack-results.json").read_text())

    c = certificate()
    sharp = sp.expand(c.subs({
        core.X: sp.Rational(191, 10) + core.S,
        core.Z: sp.Rational(3, 10) * core.T,
        core.Y: sp.Rational(13, 32) + sp.Rational(1, 32) * core.Y,
    }))
    tasks = [
        ("C", sharp),
        ("dC_dX", sp.diff(sharp, core.S)),
        ("minus_dC_dz", -sp.diff(sharp, core.T)),
        ("dC_dy", sp.diff(sharp, core.Y)),
        ("minus_d2C_dy2", -sp.diff(sharp, core.Y, 2)),
    ]
    workers = min(5, os.cpu_count() or 1)
    with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
        verified = dict(pool.map(verify_job, tasks))
    for name, signs in verified.items():
        assert signs == sharp_results["records"][name]["aggregate"]

    source_drift = core.source_positive_drift()
    witness = sp.factor(source_drift.subs({
        core.B: 1,
        core.Q: 1,
        core.U: sp.Rational(5, 2),
    }))
    assert witness == -2321249416704
    assert witness < 0
    recorded = next(
        item for item in intrinsic_results["simple_exact_candidates"]
        if item["B"] == 1 and item["Q"] == 1 and item["U"] == "5/2"
    )
    assert recorded["reduced_drift"] == str(witness)
    assert recorded["negative"] is True

    print("verified: sharp-cone monotonicity/concavity signs and intrinsic wedge counterexample")


if __name__ == "__main__":
    main()
