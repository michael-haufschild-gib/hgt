#!/usr/bin/env python3
"""Hostile exact test of the S6F thin-clock-cone conjecture.

Diagnostic only. No output from this script is admissible in a Lean proof.

The independent ODE idea predicts the actual modular orbit lies in

    191/10 < X < 20,  0 < z < 3/10,  2/5 < y=v/z < 1/2.

This run asks an unknown question: whether restricting y to that cone changes
the large Bernstein certificate into coordinate monotonicity or a short
boundary/corner certificate.
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
CORE_PATH = HERE.parent / "2026-08-29-s6f-normalized-chamber-search" / "run_experiments.py"
spec = importlib.util.spec_from_file_location("s6f_core", CORE_PATH)
core = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = core
spec.loader.exec_module(core)


def certificate() -> sp.Expr:
    drift = core.normalized_drift()
    triangle = sp.expand(drift.subs(core.V, core.Z * core.Y))
    return sp.expand(sp.cancel(triangle / core.Z))


def signs(values: list[sp.Rational]) -> dict:
    return {
        "count": len(values),
        "negative_count": sum(bool(v < 0) for v in values),
        "zero_count": sum(bool(v == 0) for v in values),
        "positive_count": sum(bool(v > 0) for v in values),
        "minimum": str(min(values)),
        "maximum": str(max(values)),
    }


def polynomial_record(expr: sp.Expr, variables: tuple[sp.Symbol, ...]) -> dict:
    poly = sp.Poly(sp.expand(expr), *variables, domain=sp.QQ)
    power = [value for _, value in poly.terms()]
    return {
        "degrees": [poly.degree(v) for v in variables],
        "terms": len(power),
        "power": signs(power),
        "bernstein": core.bernstein_tensor(expr, variables),
    }


def record_job(task: tuple[str, sp.Expr, tuple[sp.Symbol, ...]]) -> tuple[str, dict]:
    name, expr, variables = task
    return name, polynomial_record(expr, variables)


def half_ray_record(expr: sp.Expr) -> dict:
    """Power basis in S>=0, tensor Bernstein in (T,Y) in the unit square."""
    poly = sp.Poly(sp.expand(expr), core.S, domain=sp.QQ.frac_field(core.T, core.Y))
    records = []
    for k in range(poly.degree() + 1):
        coeff = sp.cancel(poly.nth(k))
        assert sp.denom(coeff) == 1
        records.append(core.bernstein_tensor(sp.expand(coeff), (core.T, core.Y)))
    all_nonnegative = all(r["nonnegative"] for r in records)
    all_positive = all(r["positive"] for r in records)
    digest = hashlib.sha256(
        "\n".join(r["coefficient_sha256"] for r in records).encode("ascii")
    ).hexdigest()
    return {
        "S_degree": poly.degree(),
        "coefficient_records": records,
        "all_coefficients_nonnegative_on_TY_cube": all_nonnegative,
        "all_coefficients_positive_on_TY_cube": all_positive,
        "nested_hash": digest,
    }


def half_ray_job(task: tuple[str, sp.Expr]) -> tuple[str, dict]:
    name, expr = task
    return name, half_ray_record(expr)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(6, os.cpu_count() or 1))
    args = parser.parse_args()

    base = certificate()
    cube = sp.expand(base.subs({
        core.X: sp.Rational(191, 10) + sp.Rational(9, 10) * core.S,
        core.Z: sp.Rational(3, 10) * core.T,
        core.Y: sp.Rational(2, 5) + sp.Rational(1, 10) * core.Y,
    }))
    boundary = sp.expand(cube.subs({core.S: 0, core.T: 1}))
    tasks = [
        ("C", cube, (core.S, core.T, core.Y)),
        ("dC_dS", sp.diff(cube, core.S), (core.S, core.T, core.Y)),
        ("dC_dT", sp.diff(cube, core.T), (core.S, core.T, core.Y)),
        ("dC_dY", sp.diff(cube, core.Y), (core.S, core.T, core.Y)),
        ("minus_dC_dY", -sp.diff(cube, core.Y), (core.S, core.T, core.Y)),
        ("minus_d2C_dY2", -sp.diff(cube, core.Y, 2), (core.S, core.T, core.Y)),
        ("boundary_P", boundary, (core.Y,)),
        ("boundary_dP", sp.diff(boundary, core.Y), (core.Y,)),
        ("boundary_minus_dP", -sp.diff(boundary, core.Y), (core.Y,)),
        ("boundary_minus_d2P", -sp.diff(boundary, core.Y, 2), (core.Y,)),
    ]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = dict(pool.map(record_job, tasks))

    corners = {}
    for s in (0, 1):
        for t in (0, 1):
            for y in (0, 1):
                corners[f"S{s}_T{t}_Y{y}"] = str(sp.factor(cube.subs({
                    core.S: s, core.T: t, core.Y: y,
                })))

    # Exact inward-pointing barrier numerators after clearing positive R.
    X, z = core.X, core.Z
    lower_wall = sp.factor(
        3 + X * (1 - z**2) * (sp.Rational(1, 4) - sp.Rational(2, 5))
        + X * z**2 * (1 - sp.Rational(2, 5))**2 / 3
    )
    upper_wall = sp.factor(
        3 + X * (1 - z**2) * (sp.Rational(1, 4) - sp.Rational(1, 2))
        + X * z**2 * (1 - sp.Rational(1, 2))**2 / 3
    )
    barrier_cube = {
        "lower": polynomial_record(sp.expand(lower_wall.subs({
            X: sp.Rational(191, 10) + sp.Rational(9, 10) * core.S,
            z: sp.Rational(3, 10) * core.T,
        })), (core.S, core.T)),
        "upper_negative": polynomial_record(sp.expand((-upper_wall).subs({
            X: sp.Rational(191, 10) + sp.Rational(9, 10) * core.S,
            z: sp.Rational(3, 10) * core.T,
        })), (core.S, core.T)),
    }

    half_cube = sp.expand(base.subs({
        core.X: sp.Rational(191, 10) + core.S,
        core.Z: sp.Rational(3, 10) * core.T,
        core.Y: sp.Rational(2, 5) + sp.Rational(1, 10) * core.Y,
    }))
    half_tasks = [
        ("C", half_cube),
        ("dC_dS", sp.diff(half_cube, core.S)),
        ("minus_dC_dT", -sp.diff(half_cube, core.T)),
        ("minus_d2C_dY2", -sp.diff(half_cube, core.Y, 2)),
        ("lower_y_wall", half_cube.subs(core.Y, 0)),
        ("upper_y_wall", half_cube.subs(core.Y, 1)),
    ]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        half_ray = dict(pool.map(half_ray_job, half_tasks))

    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers": args.workers,
        "thin_cone": "X=191/10+(9/10)S, z=(3/10)T, y=2/5+(1/10)Y",
        "records": records,
        "corners": corners,
        "barrier_numerators": {
            "lower_formula": str(lower_wall),
            "upper_formula": str(upper_wall),
            "cube_records": barrier_cube,
        },
        "half_ray_X_ge_191_over_10": half_ray,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
