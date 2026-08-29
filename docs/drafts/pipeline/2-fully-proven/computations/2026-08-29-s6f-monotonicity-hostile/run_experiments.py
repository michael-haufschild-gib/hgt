#!/usr/bin/env python3
"""Try to collapse S6F chamber certificate to coordinate monotonicity.

Diagnostic only; no result is admissible as input to a Lean proof.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
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


def sign_job(task: tuple[str, sp.Expr]) -> tuple[str, dict]:
    name, expr = task
    return name, {
        "terms": len(sp.Poly(expr, core.S, core.T, core.Y).terms()),
        "bernstein": core.bernstein_tensor(expr, (core.S, core.T, core.Y)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=3)
    args = parser.parse_args()

    base = certificate()
    cube = sp.expand(
        base.subs(
            {
                core.X: sp.Rational(191, 10) + sp.Rational(9, 10) * core.S,
                core.Z: sp.Rational(3, 10) * core.T,
            }
        )
    )
    tasks = [
        ("d_dS", sp.diff(cube, core.S)),
        ("minus_d_dT", -sp.diff(cube, core.T)),
        ("minus_d_dY", -sp.diff(cube, core.Y)),
    ]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        derivatives = dict(pool.map(sign_job, tasks))

    corner = sp.factor(cube.subs({core.S: 0, core.T: 1, core.Y: 1}))
    boundary = sp.expand(cube.subs({core.S: 0, core.T: 1}))
    boundary_bernstein = core.bernstein_tensor(boundary, (core.Y,))
    W = sp.Symbol("W")
    boundary_at_one = sp.Poly(sp.expand(boundary.subs(core.Y, 1 - W)), W, domain=sp.QQ)
    boundary_at_one_coefficients = boundary_at_one.all_coeffs()
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers": args.workers,
        "tested_corner": "S=0,T=1,Y=1, i.e. X=191/10,z=3/10,y=1",
        "corner_value": str(corner),
        "corner_positive": bool(corner > 0),
        "boundary_y": {
            "degree": boundary_at_one.degree(),
            "terms": len(sp.Poly(boundary, core.Y).terms()),
            "bernstein": boundary_bernstein,
            "one_minus_y_power_negative_count": sum(
                bool(value < 0) for value in boundary_at_one_coefficients
            ),
            "one_minus_y_power_zero_count": sum(
                bool(value == 0) for value in boundary_at_one_coefficients
            ),
            "one_minus_y_power_coefficients": [
                str(value) for value in reversed(boundary_at_one_coefficients)
            ],
        },
        "derivatives": derivatives,
        "interpretation": (
            "All three Bernstein certificates would prove corner-minimum reduction; "
            "any failure kills that direct reduction only."
        ),
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
