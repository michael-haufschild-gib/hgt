#!/usr/bin/env python3
"""Exact hostile test of S6F drift on formal sharp clock cone.

Diagnostic only. No output is admissible in a Lean proof.

Tests whether narrowing the formal clock ratio from [2/5,1/2] to
[13/32,7/16] revives direct y-monotonicity or another short reduction.
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

YA = sp.Rational(13, 32)
YB = sp.Rational(7, 16)


def certificate() -> sp.Expr:
    drift = core.normalized_drift()
    triangle = sp.expand(drift.subs(core.V, core.Z * core.Y))
    quotient = sp.cancel(triangle / core.Z)
    assert sp.denom(quotient) == 1
    return sp.expand(quotient)


def signs(values: list[sp.Rational]) -> dict:
    return {
        "count": len(values),
        "negative": sum(bool(v < 0) for v in values),
        "zero": sum(bool(v == 0) for v in values),
        "positive": sum(bool(v > 0) for v in values),
        "minimum": str(min(values)),
        "maximum": str(max(values)),
    }


def half_ray_record(expr: sp.Expr) -> dict:
    """Power basis in S>=0, tensor Bernstein in (T,Y) on unit square."""
    poly = sp.Poly(sp.expand(expr), core.S, domain=sp.QQ.frac_field(core.T, core.Y))
    records = []
    for k in range(poly.degree() + 1):
        coeff = sp.cancel(poly.nth(k))
        assert sp.denom(coeff) == 1
        records.append(core.bernstein_tensor(sp.expand(coeff), (core.T, core.Y)))
    all_values = {
        "count": sum(record["count"] for record in records),
        "negative": sum(record["negative_count"] for record in records),
        "zero": sum(record["zero_count"] for record in records),
    }
    all_values["positive"] = all_values["count"] - all_values["negative"] - all_values["zero"]
    digest = hashlib.sha256(
        "\n".join(record["coefficient_sha256"] for record in records).encode("ascii")
    ).hexdigest()
    return {
        "S_degree": poly.degree(),
        "aggregate": all_values,
        "all_nonnegative": all(record["nonnegative"] for record in records),
        "all_positive": all(record["positive"] for record in records),
        "nested_sha256": digest,
    }


def record_job(task: tuple[str, sp.Expr]) -> tuple[str, dict]:
    name, expr = task
    return name, half_ray_record(expr)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("sharp-cone-results.json"))
    parser.add_argument("--workers", type=int, default=min(7, os.cpu_count() or 1))
    args = parser.parse_args()

    print("reconstructing normalized drift", file=sys.stderr, flush=True)
    base = certificate()
    sharp = sp.expand(base.subs({
        core.X: sp.Rational(191, 10) + core.S,
        core.Z: sp.Rational(3, 10) * core.T,
        core.Y: YA + (YB - YA) * core.Y,
    }))
    tasks = [
        ("C", sharp),
        ("dC_dX", sp.diff(sharp, core.S)),
        ("minus_dC_dz", -sp.diff(sharp, core.T)),
        ("dC_dy", sp.diff(sharp, core.Y)),
        ("minus_dC_dy", -sp.diff(sharp, core.Y)),
        ("minus_d2C_dy2", -sp.diff(sharp, core.Y, 2)),
        ("lower_y_wall", sharp.subs(core.Y, 0)),
        ("upper_y_wall", sharp.subs(core.Y, 1)),
    ]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = dict(pool.map(record_job, tasks))
    corners = {
        f"T{t}_Y{y}": str(sp.factor(sharp.subs({core.S: 0, core.T: t, core.Y: y})))
        for t in (0, 1) for y in (0, 1)
    }
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers": args.workers,
        "sharp_cone": "X=191/10+S, z=(3/10)T, y=13/32+(1/32)Y",
        "records": records,
        "corners": corners,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
