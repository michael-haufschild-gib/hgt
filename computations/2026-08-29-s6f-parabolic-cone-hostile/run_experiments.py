#!/usr/bin/env python3
"""Hostile exact test of the S6F parabolic clock cone.

Diagnostic only. No output is admissible in a Lean proof.

The formal ODE comparison gives

    X >= 191/10 + (147/20) z^2,
    y >= 13/32 + z^2/32,
    y <= 33/80 + z^2/12,
    0 <= z^2 <= 9/100.

This script tests the unknown claim that the forced X/y gains overpower the
adverse z direction, so normalized drift is increasing in w=z^2 along the
parabolic lower wall. It also searches nearby exact scale shears to locate the
first coefficient-positive monotonicity threshold.
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

W = sp.Symbol("w")
X0 = sp.Rational(191, 10)
YA = sp.Rational(13, 32)
WMAX = sp.Rational(9, 100)
KFORMAL = sp.Rational(147, 20)
BASE: sp.Expr | None = None


def normalized_certificate() -> sp.Expr:
    drift = core.normalized_drift()
    triangle = sp.expand(drift.subs(core.V, core.Z * core.Y))
    quotient = sp.cancel(triangle / core.Z)
    assert sp.denom(quotient) == 1
    return sp.expand(quotient)


def even_z_to_w(expr: sp.Expr) -> sp.Expr:
    poly = sp.Poly(expr, core.X, core.Z, core.Y, domain=sp.QQ)
    out = sp.Rational(0)
    odd = []
    for (ex, ez, ey), coeff in poly.terms():
        if ez % 2:
            odd.append((ex, ez, ey))
        out += coeff * core.X**ex * W ** (ez // 2) * core.Y**ey
    assert not odd, f"unexpected odd z powers: {odd[:8]}"
    return sp.expand(out)


def signs(values: list[sp.Rational]) -> dict:
    return {
        "count": len(values),
        "negative": sum(bool(v < 0) for v in values),
        "zero": sum(bool(v == 0) for v in values),
        "positive": sum(bool(v > 0) for v in values),
        "minimum": str(min(values)),
        "maximum": str(max(values)),
    }


def univariate_bernstein(expr: sp.Expr, variable: sp.Symbol) -> list[sp.Rational]:
    poly = sp.Poly(expr, variable, domain=sp.QQ)
    degree = poly.degree()
    power = [poly.nth(i) for i in range(degree + 1)]
    return [
        sum(power[i] * sp.binomial(k, i) / sp.binomial(degree, i) for i in range(k + 1))
        for k in range(degree + 1)
    ]


def half_strip_record(expr: sp.Expr, bounded: sp.Symbol) -> dict:
    """Power basis on S>=0, Bernstein basis on bounded variable in [0,1]."""
    poly = sp.Poly(sp.expand(expr), core.S, bounded, domain=sp.QQ)
    ordinary = poly.coeffs()
    by_s: dict[int, sp.Expr] = {}
    for (es, eb), coeff in poly.terms():
        by_s[es] = by_s.get(es, sp.Rational(0)) + coeff * bounded**eb
    bernstein = []
    for es in sorted(by_s):
        bernstein.extend(univariate_bernstein(by_s[es], bounded))
    digest = hashlib.sha256(
        "\n".join(str(v) for v in bernstein).encode("ascii")
    ).hexdigest()
    return {
        "degrees": [poly.degree(core.S), poly.degree(bounded)],
        "terms": len(poly.terms()),
        "ordinary": signs(ordinary),
        "bernstein": signs(bernstein),
        "bernstein_sha256": digest,
    }


def lower_wall(k: sp.Rational) -> sp.Expr:
    assert BASE is not None
    return sp.expand(BASE.subs({
        core.X: X0 + k * W + core.S,
        core.Y: YA + W / 32,
    }))


def record_job(task: tuple[str, str, sp.Rational]) -> tuple[str, dict]:
    """Build and certify one shear wholly inside a worker process."""
    name, kind, k = task
    wall = lower_wall(k)
    if kind == "C":
        expr = wall
    elif kind == "dW":
        expr = sp.diff(wall, W)
    elif kind == "dS":
        expr = sp.diff(wall, core.S)
    elif kind == "d2W":
        expr = sp.diff(wall, W, 2)
    elif kind.startswith("alt_"):
        order = int(kind.split("_", 1)[1])
        expr = (-1) ** order * sp.diff(wall, W, order)
    elif kind == "outerSlack":
        expr = wall.subs(W, WMAX * (1 - core.T))
        return name, half_strip_record(sp.expand(expr), core.T)
    else:
        raise ValueError(kind)
    unit = sp.expand(expr.subs(W, WMAX * core.T))
    return name, half_strip_record(unit, core.T)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(12, os.cpu_count() or 1))
    args = parser.parse_args()

    print("reconstructing normalized drift", file=sys.stderr, flush=True)
    global BASE
    BASE = even_z_to_w(normalized_certificate())
    print("dispatching independent parabolic shears", file=sys.stderr, flush=True)

    tasks: list[tuple[str, str, sp.Rational]] = [
        ("formal_lower_C", "C", KFORMAL),
        ("formal_lower_dW", "dW", KFORMAL),
        ("formal_lower_dS", "dS", KFORMAL),
        ("formal_lower_d2W", "d2W", KFORMAL),
    ]
    for k in [sp.Rational(0), sp.Rational(5), sp.Rational(6), sp.Rational(7),
              KFORMAL, sp.Rational(15, 2), sp.Rational(8), sp.Rational(10)]:
        tasks.append((f"dW_k_{str(k).replace('/', '_')}", "dW", k))
    tasks.append(("formal_outer_slack_C", "outerSlack", KFORMAL))
    for order in range(14):
        tasks.append((f"formal_alt_derivative_{order}", f"alt_{order}", KFORMAL))

    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = dict(pool.map(record_job, tasks))

    formal_lower = lower_wall(KFORMAL)
    corners = {
        "seam_floor": str(sp.factor(formal_lower.subs({core.S: 0, W: 0}))),
        "outer_floor": str(sp.factor(formal_lower.subs({core.S: 0, W: WMAX}))),
        "outer_floor_dW": str(sp.factor(sp.diff(formal_lower, W).subs({core.S: 0, W: WMAX}))),
    }
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers": args.workers,
        "parabolic_cone": {
            "X_floor": "191/10 + (147/20) w",
            "y_lower": "13/32 + w/32",
            "y_upper": "33/80 + w/12",
            "w_range": "0 <= w <= 9/100",
        },
        "base_terms": len(sp.Poly(BASE, core.X, W, core.Y).terms()),
        "base_degrees": [sp.Poly(BASE, core.X, W, core.Y).degree(v)
                         for v in (core.X, W, core.Y)],
        "records": records,
        "corners": corners,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
