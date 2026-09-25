#!/usr/bin/env python3
"""Hostile exact test of intrinsic S6F clock-ratio wedge.

Diagnostic only. No output is admissible in a Lean proof.

The formal thin cone 2/5 <= y <= 1/2 is equivalent, for positive B, to

    2 B <= U <= 3 B,

because y = U/(U+3B).  This script asks the unknown stronger question whether
the literal source-positive projective drift is positive on the full intrinsic
wedge B>0, Q>0, 2B<=U<=3B, without scale or z bounds.
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

T = sp.Symbol("t")


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


def hybrid_record(expr: sp.Expr) -> dict:
    poly = sp.Poly(sp.expand(expr), core.B, core.Q, T, domain=sp.QQ)
    ordinary = poly.coeffs()
    by_bq: dict[tuple[int, int], sp.Expr] = {}
    for (eb, eq, et), value in poly.terms():
        key = (eb, eq)
        by_bq[key] = by_bq.get(key, sp.Rational(0)) + value * T**et
    bernstein = []
    records = []
    for key in sorted(by_bq):
        values = univariate_bernstein(by_bq[key], T)
        bernstein.extend(values)
        records.append({
            "BQ_power": list(key),
            "degree_t": sp.Poly(by_bq[key], T).degree(),
            "signs": signs(values),
        })
    digest = hashlib.sha256(
        "\n".join(str(v) for v in bernstein).encode("ascii")
    ).hexdigest()
    return {
        "degrees": [poly.degree(core.B), poly.degree(core.Q), poly.degree(T)],
        "terms": len(poly.terms()),
        "ordinary_power": signs(ordinary),
        "BQ_fibres": len(by_bq),
        "bernstein_t": signs(bernstein),
        "bernstein_sha256": digest,
        "fibre_records": records,
    }


def record_job(task: tuple[str, sp.Expr]) -> tuple[str, dict]:
    name, expr = task
    return name, hybrid_record(expr)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("intrinsic-results.json"))
    parser.add_argument("--workers", type=int, default=min(6, os.cpu_count() or 1))
    args = parser.parse_args()

    print("reconstructing literal source drift", file=sys.stderr, flush=True)
    drift = core.source_positive_drift()
    print("source drift reconstructed", file=sys.stderr, flush=True)
    wedge = sp.expand(drift.subs(core.U, core.B * (2 + T)))
    wedge_poly = sp.Poly(wedge, core.B, core.Q, T, domain=sp.QQ)
    min_b_degree = min(powers[0] for powers, _ in wedge_poly.terms())
    reduced = sp.expand(wedge / core.B**min_b_degree)
    assert sp.denom(reduced) == 1

    # Concavity and endpoint tests can reveal a smaller proof than a full
    # Bernstein certificate even when the wedge itself survives.
    tasks = [
        ("wedge_reduced", reduced),
        ("d_dt", sp.diff(reduced, T)),
        ("minus_d_dt", -sp.diff(reduced, T)),
        ("minus_d2_dt2", -sp.diff(reduced, T, 2)),
        ("lower_wall_t0", reduced.subs(T, 0)),
        ("upper_wall_t1", reduced.subs(T, 1)),
    ]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = dict(pool.map(record_job, tasks))
    endpoints = {
        "t0_terms": len(sp.Poly(reduced.subs(T, 0), core.B, core.Q).terms()),
        "t1_terms": len(sp.Poly(reduced.subs(T, 1), core.B, core.Q).terms()),
    }
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "workers_requested": args.workers,
        "intrinsic_wedge": "B>0, Q>0, U=B*(2+t), 0<=t<=1",
        "source_drift_terms": len(sp.Poly(drift, core.U, core.B, core.Q).terms()),
        "source_drift_degrees": [
            sp.Poly(drift, core.U, core.B, core.Q).degree(v)
            for v in (core.U, core.B, core.Q)
        ],
        "factored_B_power": min_b_degree,
        "endpoint_complexity": endpoints,
        "records": records,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
