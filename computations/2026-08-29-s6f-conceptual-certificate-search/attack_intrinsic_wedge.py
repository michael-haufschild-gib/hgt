#!/usr/bin/env python3
"""Search for and exactly verify a counterexample to intrinsic S6F wedge.

Diagnostic only. No output is admissible in a Lean proof.
"""

from __future__ import annotations

import argparse
import concurrent.futures
from fractions import Fraction
import importlib.util
import json
import os
import sys
from pathlib import Path

import numpy as np
import sympy as sp


HERE = Path(__file__).resolve().parent
CORE_PATH = HERE.parent / "2026-08-29-s6f-normalized-chamber-search" / "run_experiments.py"
spec = importlib.util.spec_from_file_location("s6f_core", CORE_PATH)
core = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = core
spec.loader.exec_module(core)

T = sp.Symbol("t")
WEDGE_EXPR: sp.Expr | None = None


def random_job(task: tuple[int, int, float]) -> dict:
    count, seed, log_radius = task
    assert WEDGE_EXPR is not None
    fn = sp.lambdify((core.B, core.Q, T), WEDGE_EXPR, modules="numpy", cse=True)
    rng = np.random.default_rng(seed)
    b = np.power(10.0, rng.uniform(-log_radius, log_radius, count))
    q = np.power(10.0, rng.uniform(-log_radius, log_radius, count))
    t = rng.random(count)
    values = np.asarray(fn(b, q, t), dtype=np.float64)
    finite = np.isfinite(values)
    safe = np.where(finite, values, np.inf)
    index = int(np.argmin(safe))
    return {
        "minimum": float(safe[index]),
        "finite": int(np.count_nonzero(finite)),
        "witness": {"B": float(b[index]), "Q": float(q[index]), "t": float(t[index])},
    }


def rational(value: float, denominator: int) -> sp.Rational:
    f = Fraction(value).limit_denominator(denominator)
    return sp.Rational(f.numerator, f.denominator)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("intrinsic-attack-results.json"))
    parser.add_argument("--samples", type=int, default=600_000)
    parser.add_argument("--workers", type=int, default=min(6, os.cpu_count() or 1))
    parser.add_argument("--log-radius", type=float, default=3.0)
    args = parser.parse_args()

    print("reconstructing intrinsic wedge", file=sys.stderr, flush=True)
    drift = core.source_positive_drift()
    global WEDGE_EXPR
    WEDGE_EXPR = sp.expand(sp.cancel(drift.subs(core.U, core.B * (2 + T)) / core.B))
    assert sp.denom(WEDGE_EXPR) == 1

    per_worker = args.samples // args.workers
    tasks = [
        (per_worker + (1 if i < args.samples % args.workers else 0), 2026082900 + i, args.log_radius)
        for i in range(args.workers)
    ]
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        records = list(pool.map(random_job, tasks))
    winner = min(records, key=lambda record: record["minimum"])

    exact = None
    if winner["minimum"] < 0:
        w = winner["witness"]
        rb = rational(w["B"], 10_000)
        rq = rational(w["Q"], 10_000)
        rt = rational(w["t"], 10_000)
        value = sp.factor(WEDGE_EXPR.subs({core.B: rb, core.Q: rq, T: rt}))
        exact = {
            "B": str(rb),
            "Q": str(rq),
            "t": str(rt),
            "U": str(sp.factor(rb * (2 + rt))),
            "reduced_drift": str(value),
            "negative": bool(value < 0),
        }

    simple_candidates = []
    for b, q, t in [
        (1, 1, sp.Rational(0)),
        (1, 1, sp.Rational(1, 4)),
        (1, 1, sp.Rational(1, 2)),
        (1, 1, sp.Rational(3, 4)),
        (1, 1, 1),
        (2, 4, 1),
        (4, 16, 1),
        (8, 64, 1),
        (16, 256, 1),
        (32, 1024, 1),
        (30, 1000, 1),
        (32, 1000, 1),
    ]:
        value = sp.factor(WEDGE_EXPR.subs({core.B: b, core.Q: q, T: t}))
        simple_candidates.append({
            "B": b,
            "Q": q,
            "t": str(t),
            "U": str(b * (2 + t)),
            "reduced_drift": str(value),
            "negative": bool(value < 0),
        })

    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "samples": args.samples,
        "workers": args.workers,
        "log10_range_BQ": [-args.log_radius, args.log_radius],
        "worker_records": records,
        "winner": winner,
        "exact_rationalization": exact,
        "simple_exact_candidates": simple_candidates,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
