#!/usr/bin/env python3
"""Route-decisive topology attack on CLG likelihood-homotopy curvature.

Diagnostic only. No output from this script may be imported into Lean.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
import platform
import random
import sys
import time
from multiprocessing import Pool
from pathlib import Path

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
BASE_PATH = HERE.parent / "2026-08-29-c5-likelihood-interpolation" / "run_experiments.py"
SPEC = importlib.util.spec_from_file_location("c5_interpolation", BASE_PATH)
BASE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = BASE
SPEC.loader.exec_module(BASE)


def initialize(dps: int) -> None:
    BASE.initialize(dps)


def margin_derivatives(jets, likelihood, t):
    """Return M, M', M'', M''' and cancellation scales for M'', M'''."""
    q, a, b, c, s, m, n = jets
    dq, da, db, dc, ds, dm, dn = likelihood
    r = mp.expm1(q)
    eq = mp.exp(q)
    v = t * a
    dv = t * da
    h = a * t * m - (a + t * b) * s
    dh = da * t * m + a * t * dm - (da + t * db) * s - (a + t * b) * ds
    ddh = 2 * (da * t * dm - (da + t * db) * ds)
    p = a * (t * m + t**2 * n) - (a + 3 * t * b + t**2 * c) * s
    dp = (da * (t * m + t**2 * n) + a * (t * dm + t**2 * dn)
          - (da + 3 * t * db + t**2 * dc) * s
          - (a + 3 * t * b + t**2 * c) * ds)
    ddp = 2 * (da * (t * dm + t**2 * dn)
               - (da + 3 * t * db + t**2 * dc) * ds)
    g = 1 / r
    gp = -eq * dq / r**2
    gpp = eq * (eq + 1) * dq**2 / r**3
    gppp = -eq * (eq**2 + 4 * eq + 1) * dq**3 / r**4
    w = 14 + 10 * v + 8 * v * g
    wp = 10 * dv + 8 * (dv * g + v * gp)
    wpp = 8 * (2 * dv * gp + v * gpp)
    wppp = 8 * (3 * dv * gpp + v * gppp)
    margin = 5 * p - w * h
    first = 5 * dp - wp * h - w * dh
    second_terms = (5 * ddp, -wpp * h, -2 * wp * dh, -w * ddh)
    second = sum(second_terms)
    third_terms = (-wppp * h, -3 * wpp * dh, -3 * wp * ddh)
    third = sum(third_terms)
    second_scale = max(map(abs, second_terms))
    third_scale = max(map(abs, third_terms))
    return margin, first, second, third, second_scale, third_scale


def at_lambda(atom, likelihood, t, lam):
    jets = tuple(atom[i] + lam * likelihood[i] for i in range(7))
    return margin_derivatives(jets, likelihood, t)


def robust_sign(value, scale):
    relative = mp.power(10, -mp.mp.dps / 3)
    if scale == 0:
        return 0 if value == 0 else (1 if value > 0 else -1)
    if abs(value) <= relative * scale:
        return 0
    return 1 if value > 0 else -1


def bisect_third(atom, likelihood, t, left, right):
    fl = at_lambda(atom, likelihood, t, left)[3]
    fr = at_lambda(atom, likelihood, t, right)[3]
    for _ in range(100):
        mid = (left + right) / 2
        fm = at_lambda(atom, likelihood, t, mid)[3]
        if fm == 0:
            return mid
        if (fl < 0) == (fm < 0):
            left, fl = mid, fm
        else:
            right, fr = mid, fm
    return (left + right) / 2


def empty_summary():
    return {
        "pairs": 0,
        "lambda_evaluations": 0,
        "third_all_positive": 0,
        "third_all_negative": 0,
        "third_mixed": 0,
        "third_unresolved": 0,
        "third_sign_change_brackets": 0,
        "robust_negative_second": 0,
        "minimum_normalized_second": None,
        "minimum_point": None,
        "first_mixed_third": [],
        "first_negative_second": [],
    }


def audit_pair(u_value, tau_value, lambda_count):
    u = mp.mpf(u_value)
    tau = mp.mpf(tau_value)
    t = u * tau
    atom = BASE.atom_jets(u, t)
    full = BASE.full_jets(u, t)
    likelihood = tuple(full[i] - atom[i] for i in range(7))
    lambdas = [mp.mpf(i) / (lambda_count - 1) for i in range(lambda_count)]
    values = [at_lambda(atom, likelihood, t, lam) for lam in lambdas]
    signs = [robust_sign(value[3], value[5]) for value in values]
    roots = []
    brackets = 0
    for i in range(lambda_count - 1):
        if signs[i] * signs[i + 1] < 0:
            brackets += 1
            roots.append(bisect_third(atom, likelihood, t, lambdas[i], lambdas[i + 1]))
    candidates = [(lambdas[0], values[0]), (lambdas[-1], values[-1])]
    candidates.extend((root, at_lambda(atom, likelihood, t, root)) for root in roots)
    best_lam, best = min(candidates, key=lambda item: item[1][2] / item[1][4]
                         if item[1][4] != 0 else item[1][2])
    normalized = best[2] / best[4] if best[4] != 0 else best[2]
    negative = robust_sign(best[2], best[4]) < 0
    return {
        "u": float(u),
        "tau": float(tau),
        "t": mp.nstr(t, 30),
        "evaluations": lambda_count + len(roots),
        "signs": signs,
        "brackets": brackets,
        "best_lambda": mp.nstr(best_lam, 30),
        "best_second": mp.nstr(best[2], 50),
        "best_second_scale": mp.nstr(best[4], 50),
        "best_normalized_second": mp.nstr(normalized, 50),
        "negative_second": negative,
    }


def deterministic_worker(task):
    u, tau_values, lambda_count = task
    return [audit_pair(u, tau, lambda_count) for tau in tau_values]


def random_worker(task):
    seed, count, u_min, u_max, lambda_count = task
    rng = random.Random(seed)
    records = []
    for _ in range(count):
        u = math.exp(rng.uniform(math.log(u_min), math.log(u_max)))
        draw = rng.random()
        if draw < 0.4:
            tau = 10 ** rng.uniform(-10, -1)
        elif draw < 0.8:
            tau = 1 - 10 ** rng.uniform(-10, -1)
        else:
            tau = rng.uniform(1e-10, 1)
        records.append(audit_pair(u, tau, lambda_count))
    return records


def merge(groups):
    summary = empty_summary()
    for group in groups:
        for record in group:
            summary["pairs"] += 1
            summary["lambda_evaluations"] += record["evaluations"]
            signs = record["signs"]
            nonzero = [s for s in signs if s]
            if nonzero and all(s > 0 for s in nonzero):
                summary["third_all_positive"] += 1
            elif nonzero and all(s < 0 for s in nonzero):
                summary["third_all_negative"] += 1
            elif any(s > 0 for s in nonzero) and any(s < 0 for s in nonzero):
                summary["third_mixed"] += 1
                if len(summary["first_mixed_third"]) < 20:
                    summary["first_mixed_third"].append(record)
            else:
                summary["third_unresolved"] += 1
            summary["third_sign_change_brackets"] += record["brackets"]
            if record["negative_second"]:
                summary["robust_negative_second"] += 1
                if len(summary["first_negative_second"]) < 20:
                    summary["first_negative_second"].append(record)
            value = mp.mpf(record["best_normalized_second"])
            if (summary["minimum_normalized_second"] is None or
                    value < mp.mpf(summary["minimum_normalized_second"])):
                summary["minimum_normalized_second"] = record["best_normalized_second"]
                summary["minimum_point"] = record
    return summary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(128, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=140)
    parser.add_argument("--u-points", type=int, default=160)
    parser.add_argument("--tau-points", type=int, default=260)
    parser.add_argument("--lambda-points", type=int, default=33)
    parser.add_argument("--random-pairs", type=int, default=30000)
    parser.add_argument("--max-u", type=float, default=20.0)
    parser.add_argument("--seed", type=int, default=20260829)
    args = parser.parse_args()
    started = time.time()
    u_min = float(mp.log(6 / mp.pi) / 2)
    u_parts = [
        np.geomspace(u_min, min(2, args.max_u), max(40, args.u_points // 2)),
        np.linspace(u_min, args.max_u, args.u_points),
    ]
    if 5.01 < args.max_u:
        u_parts.append(np.geomspace(5.01, args.max_u, max(40, args.u_points // 3)))
    u_values = np.unique(np.concatenate(u_parts))
    tau_values = np.unique(np.concatenate((
        np.geomspace(1e-10, 1e-2, max(70, args.tau_points // 3)),
        np.linspace(1e-2, 0.99, args.tau_points),
        1 - np.geomspace(1e-10, 1e-2, max(70, args.tau_points // 3)),
        np.array([1.0]),
    )))
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        deterministic = merge(pool.imap_unordered(
            deterministic_worker,
            [(float(u), [float(t) for t in tau_values], args.lambda_points)
             for u in u_values], chunksize=1))
    chunk = max(20, math.ceil(args.random_pairs / (args.workers * 4)))
    tasks = []
    remaining = args.random_pairs
    seed = args.seed
    while remaining:
        count = min(chunk, remaining)
        tasks.append((seed, count, u_min, args.max_u, args.lambda_points))
        seed += 1
        remaining -= count
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        randomized = merge(pool.imap_unordered(random_worker, tasks, chunksize=1))
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "question": "is M'' monotone in lambda, or does exact M'' fail at an endpoint/interior critical point?",
        "parameters": {**vars(args), "output": str(args.output)},
        "domain": "A=pi*exp(2u)>=6, 0<t<=u, 0<=lambda<=1",
        "deterministic_grid_shape": [len(u_values), len(tau_values), args.lambda_points],
        "deterministic": deterministic,
        "randomized": randomized,
        "elapsed_seconds": time.time() - started,
        "environment": {
            "python": platform.python_version(),
            "mpmath": mp.__version__,
            "numpy": np.__version__,
            "workers": args.workers,
        },
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
