#!/usr/bin/env python3
"""Test atom-tangent reserve for the literal C5 likelihood homotopy.

Diagnostic only. No output from this script may be imported into a Lean proof.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
import platform
import random
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
SPEC = importlib.util.spec_from_file_location("c5_likelihood_interpolation", BASE_PATH)
BASE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(BASE)


def initialize(dps: int) -> None:
    BASE.initialize(dps)


def empty_summary() -> dict:
    return {
        "count": 0,
        "nonpositive_atom_margin": [],
        "nonpositive_tangent_reserve": [],
        "nonpositive_full_margin": [],
        "negative_convexity_gap": [],
        "robust_negative_convexity_gap": [],
        "negative_atom_derivative": 0,
        "positive_atom_derivative": 0,
        "minimum_tangent_reserve": None,
        "minimum_tangent_point": None,
        "minimum_reserve_ratio": None,
        "minimum_reserve_ratio_point": None,
        "maximum_tax_ratio": None,
        "maximum_tax_ratio_point": None,
        "minimum_convexity_gap": None,
        "minimum_convexity_gap_point": None,
    }


def update(summary: dict, u: float, tau: float) -> None:
    t, _, endpoints, samples = BASE.point_record(u, tau, [0])
    _, atom_margin, atom_derivative, _ = samples[0]
    full_margin = endpoints[1]
    tangent_reserve = atom_margin + atom_derivative
    convexity_gap = full_margin - tangent_reserve
    gap_resolution = max(mp.mpf(1), abs(full_margin), abs(tangent_reserve)) * \
        mp.power(10, -mp.mp.dps / 2)
    reserve_ratio = tangent_reserve / atom_margin
    tax_ratio = -atom_derivative / atom_margin
    summary["count"] += 1
    record = [float(u), float(tau), mp.nstr(t, 30)]
    for key, value in (
        ("nonpositive_atom_margin", atom_margin),
        ("nonpositive_tangent_reserve", tangent_reserve),
        ("nonpositive_full_margin", full_margin),
        ("negative_convexity_gap", convexity_gap),
    ):
        if value <= 0 and len(summary[key]) < 50:
            summary[key].append(record + [mp.nstr(value, 40)])
    if convexity_gap < -gap_resolution and len(summary["robust_negative_convexity_gap"]) < 50:
        summary["robust_negative_convexity_gap"].append(
            record + [mp.nstr(convexity_gap, 40), mp.nstr(gap_resolution, 20)])
    if atom_derivative < 0:
        summary["negative_atom_derivative"] += 1
    elif atom_derivative > 0:
        summary["positive_atom_derivative"] += 1
    if (summary["minimum_tangent_reserve"] is None or
            tangent_reserve < mp.mpf(summary["minimum_tangent_reserve"])):
        summary["minimum_tangent_reserve"] = mp.nstr(tangent_reserve, 40)
        summary["minimum_tangent_point"] = record + [
            mp.nstr(atom_margin, 30), mp.nstr(atom_derivative, 30),
            mp.nstr(full_margin, 30)]
    if (summary["minimum_reserve_ratio"] is None or
            reserve_ratio < mp.mpf(summary["minimum_reserve_ratio"])):
        summary["minimum_reserve_ratio"] = mp.nstr(reserve_ratio, 40)
        summary["minimum_reserve_ratio_point"] = record + [
            mp.nstr(atom_margin, 30), mp.nstr(atom_derivative, 30)]
    if (summary["maximum_tax_ratio"] is None or
            tax_ratio > mp.mpf(summary["maximum_tax_ratio"])):
        summary["maximum_tax_ratio"] = mp.nstr(tax_ratio, 40)
        summary["maximum_tax_ratio_point"] = record + [
            mp.nstr(atom_margin, 30), mp.nstr(atom_derivative, 30)]
    if (summary["minimum_convexity_gap"] is None or
            convexity_gap < mp.mpf(summary["minimum_convexity_gap"])):
        summary["minimum_convexity_gap"] = mp.nstr(convexity_gap, 40)
        summary["minimum_convexity_gap_point"] = record + [
            mp.nstr(tangent_reserve, 30), mp.nstr(full_margin, 30)]


def deterministic_worker(task: tuple[float, list[float]]) -> dict:
    u, tau_values = task
    summary = empty_summary()
    for tau in tau_values:
        update(summary, u, tau)
    return summary


def random_worker(task: tuple[int, int, float, float]) -> dict:
    seed, count, u_min, u_max = task
    generator = random.Random(seed)
    summary = empty_summary()
    for _ in range(count):
        if generator.random() < 0.7:
            u = math.exp(generator.uniform(math.log(u_min), math.log(u_max)))
        else:
            u = generator.uniform(u_min, u_max)
        draw = generator.random()
        if draw < 0.35:
            tau = 10 ** generator.uniform(-10, 0)
        elif draw < 0.7:
            tau = 1 - 10 ** generator.uniform(-10, 0)
        else:
            tau = generator.uniform(1e-10, 1)
        update(summary, u, tau)
    return summary


def merge(records: list[dict]) -> dict:
    result = empty_summary()
    for record in records:
        result["count"] += record["count"]
        result["negative_atom_derivative"] += record["negative_atom_derivative"]
        result["positive_atom_derivative"] += record["positive_atom_derivative"]
        for key in ("nonpositive_atom_margin", "nonpositive_tangent_reserve",
                    "nonpositive_full_margin", "negative_convexity_gap",
                    "robust_negative_convexity_gap"):
            result[key].extend(record[key])
            result[key] = result[key][:50]
        for value_key, point_key, relation in (
            ("minimum_tangent_reserve", "minimum_tangent_point", "min"),
            ("minimum_reserve_ratio", "minimum_reserve_ratio_point", "min"),
            ("maximum_tax_ratio", "maximum_tax_ratio_point", "max"),
            ("minimum_convexity_gap", "minimum_convexity_gap_point", "min"),
        ):
            value = record[value_key]
            if value is None:
                continue
            current = result[value_key]
            improves = current is None or (
                mp.mpf(value) < mp.mpf(current) if relation == "min"
                else mp.mpf(value) > mp.mpf(current))
            if improves:
                result[value_key] = value
                result[point_key] = record[point_key]
    return result


def run(args) -> None:
    started = time.time()
    u_min = float(mp.log(6 / mp.pi) / 2)
    u_values = np.unique(np.concatenate((
        np.geomspace(u_min, 2, max(32, args.u_points // 2)),
        np.linspace(u_min, 4, args.u_points),
        np.geomspace(4.01, args.max_u, max(32, args.u_points // 3)),
    )))
    tau_values = np.unique(np.concatenate((
        np.geomspace(1e-10, 1e-2, max(64, args.tau_points // 3)),
        np.linspace(1e-2, 0.99, args.tau_points),
        1 - np.geomspace(1e-10, 1e-2, max(64, args.tau_points // 3)),
        np.array([1.0]),
    )))
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        deterministic = merge(list(pool.imap_unordered(
            deterministic_worker,
            [(float(u), [float(tau) for tau in tau_values]) for u in u_values],
            chunksize=1)))
    chunk = max(100, math.ceil(args.random_points / (args.workers * 4)))
    tasks = []
    remaining = args.random_points
    seed = args.seed
    while remaining:
        count = min(chunk, remaining)
        tasks.append((seed, count, u_min, args.max_u))
        seed += 1
        remaining -= count
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        randomized = merge(list(pool.imap_unordered(random_worker, tasks, chunksize=1)))
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "question": "does atom margin plus its exact likelihood first variation remain positive?",
        "domain": "A=pi*exp(2u)>=6, 0<t<=u",
        "implication_tested": "convex M(lambda) and M(0)+M'(0)>0 imply M(1)>0",
        "parameters": {**vars(args), "output": str(args.output)},
        "deterministic_grid_shape": [len(u_values), len(tau_values)],
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


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(128, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=140)
    parser.add_argument("--u-points", type=int, default=160)
    parser.add_argument("--tau-points", type=int, default=280)
    parser.add_argument("--random-points", type=int, default=200000)
    parser.add_argument("--max-u", type=float, default=20.0)
    parser.add_argument("--seed", type=int, default=20260829)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
