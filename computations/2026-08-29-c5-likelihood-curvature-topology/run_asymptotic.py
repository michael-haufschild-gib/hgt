#!/usr/bin/env python3
"""Stable second-atom asymptotic attack on CLG interpolation convexity.

Factors out the squared higher-atom likelihood amplitude before evaluating M''. Diagnostic only;
no output may be imported into Lean.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("topology", HERE / "run_experiments.py")
TOPOLOGY = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = TOPOLOGY
SPEC.loader.exec_module(TOPOLOGY)


def initialize(dps):
    TOPOLOGY.initialize(dps)


def log_second_atom_ratio(A):
    return mp.log(4) + mp.log(8 * A - 3) - mp.log(2 * A - 3) - 3 * A


def log_derivatives(A):
    l1 = -6 * A * (16 * A**2 - 30 * A + 15) / ((2 * A - 3) * (8 * A - 3))
    l2 = (-12 * A * (256 * A**4 - 960 * A**3 + 1092 * A**2 - 540 * A + 135) /
          ((2 * A - 3)**2 * (8 * A - 3)**2))
    l3 = (-24 * A * (4096 * A**6 - 23040 * A**5 + 51648 * A**4 -
          50040 * A**3 + 23004 * A**2 - 5670 * A + 1215) /
          ((2 * A - 3)**3 * (8 * A - 3)**3))
    return l1, l2, l3


def normalized_ratio_jets(A, common_log):
    ratio = mp.exp(log_second_atom_ratio(A) - common_log)
    l1, l2, l3 = log_derivatives(A)
    return ratio, ratio * l1, ratio * (l2 + l1**2), ratio * (l3 + 3*l1*l2 + l1**3)


def leading_likelihood_direction(A, t):
    plus = A * mp.exp(2 * t)
    minus = A * mp.exp(-2 * t)
    common_log = max(log_second_atom_ratio(A), log_second_atom_ratio(plus),
                     log_second_atom_ratio(minus))
    z0, z1, z2, z3 = normalized_ratio_jets(A, common_log)
    p0, p1, p2, p3 = normalized_ratio_jets(plus, common_log)
    m0, m1, m2, m3 = normalized_ratio_jets(minus, common_log)
    return (
        2*z0-p0-m0,
        m1-p1,
        -p2-m2,
        m3-p3,
        2*z1-p1-m1,
        m2-p2,
        -p3-m3,
    )


def audit_point(task):
    A_text, t_text = task
    A = mp.mpf(A_text)
    t = mp.mpf(t_text)
    u = mp.log(A / mp.pi) / 2
    atom = TOPOLOGY.BASE.atom_jets(u, t)
    direction = leading_likelihood_direction(A, t)
    value = TOPOLOGY.margin_derivatives(atom, direction, t)
    sign = TOPOLOGY.robust_sign(value[2], value[4])
    third_sign = TOPOLOGY.robust_sign(value[3], value[5])
    return {
        "A": A_text,
        "u": mp.nstr(u, 25),
        "t": t_text,
        "tau": mp.nstr(t/u, 25),
        "second": mp.nstr(value[2], 60),
        "scale": mp.nstr(value[4], 60),
        "normalized": mp.nstr(value[2]/value[4] if value[4] else value[2], 60),
        "sign": sign,
        "third": mp.nstr(value[3], 60),
        "third_scale": mp.nstr(value[5], 60),
        "normalized_third": mp.nstr(value[3]/value[5] if value[5] else value[3], 60),
        "third_sign": third_sign,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("asymptotic-results.json"))
    parser.add_argument("--workers", type=int, default=min(128, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=120)
    parser.add_argument("--a-points", type=int, default=500)
    parser.add_argument("--t-points", type=int, default=500)
    parser.add_argument("--max-a", type=float, default=1e10)
    args = parser.parse_args()
    started = time.time()
    a_values = np.unique(np.concatenate((
        np.geomspace(6, 200, args.a_points // 3),
        np.geomspace(201, 1e5, args.a_points // 3),
        np.geomspace(1.01e5, args.max_a, args.a_points // 3),
    )))
    tasks = []
    for A_float in a_values:
        u = math.log(A_float / math.pi) / 2
        # Resolve both seam layer A*t=O(1) and macroscopic t/u.
        t_values = np.unique(np.concatenate((
            np.geomspace(1e-8 / A_float, min(u, 1e3 / A_float), args.t_points // 2),
            u * np.geomspace(1e-10, 1, args.t_points // 2),
            np.array([u]),
        )))
        tasks.extend((repr(float(A_float)), repr(float(t))) for t in t_values if 0 < t <= u)
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        records = list(pool.imap_unordered(audit_point, tasks, chunksize=20))
    negatives = [r for r in records if r["sign"] < 0]
    positives = [r for r in records if r["sign"] > 0]
    unresolved = [r for r in records if r["sign"] == 0]
    third_negatives = [r for r in records if r["third_sign"] < 0]
    third_positives = [r for r in records if r["third_sign"] > 0]
    third_unresolved = [r for r in records if r["third_sign"] == 0]
    minimum = min(records, key=lambda r: mp.mpf(r["normalized"]))
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "question": "sign of leading second-atom coefficient of M'' after exact amplitude removal",
        "parameters": {**vars(args), "output": str(args.output)},
        "points": len(records),
        "positive": len(positives),
        "negative": len(negatives),
        "unresolved": len(unresolved),
        "third_positive": len(third_positives),
        "third_negative": len(third_negatives),
        "third_unresolved": len(third_unresolved),
        "minimum": minimum,
        "first_negative": negatives[:30],
        "first_third_negative": third_negatives[:30],
        "elapsed_seconds": time.time() - started,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
