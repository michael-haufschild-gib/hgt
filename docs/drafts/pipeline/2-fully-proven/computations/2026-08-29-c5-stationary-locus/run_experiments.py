#!/usr/bin/env python3
"""Source-faithful hostile scan of modular-center C5 stationary locus.

Diagnostic only. No output may be imported into Lean proofs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import time
from multiprocessing import Pool
from pathlib import Path

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import mpmath as mp
import numpy as np


POLYNOMIALS = None
P0 = None


def derivative_polynomials(a: mp.mpf, order: int):
    polynomial = [mp.mpf(1)]
    answer = [polynomial]
    for _ in range(order):
        following = [mp.mpf(0)] * (len(polynomial) + 1)
        for degree, coefficient in enumerate(polynomial):
            following[degree] += a * coefficient
            following[degree + 1] -= 2 * coefficient
            if degree:
                following[degree] += 2 * degree * coefficient
        polynomial = following
        answer.append(polynomial)
    return answer


def initialize(dps: int) -> None:
    global POLYNOMIALS, P0
    mp.mp.dps = dps
    POLYNOMIALS = (
        derivative_polynomials(mp.mpf(9) / 2, 4),
        derivative_polynomials(mp.mpf(5) / 2, 4),
    )
    P0 = source_derivatives(mp.mpf(0))[0] ** 2


def polynomial_eval(coefficients, value):
    answer = mp.mpf(0)
    for coefficient in reversed(coefficients):
        answer = answer * value + coefficient
    return answer


def source_derivatives(x: mp.mpf):
    # Production domain is x > 0. n <= 16 gives an enormous tail margin near zero;
    # n = 1 suffices far in the cusp.
    nmax = 1 if x >= 2 else 16
    result = [mp.mpf(0)] * 5
    e2x = mp.exp(2 * x)
    for n in range(1, nmax + 1):
        nn = mp.mpf(n)
        c = mp.pi * nn**2 * e2x
        branches = (
            (4 * mp.pi**2 * nn**4, mp.mpf(9) / 2, POLYNOMIALS[0]),
            (-6 * mp.pi * nn**2, mp.mpf(5) / 2, POLYNOMIALS[1]),
        )
        for amplitude, exponent, polynomials in branches:
            base = amplitude * mp.exp(exponent * x - c)
            for order in range(5):
                result[order] += base * polynomial_eval(polynomials[order], c)
    return result


def c5_stationary_data(t):
    """Return normalized `(N, V=N', V'=N'')` from literal center source."""
    t = mp.mpf(t)
    f0, f1, f2, f3, f4 = source_derivatives(t)
    p = f0**2
    p1 = 2 * f0 * f1
    p2 = 2 * (f1**2 + f0 * f2)
    p3 = 2 * (3 * f1 * f2 + f0 * f3)
    p4 = 2 * (3 * f2**2 + 4 * f1 * f3 + f0 * f4)
    a = P0 - p
    d = -p1
    j = -p2
    k = -p3
    ell = -p4
    numerator = 24 * a**2 - 9 * t * a * d + t**2 * (5 * a * j - 4 * d**2)
    velocity = (
        39 * a * d + t * a * j - 17 * t * d**2
        + t**2 * (5 * a * k - 3 * d * j)
    )
    acceleration = (
        22 * d**2 + 40 * a * j + t * (11 * a * k - 39 * d * j)
        + t**2 * (2 * d * k + 5 * a * ell - 3 * j**2)
    )
    scale = P0**2
    return numerator / scale, velocity / scale, acceleration / scale


def evaluate_chunk(ts):
    rows = []
    for t in ts:
        numerator, velocity, acceleration = c5_stationary_data(t)
        rows.append((float(t), int(mp.sign(numerator)), int(mp.sign(velocity)),
                     float(mp.log10(abs(numerator))) if numerator else -math.inf,
                     float(mp.log10(abs(velocity))) if velocity else -math.inf,
                     mp.nstr(numerator, 25), mp.nstr(velocity, 25),
                     mp.nstr(acceleration, 25)))
    return rows


def bisect_velocity(left, right, iterations=400):
    left, right = mp.mpf(left), mp.mpf(right)
    vl = c5_stationary_data(left)[1]
    vr = c5_stationary_data(right)[1]
    if mp.sign(vl) == mp.sign(vr):
        raise ValueError("root bracket has equal signs")
    for _ in range(iterations):
        middle = (left + right) / 2
        vm = c5_stationary_data(middle)[1]
        if vm == 0:
            left = right = middle
            break
        if mp.sign(vm) == mp.sign(vl):
            left, vl = middle, vm
        else:
            right, vr = middle, vm
    root = (left + right) / 2
    n, v, a = c5_stationary_data(root)
    return {
        "bracket": [mp.nstr(left, 70), mp.nstr(right, 70)],
        "root_midpoint": mp.nstr(root, 70),
        "normalized_c5": mp.nstr(n, 70),
        "normalized_velocity": mp.nstr(v, 20),
        "normalized_acceleration": mp.nstr(a, 70),
    }


def run(args):
    started = time.time()
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    ts = np.unique(np.concatenate((
        np.geomspace(args.t_min, args.t_max, args.log_points),
        np.linspace(args.t_min, min(args.t_max, 12.0), args.linear_points),
    )))
    chunks = [chunk.tolist() for chunk in np.array_split(ts, args.workers * 4) if len(chunk)]
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        rows = [row for block in pool.imap(evaluate_chunk, chunks, chunksize=1) for row in block]
    rows.sort(key=lambda row: row[0])

    sign_change_brackets = []
    for left, right in zip(rows, rows[1:]):
        if left[2] * right[2] < 0:
            sign_change_brackets.append((left[0], right[0]))

    initialize(args.dps)
    roots = [bisect_velocity(left, right) for left, right in sign_change_brackets]
    minimum_n = min(rows, key=lambda row: float(row[5]))
    smallest_v = min(rows, key=lambda row: row[4])
    digest = hashlib.sha256("\n".join(
        f"{row[0]:.17g},{row[1]},{row[2]},{row[5]},{row[6]}" for row in rows
    ).encode()).hexdigest()
    result = {
        "scope": "diagnostic only; forbidden as input to Lean proofs",
        "parameters": vars(args),
        "points": len(rows),
        "numerator_sign_counts": {
            "negative": sum(row[1] < 0 for row in rows),
            "zero": sum(row[1] == 0 for row in rows),
            "positive": sum(row[1] > 0 for row in rows),
        },
        "velocity_sign_counts": {
            "negative": sum(row[2] < 0 for row in rows),
            "zero": sum(row[2] == 0 for row in rows),
            "positive": sum(row[2] > 0 for row in rows),
        },
        "velocity_sign_change_brackets": sign_change_brackets,
        "stationary_roots": roots,
        "sample_minimum_normalized_c5": minimum_n[:5] + (minimum_n[5],),
        "sample_smallest_abs_velocity": smallest_v[:5] + (smallest_v[6],),
        "row_digest": digest,
        "environment": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "workers": args.workers,
            "mpmath": mp.__version__,
            "numpy": np.__version__,
        },
        "elapsed_seconds": time.time() - started,
    }
    (output / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="results")
    parser.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=120)
    parser.add_argument("--t-min", type=float, default=1e-8)
    parser.add_argument("--t-max", type=float, default=100.0)
    parser.add_argument("--log-points", type=int, default=60_000)
    parser.add_argument("--linear-points", type=int, default=20_000)
    return parser.parse_args()


if __name__ == "__main__":
    arguments = parse_args()
    initialize(arguments.dps)
    run(arguments)
