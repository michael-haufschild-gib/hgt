#!/usr/bin/env python3
"""Hostile numerical test of direct fixed-action C5 barrier transport.

Diagnostic only. No output may be imported into a Lean proof.
"""

from __future__ import annotations

import argparse
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


POLYNOMIALS = None


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
    global POLYNOMIALS
    mp.mp.dps = dps
    POLYNOMIALS = (
        derivative_polynomials(mp.mpf(9) / 2, 3),
        derivative_polynomials(mp.mpf(5) / 2, 3),
    )


def polynomial_eval(coefficients, value):
    answer = mp.mpf(0)
    for coefficient in reversed(coefficients):
        answer = answer * value + coefficient
    return answer


def source_derivatives(x: mp.mpf, nmax: int = 30):
    sign = 1 if x >= 0 else -1
    x = abs(x)
    result = [mp.mpf(0)] * 4
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
            for order in range(4):
                result[order] += base * polynomial_eval(polynomials[order], c)
    if sign < 0:
        result[1] = -result[1]
        result[3] = -result[3]
    return result


def log_jets(x: mp.mpf):
    f0, f1, f2, f3 = source_derivatives(x)
    first = f1 / f0
    second = f2 / f0 - first**2
    third = f3 / f0 - 3 * f2 * f1 / f0**2 + 2 * first**3
    return mp.log(f0), first, second, third


def fixed_action_jacobian(u, t, centre=None):
    """Return `(q, B, J)` with `J = B_u q_t - B_t q_u`.

    `B = C5/(4 r^2)` in action coordinates and `r = exp(q)-1`. The formulas
    differentiate B directly, avoiding overflow and cancellation from C5 itself.
    """
    u, t = mp.mpf(u), mp.mpf(t)
    l0, l1, _, _ = centre if centre is not None else log_jets(u)
    lp0, lp1, lp2, lp3 = log_jets(u + t)
    lm0, lm1, lm2, lm3 = log_jets(u - t)
    q = 2 * l0 - lp0 - lm0
    q_u = 2 * l1 - lp1 - lm1
    q_t = lm1 - lp1
    q_tt = -lp2 - lm2
    q_tu = lm2 - lp2
    q_ttu = -(lp3 + lm3)
    q_ttt = lm3 - lp3

    inverse_r = 1 / mp.expm1(q)
    b = 6 - mp.mpf(9) / 4 * t * q_t * inverse_r
    b += mp.mpf(5) / 4 * t**2 * (q_tt - q_t**2) * inverse_r
    b -= t**2 * q_t**2 * inverse_r**2

    b_r = -mp.mpf(9) / 4 * t * q_t
    b_r += mp.mpf(5) / 4 * t**2 * (q_tt - q_t**2)
    b_r -= 2 * t**2 * q_t**2 * inverse_r
    b_q = b_r * (-inverse_r - inverse_r**2)
    b_t_explicit = -mp.mpf(9) / 4 * q_t * inverse_r
    b_t_explicit += mp.mpf(5) / 2 * t * (q_tt - q_t**2) * inverse_r
    b_t_explicit -= 2 * t * q_t**2 * inverse_r**2
    b_qt = -mp.mpf(9) / 4 * t * inverse_r
    b_qt -= mp.mpf(5) / 2 * t**2 * q_t * inverse_r
    b_qt -= 2 * t**2 * q_t * inverse_r**2
    b_qtt = mp.mpf(5) / 4 * t**2 * inverse_r

    b_u = b_q * q_u + b_qt * q_tu + b_qtt * q_ttu
    b_t = b_t_explicit + b_q * q_t + b_qt * q_tt + b_qtt * q_ttt
    jacobian = b_u * q_t - b_t * q_u
    return q, b, jacobian


def summarize_points(points):
    negative = []
    negative_count = 0
    zero_count = 0
    positive_count = 0
    smallest_log_abs = None
    smallest_point = None
    for u, t, centre in points:
        q, barrier, jacobian = fixed_action_jacobian(u, t, centre)
        sign = int(mp.sign(jacobian))
        if sign < 0:
            negative_count += 1
            if len(negative) < 100:
                negative.append({
                    "u": float(u), "t": float(t),
                    "q": mp.nstr(q, 30), "barrier": mp.nstr(barrier, 30),
                    "jacobian": mp.nstr(jacobian, 30),
                })
        elif sign == 0:
            zero_count += 1
        else:
            positive_count += 1
        if jacobian:
            log_abs = float(mp.log10(abs(jacobian)))
            if smallest_log_abs is None or log_abs < smallest_log_abs:
                smallest_log_abs = log_abs
                smallest_point = [float(u), float(t), sign, mp.nstr(jacobian, 30)]
    return {
        "count": len(points),
        "negative_count": negative_count,
        "negative_first_100": negative,
        "zero_count": zero_count,
        "positive_count": positive_count,
        "smallest_log10_abs": smallest_log_abs,
        "smallest_point": smallest_point,
    }


def grid_worker(task):
    u, ts = task
    centre = log_jets(mp.mpf(u))
    points = [(u, t, centre) for t in ts]
    return summarize_points(points)


def random_worker(task):
    seed, count = task
    generator = random.Random(seed)
    points = []
    for _ in range(count):
        if generator.random() < 0.7:
            u = 10 ** generator.uniform(-7, math.log10(20))
        else:
            u = generator.uniform(0.0, 20.0)
        if generator.random() < 0.8:
            t = 10 ** generator.uniform(-5, 2)
        else:
            t = generator.uniform(1e-5, 100.0)
        points.append((u, t, None))
    return summarize_points(points)


def merge(records):
    negative = [item for record in records for item in record["negative_first_100"]][:100]
    nonempty = [record for record in records if record["smallest_log10_abs"] is not None]
    smallest = min(nonempty, key=lambda record: record["smallest_log10_abs"])
    return {
        "count": sum(record["count"] for record in records),
        "negative_count": sum(record["negative_count"] for record in records),
        "negative_first_100": negative,
        "zero_count": sum(record["zero_count"] for record in records),
        "positive_count": sum(record["positive_count"] for record in records),
        "smallest_log10_abs": smallest["smallest_log10_abs"],
        "smallest_point": smallest["smallest_point"],
    }


def run(args):
    started = time.time()
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    us = np.unique(np.concatenate((
        np.geomspace(1e-7, 1e-2, max(32, args.u_points // 5)),
        np.linspace(1e-2, 8.0, args.u_points),
        np.geomspace(8.01, 20.0, max(32, args.u_points // 4)),
    )))
    ts = np.unique(np.concatenate((
        np.geomspace(1e-5, 100.0, args.t_points),
        np.linspace(1e-2, 4.0, max(64, args.t_points // 3)),
    )))

    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        grid = merge(list(pool.imap_unordered(
            grid_worker, [(float(u), [float(t) for t in ts]) for u in us], chunksize=1)))
    chunk = max(100, math.ceil(args.random_points / (args.workers * 4)))
    tasks = []
    remaining = args.random_points
    seed = args.seed
    while remaining:
        count = min(chunk, remaining)
        tasks.append((seed, count))
        seed += 1
        remaining -= count
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        random_summary = merge(list(pool.imap_unordered(random_worker, tasks, chunksize=1)))

    result = {
        "scope": "diagnostic only; forbidden as input to Lean proofs",
        "parameters": vars(args),
        "grid_shape": [len(us), len(ts)],
        "grid": grid,
        "random": random_summary,
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
    parser.add_argument("--dps", type=int, default=160)
    parser.add_argument("--u-points", type=int, default=400)
    parser.add_argument("--t-points", type=int, default=900)
    parser.add_argument("--random-points", type=int, default=200_000)
    parser.add_argument("--seed", type=int, default=20260829)
    return parser.parse_args()


if __name__ == "__main__":
    arguments = parse_args()
    initialize(arguments.dps)
    run(arguments)
