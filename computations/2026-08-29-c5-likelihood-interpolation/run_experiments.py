#!/usr/bin/env python3
"""Hostile test of likelihood interpolation in fixed-action C5 compensation.

Diagnostic only. No output from this script may be imported into a Lean proof.
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


def source_derivatives(x: mp.mpf):
    sign = 1 if x >= 0 else -1
    x = abs(x)
    nmax = 1 if x >= 2 else 14
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


def atom_jets(u: mp.mpf, t: mp.mpf):
    A = mp.pi * mp.exp(2 * u)
    z = mp.cosh(2 * t) - 1
    zp = 2 * mp.sinh(2 * t)
    lam = 3 * A / (A - mp.mpf(3) / 2) ** 2
    r = 1 - lam * z
    d = -6 * A * (A + mp.mpf(3) / 2) / (A - mp.mpf(3) / 2) ** 3
    q = 2 * A * z - mp.log(r)
    slope = 2 * A + lam / r
    curvature = lam**2 / r**2
    cubic = lam**3 / r**3
    a = slope * zp
    b = 4 * curvature * z * (z + 2) + 4 * slope * (z + 1)
    c = zp * (8 * cubic * z * (z + 2) + 12 * curvature * (z + 1) + 4 * slope)
    s = 4 * A * z + d * z / r
    m = (4 * A + d / r**2) * zp
    n = 4 * (2 * lam * d * z * (z + 2) / r**3
             + (4 * A + d / r**2) * (z + 1))
    return q, a, b, c, s, m, n


def full_jets(u: mp.mpf, t: mp.mpf):
    l0, l1, _, _ = log_jets(u)
    lp0, lp1, lp2, lp3 = log_jets(u + t)
    lm0, lm1, lm2, lm3 = log_jets(u - t)
    return (
        2 * l0 - lp0 - lm0,
        lm1 - lp1,
        -lp2 - lm2,
        lm3 - lp3,
        2 * l1 - lp1 - lm1,
        lm2 - lp2,
        -lp3 - lm3,
    )


def margin_and_variations(jets, likelihood, t):
    q, a, b, c, s, m, n = jets
    dq, da, db, dc, ds, dm, dn = likelihood
    r = mp.expm1(q)
    eq = mp.exp(q)
    v = t * a
    dv = t * da
    H = a * t * m - (a + t * b) * s
    dH = da * t * m + a * t * dm - (da + t * db) * s - (a + t * b) * ds
    ddH = 2 * (da * t * dm - (da + t * db) * ds)
    P = a * (t * m + t**2 * n) - (a + 3 * t * b + t**2 * c) * s
    dP = (da * (t * m + t**2 * n) + a * (t * dm + t**2 * dn)
          - (da + 3 * t * db + t**2 * dc) * s
          - (a + 3 * t * b + t**2 * c) * ds)
    ddP = 2 * (da * (t * dm + t**2 * dn)
               - (da + 3 * t * db + t**2 * dc) * ds)
    inverse_r = 1 / r
    gprime = -eq * dq / r**2
    gsecond = eq * dq**2 * (eq + 1) / r**3
    W = 14 + 10 * v + 8 * v * inverse_r
    dW = 10 * dv + 8 * (dv * inverse_r + v * gprime)
    ddW = 8 * (2 * dv * gprime + v * gsecond)
    margin = 5 * P - W * H
    derivative = 5 * dP - dW * H - W * dH
    second = 5 * ddP - ddW * H - 2 * dW * dH - W * ddH
    return margin, derivative, second


def point_record(u_value, tau_value, lambda_values):
    u = mp.mpf(u_value)
    tau = mp.mpf(tau_value)
    t = u * tau
    atom = atom_jets(u, t)
    full = full_jets(u, t)
    likelihood = tuple(full[i] - atom[i] for i in range(7))
    samples = []
    for lam_value in lambda_values:
        lam = mp.mpf(lam_value)
        jets = tuple(atom[i] + lam * likelihood[i] for i in range(7))
        samples.append((lam, *margin_and_variations(jets, likelihood, t)))
    endpoints = [margin_and_variations(atom, likelihood, t)[0],
                 margin_and_variations(full, likelihood, t)[0]]
    return t, likelihood, endpoints, samples


def empty_summary():
    return {
        "count": 0,
        "negative_margin": [],
        "negative_derivative": 0,
        "positive_derivative": 0,
        "negative_second": 0,
        "positive_second": 0,
        "robust_negative_derivative": 0,
        "robust_positive_derivative": 0,
        "robust_negative_second": 0,
        "robust_positive_second": 0,
        "interior_below_both_endpoints": 0,
        "first_negative_derivative": [],
        "first_negative_second": [],
        "minimum_margin": None,
        "minimum_margin_point": None,
    }


def update(summary, u, tau, t, endpoints, sample):
    lam, margin, derivative, second = sample
    resolution = mp.power(10, -mp.mp.dps / 2)
    summary["count"] += 1
    if margin <= 0 and len(summary["negative_margin"]) < 50:
        summary["negative_margin"].append(
            [float(u), float(tau), float(lam), mp.nstr(margin, 40)])
    if derivative < 0:
        summary["negative_derivative"] += 1
        if len(summary["first_negative_derivative"]) < 50:
            summary["first_negative_derivative"].append(
                [float(u), float(tau), float(lam), mp.nstr(derivative, 40)])
    elif derivative > 0:
        summary["positive_derivative"] += 1
    if derivative < -resolution:
        summary["robust_negative_derivative"] += 1
    elif derivative > resolution:
        summary["robust_positive_derivative"] += 1
    if second < 0:
        summary["negative_second"] += 1
        if len(summary["first_negative_second"]) < 50:
            summary["first_negative_second"].append(
                [float(u), float(tau), float(lam), mp.nstr(second, 40)])
    elif second > 0:
        summary["positive_second"] += 1
    if second < -resolution:
        summary["robust_negative_second"] += 1
    elif second > resolution:
        summary["robust_positive_second"] += 1
    if 0 < lam < 1 and margin < min(endpoints):
        summary["interior_below_both_endpoints"] += 1
    if summary["minimum_margin"] is None or margin < mp.mpf(summary["minimum_margin"]):
        summary["minimum_margin"] = mp.nstr(margin, 40)
        summary["minimum_margin_point"] = [
            float(u), float(tau), float(lam), mp.nstr(t, 30),
            mp.nstr(derivative, 30), mp.nstr(second, 30),
        ]


def deterministic_worker(task):
    u, tau_values, lambda_values = task
    summary = empty_summary()
    for tau in tau_values:
        t, _, endpoints, samples = point_record(u, tau, lambda_values)
        for sample in samples:
            update(summary, u, tau, t, endpoints, sample)
    return summary


def random_worker(task):
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
            tau = 10 ** generator.uniform(-8, 0)
        elif draw < 0.7:
            tau = 1 - 10 ** generator.uniform(-8, 0)
        else:
            tau = generator.uniform(1e-8, 1)
        lam = generator.random()
        t, _, endpoints, samples = point_record(u, tau, [lam])
        update(summary, u, tau, t, endpoints, samples[0])
    return summary


def merge(records):
    result = empty_summary()
    for record in records:
        result["count"] += record["count"]
        for key in ("negative_derivative", "positive_derivative", "negative_second",
                    "positive_second", "robust_negative_derivative",
                    "robust_positive_derivative", "robust_negative_second",
                    "robust_positive_second", "interior_below_both_endpoints"):
            result[key] += record[key]
        for key in ("negative_margin", "first_negative_derivative", "first_negative_second"):
            result[key].extend(record[key])
            result[key] = result[key][:50]
        if (record["minimum_margin"] is not None
                and (result["minimum_margin"] is None
                     or mp.mpf(record["minimum_margin"]) < mp.mpf(result["minimum_margin"]))):
            result["minimum_margin"] = record["minimum_margin"]
            result["minimum_margin_point"] = record["minimum_margin_point"]
    return result


def run(args):
    started = time.time()
    u_min = float(mp.log(6 / mp.pi) / 2)
    u_values = np.unique(np.concatenate((
        np.geomspace(u_min, 2, max(32, args.u_points // 2)),
        np.linspace(u_min, 4, args.u_points),
        np.geomspace(4.01, args.max_u, max(32, args.u_points // 3)),
    )))
    tau_values = np.unique(np.concatenate((
        np.geomspace(1e-8, 1e-2, max(48, args.tau_points // 3)),
        np.linspace(1e-2, 0.99, args.tau_points),
        1 - np.geomspace(1e-8, 1e-2, max(48, args.tau_points // 3)),
        np.array([1.0]),
    )))
    lambda_values = np.linspace(0, 1, args.lambda_points)
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        deterministic = merge(list(pool.imap_unordered(
            deterministic_worker,
            [(float(u), [float(tau) for tau in tau_values],
              [float(lam) for lam in lambda_values]) for u in u_values],
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
        "question": "does first-atom-to-full likelihood interpolation preserve or monotonically improve C5 compensation?",
        "parameters": {**vars(args), "output": str(args.output)},
        "domain": "A=pi*exp(2u)>=6, 0<t<=u, 0<=lambda<=1",
        "interpolation": "q_lambda=q_first_atom+lambda*(q_full-q_first_atom)",
        "deterministic_grid_shape": [len(u_values), len(tau_values), len(lambda_values)],
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
    parser.add_argument("--dps", type=int, default=120)
    parser.add_argument("--u-points", type=int, default=128)
    parser.add_argument("--tau-points", type=int, default=220)
    parser.add_argument("--lambda-points", type=int, default=17)
    parser.add_argument("--random-points", type=int, default=100000)
    parser.add_argument("--max-u", type=float, default=20.0)
    parser.add_argument("--seed", type=int, default=20260829)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
