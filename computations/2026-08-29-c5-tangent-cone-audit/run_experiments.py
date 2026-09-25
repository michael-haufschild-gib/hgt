#!/usr/bin/env python3
"""Audit whether the current formal likelihood cone forces the CLG tangent reserve.

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


POLYNOMIALS = None
CAP = mp.mpf(13) / 5


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
    global POLYNOMIALS, CAP
    mp.mp.dps = dps
    CAP = mp.mpf(13) / 5
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
    return (q, a, b, c, s, m, n), A


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


def margin_and_derivative(atom, likelihood, t):
    q, a, b, c, s, m, n = atom
    dq, da, db, dc, ds, dm, dn = likelihood
    r = mp.expm1(q)
    eq = mp.exp(q)
    v = t * a
    H = a * t * m - (a + t * b) * s
    P = a * (t * m + t**2 * n) - (a + 3 * t * b + t**2 * c) * s
    W = 14 + 10 * v + 8 * v / r
    dH = da * t * m + a * t * dm - (da + t * db) * s - (a + t * b) * ds
    dP = (da * (t * m + t**2 * n) + a * (t * dm + t**2 * dn)
          - (da + 3 * t * db + t**2 * dc) * s
          - (a + 3 * t * b + t**2 * c) * ds)
    dW = 10 * t * da + 8 * (t * da / r - v * eq * dq / r**2)
    margin = 5 * P - W * H
    derivative = 5 * dP - dW * H - W * dH
    return margin, derivative, H, W


def tangent_coefficients(atom, t):
    q, a, b, c, s, m, n = atom
    r = mp.expm1(q)
    eq = mp.exp(q)
    v = t * a
    H = a * t * m - (a + t * b) * s
    W = 14 + 10 * v + 8 * v / r
    k_da = t * (10 + 8 / r)
    k_dq = -8 * v * eq / r**2
    return {
        "dq": -k_dq * H,
        "da": 5 * (t * m + t**2 * n - s) - k_da * H - W * (t * m - s),
        "db": t * s * (W - 15),
        "dc": -5 * t**2 * s,
        "ds": W * (a + t * b) - 5 * (a + 3 * t * b + t**2 * c),
        "dm": a * t * (5 - W),
        "dn": 5 * a * t**2,
    }


def cone_vertices(coefficients, t):
    ca = coefficients["da"]
    cb = coefficients["db"]
    cs = coefficients["ds"]
    cm = coefficients["dm"]
    # Normalize y = -db to one. Formal closure constraints are
    # 0 <= x=-da <= t*y, 0 <= dm <= y, 0 <= ds <= min(x,t*dm).
    return {
        "zero": mp.mpf(0),
        "y_only": -cb,
        "y_dm": -cb + cm,
        "y_da": -cb - t * ca,
        "y_da_dm": -cb - t * ca + cm,
        "y_da_dm_ds": -cb - t * ca + cm + t * cs,
    }


def safe_float(x):
    if not mp.isfinite(x):
        return math.copysign(math.inf, float(mp.sign(x)))
    return float(x)


def point_record(u_value, tau_value):
    u = mp.mpf(u_value)
    tau = mp.mpf(tau_value)
    t = u * tau
    atom, A = atom_jets(u, t)
    full = full_jets(u, t)
    likelihood = tuple(full[i] - atom[i] for i in range(7))
    margin, derivative, H, W = margin_and_derivative(atom, likelihood, t)
    coefficients = tangent_coefficients(atom, t)
    derivative_linear = sum(coefficients[name] * value for name, value in zip(
        ("dq", "da", "db", "dc", "ds", "dm", "dn"), likelihood))
    vertices = cone_vertices(coefficients, t)
    label, unit_min = min(vertices.items(), key=lambda item: item[1])
    unit_min = min(mp.mpf(0), unit_min)
    cone_lower = margin + 5 * CAP * unit_min
    actual_y = -likelihood[2]
    actual_adversarial = margin + 5 * actual_y * unit_min
    actual_tangent = margin + 5 * derivative
    required_cap = mp.inf if unit_min >= 0 else margin / (-5 * unit_min)
    channel_scales = tuple(max(mp.mpf(1), abs(atom[i]), abs(full[i])) for i in range(7))
    h_scale = max(mp.mpf(1), abs(atom[1] * t * atom[5]),
                  abs((atom[1] + t * atom[2]) * atom[4]))
    derivative_scale = max(mp.mpf(1), abs(derivative),
                           sum(abs(coefficients[name] * value) for name, value in zip(
                               ("dq", "da", "db", "dc", "ds", "dm", "dn"), likelihood)))
    return {
        "u": u,
        "tau": tau,
        "t": t,
        "A": A,
        "margin": margin,
        "H": H,
        "W": W,
        "likelihood": likelihood,
        "coefficients": coefficients,
        "derivative_error": derivative - derivative_linear,
        "vertex": label,
        "unit_min": unit_min,
        "cone_lower": cone_lower,
        "actual_y": actual_y,
        "actual_adversarial": actual_adversarial,
        "actual_tangent": actual_tangent,
        "required_cap": required_cap,
        "channel_scales": channel_scales,
        "h_scale": h_scale,
        "derivative_scale": derivative_scale,
    }


def printable(record):
    contribution_names = ("dq", "da", "db", "dc", "ds", "dm", "dn")
    return {
        "u": mp.nstr(record["u"], 35),
        "tau": mp.nstr(record["tau"], 35),
        "t": mp.nstr(record["t"], 35),
        "A": mp.nstr(record["A"], 35),
        "vertex": record["vertex"],
        "margin": mp.nstr(record["margin"], 35),
        "unit_min": mp.nstr(record["unit_min"], 35),
        "cone_lower": mp.nstr(record["cone_lower"], 35),
        "actual_y": mp.nstr(record["actual_y"], 35),
        "actual_adversarial": mp.nstr(record["actual_adversarial"], 35),
        "actual_tangent": mp.nstr(record["actual_tangent"], 35),
        "required_cap": mp.nstr(record["required_cap"], 35),
        "current_cap_over_required": mp.nstr(CAP / record["required_cap"], 35),
        "actual_y_over_required": mp.nstr(record["actual_y"] / record["required_cap"], 35),
        "H": mp.nstr(record["H"], 35),
        "coefficients": {key: mp.nstr(value, 35)
                         for key, value in record["coefficients"].items()},
        "likelihood": [mp.nstr(value, 35) for value in record["likelihood"]],
        "channel_contributions": {
            name: mp.nstr(record["coefficients"][name] * value, 35)
            for name, value in zip(contribution_names, record["likelihood"])
        },
        "derivative_error": mp.nstr(record["derivative_error"], 20),
    }


def empty_summary():
    return {
        "count": 0,
        "cone_failures": 0,
        "actual_adversarial_failures": 0,
        "actual_tangent_failures": 0,
        "sign_failures": 0,
        "vertex_counts": {},
        "min_cone_ratio": None,
        "max_cap_ratio": None,
        "max_actual_y_ratio": None,
        "min_actual_adversarial_ratio": None,
        "min_actual_tangent_ratio": None,
    }


def consider(summary, record):
    summary["count"] += 1
    if record["cone_lower"] <= 0:
        summary["cone_failures"] += 1
    if record["actual_adversarial"] <= 0:
        summary["actual_adversarial_failures"] += 1
    if record["actual_tangent"] <= 0:
        summary["actual_tangent_failures"] += 1
    likelihood = record["likelihood"]
    coefficients = record["coefficients"]
    # Full-minus-atom channels can lose roughly half the working digits at large scale.
    # One-third-DPS relative tolerance classifies those cancellation-level residues only.
    resolution = mp.power(10, -mp.mp.dps / 3)
    scales = record["channel_scales"]
    # At large u the higher atoms lie below working precision, so exact zeros are accepted.
    # Only a wrong sign larger than the precision floor is a failure.
    good_signs = (
        record["H"] <= resolution * record["h_scale"] and
        likelihood[0] <= resolution * scales[0] and
        likelihood[1] <= resolution * scales[1] and
        likelihood[2] <= resolution * scales[2] and
        likelihood[3] <= resolution * scales[3] and
        likelihood[4] >= -resolution * scales[4] and
        likelihood[5] >= -resolution * scales[5] and
        likelihood[6] >= -resolution * scales[6] and
        coefficients["dq"] <= resolution * max(1, abs(coefficients["dq"])) and
        coefficients["dc"] <= resolution * max(1, abs(coefficients["dc"])) and
        coefficients["dn"] >= -resolution * max(1, abs(coefficients["dn"])) and
        abs(record["derivative_error"]) <= resolution * record["derivative_scale"]
    )
    if not good_signs:
        summary["sign_failures"] += 1
    label = record["vertex"]
    summary["vertex_counts"][label] = summary["vertex_counts"].get(label, 0) + 1
    metrics = {
        "min_cone_ratio": record["cone_lower"] / record["margin"],
        "max_cap_ratio": CAP / record["required_cap"],
        "max_actual_y_ratio": record["actual_y"] / record["required_cap"],
        "min_actual_adversarial_ratio": record["actual_adversarial"] / record["margin"],
        "min_actual_tangent_ratio": record["actual_tangent"] / record["margin"],
    }
    for key, value in metrics.items():
        current = summary[key]
        choose = current is None or (key.startswith("max_") and value > current[0]) or (
            key.startswith("min_") and value < current[0])
        if choose:
            summary[key] = (value, printable(record))


def merge(left, right):
    left["count"] += right["count"]
    for key in ("cone_failures", "actual_adversarial_failures", "actual_tangent_failures",
                "sign_failures"):
        left[key] += right[key]
    for label, count in right["vertex_counts"].items():
        left["vertex_counts"][label] = left["vertex_counts"].get(label, 0) + count
    for key in ("min_cone_ratio", "max_cap_ratio", "max_actual_y_ratio",
                "min_actual_adversarial_ratio", "min_actual_tangent_ratio"):
        candidate = right[key]
        if candidate is None:
            continue
        current = left[key]
        if current is None or (key.startswith("max_") and candidate[0] > current[0]) or (
            key.startswith("min_") and candidate[0] < current[0]):
            left[key] = candidate
    return left


def deterministic_worker(task):
    u, tau_values = task
    summary = empty_summary()
    for tau in tau_values:
        consider(summary, point_record(u, tau))
    return summary


def random_worker(task):
    seed, count, u_min, u_max = task
    generator = random.Random(seed)
    summary = empty_summary()
    for _ in range(count):
        if generator.random() < 0.7:
            u = u_min + (u_max - u_min) * generator.random() ** 3
        else:
            u = generator.uniform(u_min, u_max)
        draw = generator.random()
        if draw < 0.35:
            tau = 10 ** generator.uniform(-8, 0)
        elif draw < 0.7:
            tau = 1 - 10 ** generator.uniform(-8, 0)
        else:
            tau = generator.uniform(1e-8, 1)
        consider(summary, point_record(u, tau))
    return summary


def enriched_values(low, high, count):
    values = {low, high}
    for i in range(count):
        x = i / max(1, count - 1)
        values.add(low + (high - low) * x)
        values.add(low + (high - low) * x**3)
        values.add(high - (high - low) * x**3)
    return sorted(values)


def tau_values(count):
    values = {1e-10, 1.0}
    for i in range(count):
        x = (i + 1) / count
        values.add(x)
        values.add(10 ** (-10 * (1 - x)))
        values.add(1 - 10 ** (-10 * (1 - x)))
    return sorted(value for value in values if 0 < value <= 1)


def serialize_summary(summary):
    result = dict(summary)
    for key in ("min_cone_ratio", "max_cap_ratio", "max_actual_y_ratio",
                "min_actual_adversarial_ratio", "min_actual_tangent_ratio"):
        value, record = result[key]
        result[key] = {"value": mp.nstr(value, 40), "point": record}
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=120)
    parser.add_argument("--u-points", type=int, default=120)
    parser.add_argument("--tau-points", type=int, default=180)
    parser.add_argument("--random-points", type=int, default=200000)
    parser.add_argument("--max-u", type=float, default=20.0)
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    args = parser.parse_args()
    initialize(args.dps)
    u_min = float(mp.log(mp.mpf(6) / mp.pi) / 2)
    us = enriched_values(u_min, args.max_u, args.u_points)
    taus = tau_values(args.tau_points)
    deterministic_tasks = [(u, taus) for u in us]
    base = args.random_points // args.workers
    remainder = args.random_points % args.workers
    random_tasks = [(2026082900 + i, base + (1 if i < remainder else 0), u_min, args.max_u)
                    for i in range(args.workers)]
    started = time.time()
    summary = empty_summary()
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        for partial in pool.imap_unordered(deterministic_worker, deterministic_tasks, chunksize=1):
            merge(summary, partial)
        for partial in pool.imap_unordered(random_worker, random_tasks, chunksize=1):
            merge(summary, partial)
    elapsed = time.time() - started
    payload = {
        "question": "Do current formal CLG likelihood inequalities force M(0)+5*M'(0)>=0?",
        "formal_cone": {
            "variables": "x=-da, y=-db, ds, dm; dq/dc/dn discarded as favorable",
            "constraints": [
                "0<=y<=13/5", "0<=x<=t*y", "0<=dm<=y",
                "0<=ds<=x", "0<=ds<=t*dm",
            ],
            "extreme_rays": ["zero", "y_only", "y_dm", "y_da", "y_da_dm",
                             "y_da_dm_ds"],
        },
        "parameters": vars(args) | {"output": str(args.output), "u_min": u_min,
                                     "deterministic_u_count": len(us),
                                     "deterministic_tau_count": len(taus)},
        "environment": {
            "platform": platform.platform(), "python": platform.python_version(),
            "cpu_count": os.cpu_count(), "mpmath": mp.__version__,
        },
        "elapsed_seconds": elapsed,
        "summary": serialize_summary(summary),
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"elapsed_seconds": elapsed, "count": summary["count"],
                      "cone_failures": summary["cone_failures"],
                      "actual_adversarial_failures": summary["actual_adversarial_failures"],
                      "actual_tangent_failures": summary["actual_tangent_failures"],
                      "sign_failures": summary["sign_failures"],
                      "vertex_counts": summary["vertex_counts"]}, sort_keys=True))


if __name__ == "__main__":
    main()
