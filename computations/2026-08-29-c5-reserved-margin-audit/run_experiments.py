#!/usr/bin/env python3
"""Audit literal CLG lower/master/adaptive reserved margins on physical theta tail.

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


def compensation_margin(jets, t):
    q, a, b, c, s, m, n = jets
    r = mp.expm1(q)
    v = t * a
    H = a * t * m - (a + t * b) * s
    P = a * (t * m + t**2 * n) - (a + 3 * t * b + t**2 * c) * s
    W = 14 + 10 * v + 8 * v / r
    return 5 * P - W * H, H, P, W


def point_record(u_value, tau_value):
    u = mp.mpf(u_value)
    tau = mp.mpf(tau_value)
    t = u * tau
    atom = atom_jets(u, t)
    full = full_jets(u, t)
    likelihood = tuple(full[i] - atom[i] for i in range(7))
    full_margin, H, P, W = compensation_margin(full, t)
    _, a, _, _, s, _, _ = full
    _, _, db, dc, _, dm, dn = likelihood
    gain = 5 * t**2 * (a * dn - dc * s)
    lower = full_margin - gain
    y = -db
    master_reserve = 30 * t**2 * a * y
    master = lower + master_reserve
    hminus = (y + dm) / 2
    hplus = (y - dm) / 2
    Aminus = mp.pi * mp.exp(2 * (u - t))
    Aplus = mp.pi * mp.exp(2 * (u + t))
    adaptive_curvature = 2 * Aplus * hplus + 2 * Aminus * hminus
    adaptive_reserve = 5 * t**2 * a * adaptive_curvature
    adaptive = lower + adaptive_reserve
    return {
        "u": u, "tau": tau, "t": t, "A": mp.pi * mp.exp(2 * u),
        "full": full_margin, "lower": lower, "master": master, "adaptive": adaptive,
        "gain": gain, "master_reserve": master_reserve,
        "adaptive_reserve": adaptive_reserve, "adaptive_curvature": adaptive_curvature,
        "y": y, "dm": dm, "dc": dc, "dn": dn, "a": a, "s": s,
        "H": H, "P": P, "W": W,
        "identity_error": full_margin - (lower + gain),
    }


def printable(record):
    return {key: mp.nstr(value, 40) for key, value in record.items()}


def empty_summary():
    return {
        "count": 0,
        "robust_negative": {name: 0 for name in ("full", "lower", "master", "adaptive")},
        "robust_positive": {name: 0 for name in ("full", "lower", "master", "adaptive")},
        "minimum_ratio": {name: None for name in ("lower", "master", "adaptive")},
        "minimum_value": {name: None for name in ("full", "lower", "master", "adaptive")},
        "max_identity_relative_error": None,
        "negative_max_A": {name: None for name in ("lower", "master", "adaptive")},
        "minimum_gain_coefficient": {name: None for name in ("master", "adaptive")},
        "maximum_required_coefficient": {name: None for name in ("master", "adaptive")},
        "structural_failures": 0,
    }


def consider(summary, record):
    summary["count"] += 1
    scale = max(mp.mpf(1), abs(record["full"]), abs(record["lower"]), abs(record["gain"]))
    resolution = mp.power(10, -mp.mp.dps / 3) * scale
    structural = (
        record["gain"] > -resolution and record["master_reserve"] > -resolution and
        record["adaptive_reserve"] > -resolution and record["adaptive_curvature"] > -resolution and
        record["y"] > -resolution and record["dm"] > -resolution and
        record["dn"] > -resolution and record["dc"] < resolution and
        abs(record["identity_error"]) <= resolution
    )
    if not structural:
        summary["structural_failures"] += 1
    for name in ("full", "lower", "master", "adaptive"):
        value = record[name]
        if value < -resolution:
            summary["robust_negative"][name] += 1
            if name != "full":
                current_A = summary["negative_max_A"][name]
                if current_A is None or record["A"] > current_A[0]:
                    summary["negative_max_A"][name] = (record["A"], printable(record))
        elif value > resolution:
            summary["robust_positive"][name] += 1
        current = summary["minimum_value"][name]
        if current is None or value < current[0]:
            summary["minimum_value"][name] = (value, printable(record))
    if record["full"] != 0:
        for name in ("lower", "master", "adaptive"):
            value = record[name] / record["full"]
            current = summary["minimum_ratio"][name]
            if current is None or value < current[0]:
                summary["minimum_ratio"][name] = (value, printable(record))
    units = {
        "master": record["master_reserve"] / 30,
        "adaptive": record["adaptive_reserve"] / 5,
    }
    for name, unit in units.items():
        if unit > resolution:
            gain_coefficient = record["gain"] / unit
            current_gain = summary["minimum_gain_coefficient"][name]
            if current_gain is None or gain_coefficient < current_gain[0]:
                summary["minimum_gain_coefficient"][name] = (
                    gain_coefficient, printable(record))
            required = max(mp.mpf(0), -record["lower"]) / unit
            current_required = summary["maximum_required_coefficient"][name]
            if current_required is None or required > current_required[0]:
                summary["maximum_required_coefficient"][name] = (
                    required, printable(record))
    error = abs(record["identity_error"]) / scale
    current = summary["max_identity_relative_error"]
    if current is None or error > current[0]:
        summary["max_identity_relative_error"] = (error, printable(record))


def merge(left, right):
    left["count"] += right["count"]
    left["structural_failures"] += right["structural_failures"]
    for sign in ("robust_negative", "robust_positive"):
        for name, count in right[sign].items():
            left[sign][name] += count
    for category in ("minimum_value", "minimum_ratio"):
        for name, candidate in right[category].items():
            if candidate is None:
                continue
            current = left[category][name]
            if current is None or candidate[0] < current[0]:
                left[category][name] = candidate
    for category in ("negative_max_A", "minimum_gain_coefficient",
                     "maximum_required_coefficient"):
        for name, candidate in right[category].items():
            if candidate is None:
                continue
            current = left[category][name]
            take = current is None
            if category in ("negative_max_A", "maximum_required_coefficient"):
                take = take or candidate[0] > current[0]
            else:
                take = take or candidate[0] < current[0]
            if take:
                left[category][name] = candidate
    candidate = right["max_identity_relative_error"]
    current = left["max_identity_relative_error"]
    if current is None or candidate[0] > current[0]:
        left["max_identity_relative_error"] = candidate


def deterministic_worker(task):
    u, taus = task
    summary = empty_summary()
    for tau in taus:
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
            tau = 10 ** generator.uniform(-20, -1e-6)
        elif draw < 0.7:
            tau = 1 - 10 ** generator.uniform(-10, -1e-6)
        else:
            tau = generator.uniform(1e-10, 1 - 1e-10)
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
    values = {mp.mpf("1e-20"), mp.mpf(1) - mp.mpf("1e-20")}
    for i in range(count):
        x = mp.mpf(i + 1) / (count + 1)
        values.add(x)
        values.add(mp.power(10, -20 * (1 - x)))
        values.add(1 - mp.power(10, -20 * (1 - x)))
    return sorted(value for value in values if 0 < value < 1)


def serialize(summary):
    result = dict(summary)
    for category in ("minimum_value", "minimum_ratio", "negative_max_A",
                     "minimum_gain_coefficient", "maximum_required_coefficient"):
        result[category] = {
            name: {"value": mp.nstr(item[0], 40), "point": item[1]}
            for name, item in summary[category].items()
        }
    item = summary["max_identity_relative_error"]
    result["max_identity_relative_error"] = {
        "value": mp.nstr(item[0], 40), "point": item[1]
    }
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=120)
    parser.add_argument("--u-points", type=int, default=140)
    parser.add_argument("--tau-points", type=int, default=220)
    parser.add_argument("--random-points", type=int, default=240000)
    parser.add_argument("--max-u", type=float, default=20.0)
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    args = parser.parse_args()
    initialize(args.dps)
    u_min = float(mp.log(mp.mpf(6) / mp.pi) / 2)
    us = enriched_values(u_min, args.max_u, args.u_points)
    taus = tau_values(args.tau_points)
    deterministic_tasks = [(u, taus) for u in us]
    base, remainder = divmod(args.random_points, args.workers)
    random_tasks = [(2026082910 + i, base + (1 if i < remainder else 0), u_min, args.max_u)
                    for i in range(args.workers)]
    summary = empty_summary()
    started = time.time()
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        for partial in pool.imap_unordered(deterministic_worker, deterministic_tasks, chunksize=1):
            merge(summary, partial)
        for partial in pool.imap_unordered(random_worker, random_tasks, chunksize=1):
            merge(summary, partial)
    elapsed = time.time() - started
    payload = {
        "question": "Are literal CLG lower/master/adaptive reserved margins positive on A>=6, 0<t<u?",
        "definitions": {
            "lower": "full - 5*t^2*(completed_a*likelihood_dn - likelihood_dc*completed_s)",
            "master": "lower + 30*t^2*completed_a*(-likelihood_db)",
            "adaptive": "lower + 5*t^2*completed_a*(2*Aplus*hplus+2*Aminus*hminus)",
        },
        "parameters": vars(args) | {"output": str(args.output), "u_min": u_min,
                                     "deterministic_u_count": len(us),
                                     "deterministic_tau_count": len(taus)},
        "environment": {"platform": platform.platform(), "python": platform.python_version(),
                        "cpu_count": os.cpu_count(), "mpmath": mp.__version__},
        "elapsed_seconds": elapsed,
        "summary": serialize(summary),
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"elapsed_seconds": elapsed, "count": summary["count"],
                      "robust_negative": summary["robust_negative"],
                      "robust_positive": summary["robust_positive"],
                      "structural_failures": summary["structural_failures"]}, sort_keys=True))


if __name__ == "__main__":
    main()
