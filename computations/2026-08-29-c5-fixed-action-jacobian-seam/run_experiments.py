#!/usr/bin/env python3
"""Hostile seam test for the direct fixed-action C5 Jacobian.

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
import sympy as sp


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
        derivative_polynomials(mp.mpf(9) / 2, 4),
        derivative_polynomials(mp.mpf(5) / 2, 4),
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
    if sign < 0:
        result[1] = -result[1]
        result[3] = -result[3]
    return result


def log_jets_four(x: mp.mpf):
    f0, f1, f2, f3, f4 = source_derivatives(x)
    first = f1 / f0
    second = f2 / f0 - first**2
    third = f3 / f0 - 3 * f2 * f1 / f0**2 + 2 * first**3
    fourth = f4 / f0 - 4 * f3 * f1 / f0**2 - 3 * (f2 / f0) ** 2
    fourth += 12 * f2 * f1**2 / f0**3 - 6 * first**4
    return mp.log(f0), first, second, third, fourth


def seam_margin(t, centre=None):
    """Return exact scalar formula for d/du J(0,t).

    If q is reflected log action and F(t,q,q_t,q_tt) is direct C5 balance,
    reflection makes all first centre derivatives vanish at u=0. Hence

      J_u(0,t) = q_t (F_a q_tuu + F_b q_ttuu)
                   - q_uu (F_t + F_a q_tt + F_b q_ttt).

    The F_q terms cancel identically.
    """
    t = mp.mpf(t)
    lc0, _, lc2, _, _ = centre if centre is not None else log_jets_four(mp.mpf(0))
    l0, l1, l2, l3, l4 = log_jets_four(t)
    q = 2 * (lc0 - l0)
    a = -2 * l1
    b = -2 * l2
    c = -2 * l3
    d = 2 * (lc2 - l2)
    e = -2 * l4
    inverse_r = 1 / mp.expm1(q)
    f_a = -mp.mpf(9) / 4 * t * inverse_r
    f_a -= mp.mpf(5) / 2 * t**2 * a * inverse_r
    f_a -= 2 * t**2 * a * inverse_r**2
    f_b = mp.mpf(5) / 4 * t**2 * inverse_r
    f_t = -mp.mpf(9) / 4 * a * inverse_r
    f_t += mp.mpf(5) / 2 * t * (b - a**2) * inverse_r
    f_t -= 2 * t * a**2 * inverse_r**2
    margin = a * (f_a * c + f_b * e) - d * (f_t + f_a * b + f_b * c)
    return q, margin


def fixed_action_jacobian(u, t):
    u, t = mp.mpf(u), mp.mpf(t)
    lc0, lc1, _, _, _ = log_jets_four(u)
    lp0, lp1, lp2, lp3, _ = log_jets_four(u + t)
    lm0, lm1, lm2, lm3, _ = log_jets_four(u - t)
    q = 2 * lc0 - lp0 - lm0
    q_u = 2 * lc1 - lp1 - lm1
    q_t = lm1 - lp1
    q_tt = -lp2 - lm2
    q_tu = lm2 - lp2
    q_ttu = -(lp3 + lm3)
    q_ttt = lm3 - lp3
    inverse_r = 1 / mp.expm1(q)
    f_q_raw = -mp.mpf(9) / 4 * t * q_t
    f_q_raw += mp.mpf(5) / 4 * t**2 * (q_tt - q_t**2)
    f_q_raw -= 2 * t**2 * q_t**2 * inverse_r
    f_q = f_q_raw * (-inverse_r - inverse_r**2)
    f_t = -mp.mpf(9) / 4 * q_t * inverse_r
    f_t += mp.mpf(5) / 2 * t * (q_tt - q_t**2) * inverse_r
    f_t -= 2 * t * q_t**2 * inverse_r**2
    f_a = -mp.mpf(9) / 4 * t * inverse_r
    f_a -= mp.mpf(5) / 2 * t**2 * q_t * inverse_r
    f_a -= 2 * t**2 * q_t * inverse_r**2
    f_b = mp.mpf(5) / 4 * t**2 * inverse_r
    f_u = f_q * q_u + f_a * q_tu + f_b * q_ttu
    f_total_t = f_t + f_q * q_t + f_a * q_tt + f_b * q_ttt
    return f_u * q_t - f_total_t * q_u


def symbolic_seam_series(order: int):
    """Exact abstract even-log-jet expansion; no theta numerical values."""
    t = sp.symbols("t")
    jets = {n: sp.symbols(f"L{n}") for n in range(0, order + 5, 2)}
    ell = sum(jets[n] * t**n / sp.factorial(n) for n in jets)
    q = 2 * (jets[0] - ell)
    a = sp.diff(q, t)
    b = sp.diff(q, t, 2)
    c = sp.diff(q, t, 3)
    d = 2 * (jets[2] - sp.diff(ell, t, 2))
    e = -2 * sp.diff(ell, t, 4)
    inv_r = sp.series(1 / (sp.exp(q) - 1), t, 0, order + 7).removeO()
    f_a = -sp.Rational(9, 4) * t * inv_r
    f_a -= sp.Rational(5, 2) * t**2 * a * inv_r
    f_a -= 2 * t**2 * a * inv_r**2
    f_b = sp.Rational(5, 4) * t**2 * inv_r
    f_t = -sp.Rational(9, 4) * a * inv_r
    f_t += sp.Rational(5, 2) * t * (b - a**2) * inv_r
    f_t -= 2 * t * a**2 * inv_r**2
    margin = a * (f_a * c + f_b * e) - d * (f_t + f_a * b + f_b * c)
    series = sp.series(margin, t, 0, order + 1).removeO().expand()
    coefficients = {}
    for power in range(order + 1):
        coefficient = sp.factor(series.coeff(t, power))
        if coefficient != 0:
            coefficients[str(power)] = str(coefficient)
    return {"order": order, "nonzero_coefficients": coefficients}


def chunk_worker(values):
    centre = log_jets_four(mp.mpf(0))
    counts = {-1: 0, 0: 0, 1: 0}
    first_negative = []
    smallest = None
    for raw_t in values:
        q, margin = seam_margin(raw_t, centre)
        sign = int(mp.sign(margin))
        counts[sign] += 1
        if sign < 0 and len(first_negative) < 50:
            first_negative.append({
                "t": float(raw_t),
                "q": mp.nstr(q, 40),
                "margin": mp.nstr(margin, 40),
            })
        if margin:
            log_abs = mp.log10(abs(margin))
            if smallest is None or log_abs < smallest[0]:
                smallest = (log_abs, raw_t, sign, margin)
    return {
        "count": len(values),
        "negative_count": counts[-1],
        "zero_count": counts[0],
        "positive_count": counts[1],
        "negative_first_50": first_negative,
        "smallest": None if smallest is None else {
            "log10_abs": mp.nstr(smallest[0], 40),
            "t": float(smallest[1]),
            "sign": smallest[2],
            "margin": mp.nstr(smallest[3], 40),
        },
    }


def merge(records):
    nonempty = [record for record in records if record["smallest"] is not None]
    smallest = min(nonempty, key=lambda record: mp.mpf(record["smallest"]["log10_abs"]))
    return {
        "count": sum(record["count"] for record in records),
        "negative_count": sum(record["negative_count"] for record in records),
        "zero_count": sum(record["zero_count"] for record in records),
        "positive_count": sum(record["positive_count"] for record in records),
        "negative_first_50": [
            item for record in records for item in record["negative_first_50"]
        ][:50],
        "smallest": smallest["smallest"],
    }


def precision_checkpoints(dps_values):
    test_t = ["1e-8", "1e-6", "1e-4", "0.01", "0.1", "0.5", "1", "2", "5", "10", "50", "100"]
    records = []
    for dps in dps_values:
        initialize(dps)
        centre = log_jets_four(mp.mpf(0))
        values = []
        for raw_t in test_t:
            _, margin = seam_margin(raw_t, centre)
            values.append({"t": raw_t, "sign": int(mp.sign(margin)), "margin": mp.nstr(margin, 50)})
        records.append({"dps": dps, "values": values})
    return records


def derivative_consistency(dps: int):
    initialize(dps)
    records = []
    for raw_t in ["1e-4", "0.01", "0.1", "0.5", "1", "2", "5"]:
        _, margin = seam_margin(raw_t)
        ratios = []
        for raw_u in ["1e-6", "1e-10", "1e-14", "1e-18"]:
            u = mp.mpf(raw_u)
            ratio = fixed_action_jacobian(u, raw_t) / u
            ratios.append({
                "u": raw_u,
                "ratio": mp.nstr(ratio, 50),
                "relative_error": mp.nstr(abs(ratio / margin - 1), 20),
            })
        records.append({"t": raw_t, "seam_margin": mp.nstr(margin, 50), "ratios": ratios})
    return records


def shape_attack(dps: int):
    """Try to kill monotonicity of the desingularized Jacobian in centre."""
    initialize(dps)
    test_t = ["0.001", "0.01", "0.1", "0.5", "1", "2", "5"]
    test_u = ["1e-6", "0.001", "0.01", "0.1", "0.5", "1", "2", "5", "10"]
    records = []
    for raw_t in test_t:
        _, margin = seam_margin(raw_t)
        values = []
        for raw_u in test_u:
            u = mp.mpf(raw_u)
            quotient = fixed_action_jacobian(u, raw_t) / u
            values.append({
                "u": raw_u,
                "quotient": mp.nstr(quotient, 40),
                "quotient_over_seam": mp.nstr(quotient / margin, 40),
            })
        increasing_violations = []
        decreasing_violations = []
        for left, right in zip(values, values[1:]):
            left_value = mp.mpf(left["quotient"])
            right_value = mp.mpf(right["quotient"])
            if right_value < left_value:
                increasing_violations.append([left["u"], right["u"]])
            if left_value < right_value:
                decreasing_violations.append([left["u"], right["u"]])
        records.append({
            "t": raw_t,
            "seam_margin": mp.nstr(margin, 40),
            "values": values,
            "nondecreasing_violations": increasing_violations,
            "nonincreasing_violations": decreasing_violations,
        })
    return records


def run(args):
    started = time.time()
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    symbolic = symbolic_seam_series(args.series_order)
    checkpoint_dps = sorted(set([80, 160, args.dps, 2 * args.dps]))
    checkpoints = precision_checkpoints(checkpoint_dps)
    consistency = derivative_consistency(args.dps)
    shape = shape_attack(args.dps)
    initialize(args.dps)
    grid = np.unique(np.concatenate((
        np.geomspace(1e-8, 1e-2, max(1000, args.points // 5)),
        np.geomspace(1e-2, 100.0, args.points),
        np.linspace(1e-4, 8.0, max(1000, args.points // 3)),
    )))
    generator = random.Random(args.seed)
    random_values = np.array([10 ** generator.uniform(-8, 2) for _ in range(args.random_points)])
    values = np.unique(np.concatenate((grid, random_values)))
    chunk_size = max(100, math.ceil(len(values) / (args.workers * 8)))
    tasks = [[float(value) for value in values[i:i + chunk_size]]
             for i in range(0, len(values), chunk_size)]
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        summary = merge(list(pool.imap_unordered(chunk_worker, tasks, chunksize=1)))
    result = {
        "scope": "diagnostic only; forbidden as input to Lean proofs",
        "parameters": vars(args),
        "symbolic_seam_series": symbolic,
        "precision_checkpoints": checkpoints,
        "derivative_consistency": consistency,
        "desingularized_shape_attack": shape,
        "scan": summary,
        "environment": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "workers": args.workers,
            "mpmath": mp.__version__,
            "numpy": np.__version__,
            "sympy": sp.__version__,
        },
        "elapsed_seconds": time.time() - started,
    }
    (output / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="results")
    parser.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=240)
    parser.add_argument("--points", type=int, default=250_000)
    parser.add_argument("--random-points", type=int, default=250_000)
    parser.add_argument("--series-order", type=int, default=6)
    parser.add_argument("--seed", type=int, default=20260829)
    return parser.parse_args()


if __name__ == "__main__":
    arguments = parse_args()
    initialize(arguments.dps)
    run(arguments)
