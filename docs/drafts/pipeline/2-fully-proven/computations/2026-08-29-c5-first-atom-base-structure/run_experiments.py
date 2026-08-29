#!/usr/bin/env python3
"""Structural and hostile test of the CLG exact first-atom base margin.

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
import sympy as sp


def initialize(dps: int) -> None:
    mp.mp.dps = dps


def base_margin(A_value: float, rho_value: float):
    """Return base margin, centre numerator, t, and z.

    `rho=lambda(A) z`; `0<rho<1/2` is exactly the structural factor chamber `r>1/2`.
    """
    A = mp.mpf(A_value)
    rho = mp.mpf(rho_value)
    lam = 3 * A / (A - mp.mpf(3) / 2) ** 2
    z = rho / lam
    t = mp.acosh(1 + z) / 2
    velocity = 2 * mp.sinh(2 * t)
    r = 1 - rho
    d = -6 * A * (A + mp.mpf(3) / 2) / (A - mp.mpf(3) / 2) ** 3
    slope = 2 * A + lam / r
    curvature = lam**2 / r**2
    cubic = lam**3 / r**3
    a = slope * velocity
    b = 4 * curvature * z * (z + 2) + 4 * slope * (z + 1)
    c = velocity * (8 * cubic * z * (z + 2) + 12 * curvature * (z + 1) + 4 * slope)
    centre = 4 * A * z + d * z / r
    mixed_one = (4 * A + d / r**2) * velocity
    mixed_two = 4 * (2 * lam * d * z * (z + 2) / r**3
                     + (4 * A + d / r**2) * (z + 1))
    H = a * (t * mixed_one) - (a + t * b) * centre
    P = a * (t * mixed_one + t**2 * mixed_two) - (a + 3 * t * b + t**2 * c) * centre
    margin = 5 * P - (30 + 72 * z) * H
    return margin, H, t, z


def summarize(points):
    negative_margin = []
    nonnegative_H = []
    minimum_normalized = None
    minimum_point = None
    for A, rho in points:
        margin, H, t, z = base_margin(A, rho)
        if margin <= 0 and len(negative_margin) < 50:
            negative_margin.append([A, rho, mp.nstr(margin, 40)])
        if H >= 0 and len(nonnegative_H) < 50:
            nonnegative_H.append([A, rho, mp.nstr(H, 40)])
        normalized = margin / t**7
        if minimum_normalized is None or normalized < minimum_normalized:
            minimum_normalized = normalized
            minimum_point = [A, rho, mp.nstr(margin, 40), mp.nstr(H, 40),
                             mp.nstr(t, 30), mp.nstr(z, 30)]
    return {
        "count": len(points),
        "negative_margin": negative_margin,
        "nonnegative_center_numerator": nonnegative_H,
        "minimum_margin_over_t7": mp.nstr(minimum_normalized, 40),
        "minimum_point": minimum_point,
    }


def deterministic_worker(task):
    A, rho_values = task
    return summarize([(A, rho) for rho in rho_values])


def random_worker(task):
    seed, count, log_A_max = task
    generator = random.Random(seed)
    points = []
    for _ in range(count):
        log_A = generator.uniform(math.log(6), log_A_max)
        A = math.exp(log_A)
        draw = generator.random()
        if draw < 0.4:
            rho = 10 ** generator.uniform(-12, math.log10(0.499999999))
        elif draw < 0.7:
            rho = 0.5 - 10 ** generator.uniform(-12, math.log10(0.49))
        else:
            rho = generator.uniform(1e-12, 0.499999999999)
        points.append((A, rho))
    return summarize(points)


def merge(records):
    smallest = min(records, key=lambda record: mp.mpf(record["minimum_margin_over_t7"]))
    return {
        "count": sum(record["count"] for record in records),
        "negative_margin": [item for record in records
                            for item in record["negative_margin"]][:50],
        "nonnegative_center_numerator": [item for record in records
                                         for item in record["nonnegative_center_numerator"]][:50],
        "minimum_margin_over_t7": smallest["minimum_margin_over_t7"],
        "minimum_point": smallest["minimum_point"],
    }


def series_add(left, right):
    return [a + b for a, b in zip(left, right)]


def series_scale(c, value):
    return [c * a for a in value]


def series_mul(left, right):
    return [sum(left[j] * right[i - j] for j in range(i + 1))
            for i in range(len(left))]


def series_inv(value):
    result = [sp.Rational(0)] * len(value)
    result[0] = 1 / value[0]
    for i in range(1, len(value)):
        result[i] = -sum(value[j] * result[i - j] for j in range(1, i + 1)) / value[0]
    return result


def exact_seam_coefficient(A: sp.Symbol):
    order = 9
    one = [sp.Rational(0)] * order
    time_series = [sp.Rational(0)] * order
    z = [sp.Rational(0)] * order
    velocity = [sp.Rational(0)] * order
    one[0] = 1
    time_series[1] = 1
    for j in range(1, 5):
        if 2 * j < order:
            z[2 * j] = sp.Rational(2) ** (2 * j) / sp.factorial(2 * j)
    for j in range(4):
        if 2 * j + 1 < order:
            velocity[2 * j + 1] = (
                2 * sp.Rational(2) ** (2 * j + 1) / sp.factorial(2 * j + 1)
            )
    const = lambda c: series_scale(c, one)
    neg = lambda value: series_scale(-1, value)
    lam = 3 * A / (A - sp.Rational(3, 2)) ** 2
    d = -6 * A * (A + sp.Rational(3, 2)) / (A - sp.Rational(3, 2)) ** 3
    r = series_add(one, neg(series_scale(lam, z)))
    rinv = series_inv(r)
    rinv2 = series_mul(rinv, rinv)
    rinv3 = series_mul(rinv2, rinv)
    slope = series_add(const(2 * A), series_scale(lam, rinv))
    curvature = series_scale(lam**2, rinv2)
    cubic = series_scale(lam**3, rinv3)
    zp1 = series_add(z, one)
    zp2 = series_add(z, const(2))
    a = series_mul(slope, velocity)
    b = series_scale(4, series_add(series_mul(series_mul(curvature, z), zp2),
                                   series_mul(slope, zp1)))
    c = series_mul(velocity, series_add(
        series_add(series_scale(8, series_mul(series_mul(cubic, z), zp2)),
                   series_scale(12, series_mul(curvature, zp1))),
        series_scale(4, slope)))
    centre = series_mul(z, series_add(const(4 * A), series_scale(d, rinv)))
    mixed_one = series_mul(series_add(const(4 * A), series_scale(d, rinv2)), velocity)
    mixed_two = series_scale(4, series_add(
        series_scale(2 * lam * d, series_mul(series_mul(z, zp2), rinv3)),
        series_mul(series_add(const(4 * A), series_scale(d, rinv2)), zp1)))
    H = series_add(
        series_mul(series_mul(a, time_series), mixed_one),
        neg(series_mul(series_add(a, series_mul(time_series, b)), centre)))
    t2 = series_mul(time_series, time_series)
    P = series_add(
        series_mul(a, series_add(series_mul(time_series, mixed_one),
                                 series_mul(t2, mixed_two))),
        neg(series_mul(series_add(series_add(a, series_scale(3, series_mul(time_series, b))),
                                  series_mul(t2, c)), centre)))
    base = series_add(series_scale(5, P),
                      neg(series_mul(series_add(const(30), series_scale(72, z)), H)))
    simplified = [(index, sp.factor(sp.cancel(value)))
                  for index, value in enumerate(base)]
    nonzero = [(index, value) for index, value in simplified if value != 0]
    assert nonzero and nonzero[0][0] == 7
    return nonzero[0][1]


def exact_structure():
    A, z, t, velocity = sp.symbols("A z t velocity")
    lam = 3 * A / (A - sp.Rational(3, 2)) ** 2
    d = -6 * A * (A + sp.Rational(3, 2)) / (A - sp.Rational(3, 2)) ** 3
    r = 1 - lam * z
    slope = 2 * A + lam / r
    curvature = lam**2 / r**2
    cubic = lam**3 / r**3
    a = slope * velocity
    b = 4 * curvature * z * (z + 2) + 4 * slope * (z + 1)
    c = velocity * (8 * cubic * z * (z + 2) + 12 * curvature * (z + 1) + 4 * slope)
    centre = 4 * A * z + d * z / r
    mixed_one = (4 * A + d / r**2) * velocity
    mixed_two = 4 * (2 * lam * d * z * (z + 2) / r**3
                     + (4 * A + d / r**2) * (z + 1))
    H = a * t * mixed_one - (a + t * b) * centre
    P = a * (t * mixed_one + t**2 * mixed_two) - (a + 3 * t * b + t**2 * c) * centre
    base = sp.cancel(5 * P - (30 + 72 * z) * H)
    numerator, denominator = sp.fraction(base)
    reduced = sp.rem(sp.Poly(numerator, velocity),
                     sp.Poly(velocity**2 - 4 * z * (z + 2), velocity)).as_expr()
    common = sp.factor(sp.gcd_list(sp.Poly(reduced, A, z, t, velocity).coeffs()))
    reduced = sp.expand(reduced / common)
    reduced_poly = sp.Poly(reduced, velocity, t)
    P0 = sp.factor(reduced_poly.coeff_monomial(velocity))
    P2 = sp.factor(reduced_poly.coeff_monomial(velocity * t**2))
    Q0 = sp.factor(reduced_poly.coeff_monomial(t))
    expected_P0 = sp.factor(
        z * (72 * z + 25) * A**2
        * (-4 * A**2 + 12 * A * z + 12 * A - 15)
        * (-4 * A**2 + 12 * A * z + 12 * A - 9)
        * (-8 * A**3 + 24 * A**2 * z + 36 * A**2 - 36 * A * z - 42 * A + 45)
    )
    rho = sp.Symbol("rho")
    z_rho = rho * (2 * A - 3)**2 / (12 * A)
    P2_core = sp.factor(P2 / (20 * A**2))
    witnesses = {
        "negative_at_A6_rho1_4": str(sp.factor(P2_core.subs({A: 6, z: z_rho.subs({A: 6, rho: sp.Rational(1, 4)})}))),
        "positive_at_A6_rho49_100": str(sp.factor(P2_core.subs({A: 6, z: z_rho.subs({A: 6, rho: sp.Rational(49, 100)})}))),
    }
    seam = exact_seam_coefficient(A)
    seam_num, seam_den = sp.fraction(seam)
    seam_poly = sp.factor(seam_num / (4096 * A**2))
    x = sp.Symbol("x")
    shifted = sp.Poly(sp.expand(seam_poly.subs(A, x + 6)), x, domain=sp.QQ)
    return {
        "reduced_identity": "numerator = common*(velocity*(P0+t^2*P2)+t*Q0)",
        "common": str(common),
        "denominator": str(sp.factor(denominator)),
        "P0_factor": str(P0),
        "P0_factor_identity_exact": bool(sp.expand(P0 - expected_P0) == 0),
        "P2_mixed_sign_exact_witnesses": witnesses,
        "P2_mixed_sign": bool(
            sp.Rational(witnesses["negative_at_A6_rho1_4"]) < 0
            and sp.Rational(witnesses["positive_at_A6_rho49_100"]) > 0
        ),
        "P0_terms": len(sp.Poly(P0, A, z).terms()),
        "P2_terms": len(sp.Poly(P2, A, z).terms()),
        "Q0_terms": len(sp.Poly(Q0, A, z).terms()),
        "seam_first_nonzero_order": 7,
        "seam_coefficient": str(seam),
        "seam_polynomial": str(seam_poly),
        "seam_polynomial_shift_A6_coefficients_descending": [str(c) for c in shifted.all_coeffs()],
        "seam_polynomial_shift_A6_all_positive": all(c > 0 for c in shifted.all_coeffs()),
        "seam_denominator": str(seam_den),
    }


def run(args):
    started = time.time()
    structure = exact_structure()
    log_A_max = math.log(math.pi) + args.max_u * 2
    A_values = np.geomspace(6, math.exp(log_A_max), args.A_points)
    rho_values = np.unique(np.concatenate((
        np.geomspace(1e-12, 1e-2, max(64, args.rho_points // 3)),
        np.linspace(1e-2, 0.49, args.rho_points),
        0.5 - np.geomspace(1e-12, 1e-2, max(64, args.rho_points // 3)),
    )))
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        deterministic = merge(list(pool.imap_unordered(
            deterministic_worker,
            [(float(A), [float(rho) for rho in rho_values]) for A in A_values],
            chunksize=1)))
    chunk = max(100, math.ceil(args.random_points / (args.workers * 4)))
    tasks = []
    remaining = args.random_points
    seed = args.seed
    while remaining:
        count = min(chunk, remaining)
        tasks.append((seed, count, log_A_max))
        seed += 1
        remaining -= count
    with Pool(args.workers, initializer=initialize, initargs=(args.dps,)) as pool:
        randomized = merge(list(pool.imap_unordered(random_worker, tasks, chunksize=1)))
    result = {
        "scope": "diagnostic only; forbidden as Lean input",
        "question": "does the exact first-atom rational-hyperbolic base margin fail on A>=6, r>1/2?",
        "parameters": {**vars(args), "output": str(args.output)},
        "domain": "A>=6, 0<rho=lambda(A)z<1/2; larger than physical t<=u chamber",
        "structure": structure,
        "deterministic": deterministic,
        "randomized": randomized,
        "environment": {
            "python": platform.python_version(),
            "workers": args.workers,
            "mpmath": mp.__version__,
            "numpy": np.__version__,
            "sympy": sp.__version__,
        },
        "elapsed_seconds": time.time() - started,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    parser.add_argument("--workers", type=int, default=min(128, os.cpu_count() or 1))
    parser.add_argument("--dps", type=int, default=100)
    parser.add_argument("--A-points", type=int, default=192)
    parser.add_argument("--rho-points", type=int, default=640)
    parser.add_argument("--random-points", type=int, default=200000)
    parser.add_argument("--max-u", type=float, default=20.0)
    parser.add_argument("--seed", type=int, default=20260829)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
