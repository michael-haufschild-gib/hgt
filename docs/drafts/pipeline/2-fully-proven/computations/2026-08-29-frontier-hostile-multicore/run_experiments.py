#!/usr/bin/env python3
"""Multicore hostile computations for current RH frontier.

Diagnostic only. Results from this script are forbidden as inputs to Lean proofs.

Implemented exact-source jobs:

1. S6F/TCD: direct theta-source derivative series through order eight and the
   exact reflected rank-three determinant on 0 <= x <= 137/2000. A dense
   float64 reconnaissance is followed by high-precision re-evaluation.
2. S6F/TCD: Arb interval-box evaluation of the same expression, including a
   conservative radius for the omitted n > 20 source-series tail.
3. CLG/TTF: broad high-precision scan of the exact C5 action/barrier formulas.

The process pool uses one BLAS/OpenMP thread per worker to avoid oversubscription.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import platform
import time
from dataclasses import dataclass
from multiprocessing import Pool
from pathlib import Path
from typing import Iterable

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("NUMEXPR_NUM_THREADS", "1")

import mpmath as mp
import numpy as np


X_MAX = 137.0 / 2000.0


def derivative_polynomials_float(a: float, order: int) -> list[np.ndarray]:
    """P_m with D^m exp(a*x-c(x)) = P_m(c) exp(a*x-c), c'=2c."""
    p = np.array([1.0])
    out = [p]
    for _ in range(order):
        q = np.zeros(len(p) + 1)
        for j, value in enumerate(p):
            q[j] += a * value
            q[j + 1] -= 2.0 * value
            if j:
                q[j] += 2.0 * j * value
        p = q
        out.append(p)
    return out


POLY_FLOAT = (
    derivative_polynomials_float(4.5, 9),
    derivative_polynomials_float(2.5, 9),
)


def poly_eval_float(coefficients: np.ndarray, x: np.ndarray) -> np.ndarray:
    answer = np.zeros_like(x)
    for coefficient in coefficients[::-1]:
        answer = answer * x + coefficient
    return answer


def theta_source_derivatives_float(xs: np.ndarray, order: int = 9, nmax: int = 14) -> np.ndarray:
    """Literal thetaCuspFullSource derivatives, vectorized over xs."""
    xs = np.asarray(xs, dtype=np.float64)
    result = np.zeros((order + 1, xs.size), dtype=np.float64)
    e2x = np.exp(2.0 * xs)
    for n in range(1, nmax + 1):
        nn = float(n)
        c = math.pi * nn * nn * e2x
        branches = (
            (4.0 * math.pi**2 * nn**4, 4.5, POLY_FLOAT[0]),
            (-6.0 * math.pi * nn**2, 2.5, POLY_FLOAT[1]),
        )
        for amplitude, exponent, polynomials in branches:
            base = amplitude * np.exp(exponent * xs - c)
            for derivative in range(order + 1):
                result[derivative] += base * poly_eval_float(polynomials[derivative], c)
    return result


def reflected_rank_three_float(xs: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    f = theta_source_derivatives_float(xs, order=9)
    p0 = f[0] ** 2
    p2 = 2.0 * (f[0] * f[2] - f[1] ** 2)
    p4 = 2.0 * f[0] * f[4] - 8.0 * f[1] * f[3] + 6.0 * f[2] ** 2
    p6 = (
        2.0 * f[0] * f[6]
        - 12.0 * f[1] * f[5]
        + 30.0 * f[2] * f[4]
        - 20.0 * f[3] ** 2
    )
    p8 = (
        2.0 * f[0] * f[8]
        - 16.0 * f[1] * f[7]
        + 56.0 * f[2] * f[6]
        - 112.0 * f[3] * f[5]
        + 70.0 * f[4] ** 2
    )
    determinant = (
        p0 * p4 * p8
        - p0 * p6**2
        - p2**2 * p8
        + 2.0 * p2 * p4 * p6
        - p4**3
    )
    normalized = determinant / f[0] ** 6

    # Exact derivative of the determinant is evaluated by shifting every source jet.
    def dprod(*terms: tuple[np.ndarray, np.ndarray]) -> np.ndarray:
        total = np.zeros_like(xs)
        for i, (_, derivative) in enumerate(terms):
            product = derivative.copy()
            for j, (value, _) in enumerate(terms):
                if i != j:
                    product *= value
            total += product
        return total

    p0d = 2.0 * f[0] * f[1]
    p2d = 2.0 * (f[0] * f[3] - f[1] * f[2])
    p4d = 2.0 * f[0] * f[5] - 6.0 * f[1] * f[4] + 4.0 * f[2] * f[3]
    p6d = (
        2.0 * f[0] * f[7]
        - 10.0 * f[1] * f[6]
        + 18.0 * f[2] * f[5]
        - 10.0 * f[3] * f[4]
    )
    p8d = (
        2.0 * f[0] * f[9]
        - 14.0 * f[1] * f[8]
        + 40.0 * f[2] * f[7]
        - 56.0 * f[3] * f[6]
        + 28.0 * f[4] * f[5]
    )
    derivative = (
        dprod((p0, p0d), (p4, p4d), (p8, p8d))
        - dprod((p0, p0d), (p6, p6d), (p6, p6d))
        - dprod((p2, p2d), (p2, p2d), (p8, p8d))
        + 2.0 * dprod((p2, p2d), (p4, p4d), (p6, p6d))
        - dprod((p4, p4d), (p4, p4d), (p4, p4d))
    )
    return determinant, normalized, derivative


def s6f_chunk(task: tuple[int, int, int]) -> dict:
    start, stop, total = task
    xs = np.linspace(0.0, X_MAX, total, dtype=np.float64)[start:stop]
    determinant, normalized, derivative = reflected_rank_three_float(xs)
    i_min = int(np.argmin(determinant))
    i_min_norm = int(np.argmin(normalized))
    i_max_derivative = int(np.argmax(np.abs(derivative)))
    sign_changes = np.flatnonzero(np.signbit(derivative[:-1]) != np.signbit(derivative[1:]))
    return {
        "count": int(xs.size),
        "minimum": [float(xs[i_min]), float(determinant[i_min])],
        "minimum_normalized": [float(xs[i_min_norm]), float(normalized[i_min_norm])],
        "maximum_abs_derivative": [float(xs[i_max_derivative]), float(abs(derivative[i_max_derivative]))],
        "negative_count": int(np.count_nonzero(determinant < 0.0)),
        "derivative_sign_change_brackets": [
            [float(xs[i]), float(xs[i + 1])] for i in sign_changes
        ],
    }


def merge_s6f(records: Iterable[dict]) -> dict:
    records = list(records)
    return {
        "points": sum(record["count"] for record in records),
        "minimum": min((record["minimum"] for record in records), key=lambda item: item[1]),
        "minimum_normalized": min(
            (record["minimum_normalized"] for record in records), key=lambda item: item[1]
        ),
        "maximum_abs_derivative": max(
            (record["maximum_abs_derivative"] for record in records), key=lambda item: item[1]
        ),
        "negative_count": sum(record["negative_count"] for record in records),
        "derivative_sign_change_brackets": [
            bracket
            for record in records
            for bracket in record["derivative_sign_change_brackets"]
        ],
    }


def derivative_polynomials_mp(a: mp.mpf, order: int) -> list[list[mp.mpf]]:
    p = [mp.mpf(1)]
    out = [p]
    for _ in range(order):
        q = [mp.mpf(0)] * (len(p) + 1)
        for j, value in enumerate(p):
            q[j] += a * value
            q[j + 1] -= 2 * value
            if j:
                q[j] += 2 * j * value
        p = q
        out.append(p)
    return out


def poly_eval_mp(coefficients: list[mp.mpf], x: mp.mpf) -> mp.mpf:
    answer = mp.mpf(0)
    for coefficient in reversed(coefficients):
        answer = answer * x + coefficient
    return answer


def theta_source_derivatives_mp(x: mp.mpf, order: int = 9, nmax: int = 40) -> list[mp.mpf]:
    polynomials = (
        derivative_polynomials_mp(mp.mpf(9) / 2, order),
        derivative_polynomials_mp(mp.mpf(5) / 2, order),
    )
    result = [mp.mpf(0)] * (order + 1)
    e2x = mp.exp(2 * x)
    for n in range(1, nmax + 1):
        nn = mp.mpf(n)
        c = mp.pi * nn**2 * e2x
        branches = (
            (4 * mp.pi**2 * nn**4, mp.mpf(9) / 2, polynomials[0]),
            (-6 * mp.pi * nn**2, mp.mpf(5) / 2, polynomials[1]),
        )
        for amplitude, exponent, branch_polynomials in branches:
            base = amplitude * mp.exp(exponent * x - c)
            for derivative in range(order + 1):
                result[derivative] += base * poly_eval_mp(branch_polynomials[derivative], c)
    return result


def reflected_rank_three_mp(x: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    f = theta_source_derivatives_mp(x, 8)
    p0 = f[0] ** 2
    p2 = 2 * (f[0] * f[2] - f[1] ** 2)
    p4 = 2 * f[0] * f[4] - 8 * f[1] * f[3] + 6 * f[2] ** 2
    p6 = 2 * f[0] * f[6] - 12 * f[1] * f[5] + 30 * f[2] * f[4] - 20 * f[3] ** 2
    p8 = (
        2 * f[0] * f[8]
        - 16 * f[1] * f[7]
        + 56 * f[2] * f[6]
        - 112 * f[3] * f[5]
        + 70 * f[4] ** 2
    )
    determinant = p0 * p4 * p8 - p0 * p6**2 - p2**2 * p8 + 2 * p2 * p4 * p6 - p4**3
    return determinant, determinant / f[0] ** 6


def arb_poly_eval(coefficients, x):
    from flint import arb

    answer = arb(0)
    for coefficient in reversed(coefficients):
        answer = answer * x + arb(str(coefficient))
    return answer


def arb_tail_radius(order: int, n0: int = 21) -> str:
    """Conservative source-derivative tail radius for n >= n0 on [0, X_MAX].

    For n >= 21 the envelope ratio is far below 1/2; twice its first term
    therefore bounds the full remaining tail. Coefficient absolute values are
    taken from the exact derivative recurrence.
    """
    mp.mp.dps = 100
    total = mp.mpf(0)
    for a, power, amplitude, polynomials in (
        (mp.mpf(9) / 2, 4, 4 * mp.pi**2, derivative_polynomials_mp(mp.mpf(9) / 2, order)),
        (mp.mpf(5) / 2, 2, 6 * mp.pi, derivative_polynomials_mp(mp.mpf(5) / 2, order)),
    ):
        n = mp.mpf(n0)
        cmax = mp.pi * n**2 * mp.exp(2 * X_MAX)
        polynomial_bound = sum(abs(value) * cmax**j for j, value in enumerate(polynomials[order]))
        total += amplitude * n**power * mp.exp(a * X_MAX - mp.pi * n**2) * polynomial_bound
    return mp.nstr(2 * total, 40)


ARB_POLY_TEXT = (
    [[str(value) for value in polynomial] for polynomial in derivative_polynomials_mp(mp.mpf(9) / 2, 8)],
    [[str(value) for value in polynomial] for polynomial in derivative_polynomials_mp(mp.mpf(5) / 2, 8)],
)
ARB_TAIL_RADII = [arb_tail_radius(order) for order in range(9)]


def init_arb_worker(bits: int) -> None:
    from flint import ctx

    ctx.prec = bits


def arb_s6f_box(task: tuple[int, int]) -> dict:
    from flint import arb

    index, boxes = task
    lo = X_MAX * index / boxes
    hi = X_MAX * (index + 1) / boxes
    x = arb(str((lo + hi) / 2.0), str((hi - lo) / 2.0 + 2e-20))
    result = [arb(0) for _ in range(9)]
    e2x = (2 * x).exp()
    for n in range(1, 21):
        nn = arb(n)
        c = arb.pi() * nn**2 * e2x
        branches = (
            (4 * arb.pi() ** 2 * nn**4, arb(9) / 2, ARB_POLY_TEXT[0]),
            (-6 * arb.pi() * nn**2, arb(5) / 2, ARB_POLY_TEXT[1]),
        )
        for amplitude, exponent, polynomials in branches:
            base = amplitude * (exponent * x - c).exp()
            for derivative in range(9):
                result[derivative] += base * arb_poly_eval(polynomials[derivative], c)
    for derivative, radius in enumerate(ARB_TAIL_RADII):
        result[derivative] += arb(0, radius)
    f = result
    p0 = f[0] ** 2
    p2 = 2 * (f[0] * f[2] - f[1] ** 2)
    p4 = 2 * f[0] * f[4] - 8 * f[1] * f[3] + 6 * f[2] ** 2
    p6 = 2 * f[0] * f[6] - 12 * f[1] * f[5] + 30 * f[2] * f[4] - 20 * f[3] ** 2
    p8 = 2 * f[0] * f[8] - 16 * f[1] * f[7] + 56 * f[2] * f[6] - 112 * f[3] * f[5] + 70 * f[4] ** 2
    determinant = p0 * p4 * p8 - p0 * p6**2 - p2**2 * p8 + 2 * p2 * p4 * p6 - p4**3
    return {
        "index": index,
        "lo": lo,
        "hi": hi,
        "positive": bool(determinant > 0),
        "lower": float(determinant.lower()),
        "upper": float(determinant.upper()),
        "relative_accuracy_bits": int(determinant.rel_accuracy_bits()),
    }


def phi_derivatives_c5(x: mp.mpf, order: int = 2) -> list[mp.mpf]:
    sign = 1 if x >= 0 else -1
    values = theta_source_derivatives_mp(abs(x), order=order, nmax=30)
    if sign < 0:
        for index in range(1, order + 1, 2):
            values[index] = -values[index]
    return values


def c5_point(u: float, t: float) -> dict:
    mp.mp.dps = 60
    u_mp, t_mp = mp.mpf(u), mp.mpf(t)
    phi_u = phi_derivatives_c5(u_mp, 0)[0]
    pp, pp1, pp2 = phi_derivatives_c5(u_mp + t_mp, 2)
    pm, pm1, pm2 = phi_derivatives_c5(u_mp - t_mp, 2)
    p_zero = phi_u**2
    product = pp * pm
    lp1 = pp1 / pp
    lp2 = pp2 / pp - lp1**2
    lm1 = pm1 / pm
    lm2 = pm2 / pm - lm1**2
    q1 = lm1 - lp1
    q2 = -lp2 - lm2
    q = 2 * mp.log(phi_u) - mp.log(pp) - mp.log(pm)
    r = mp.expm1(q)
    action = 24 * r**2 - 9 * t_mp * r * q1 + t_mp**2 * (
        5 * r * (q2 - q1**2) - 4 * q1**2
    )
    a = p_zero - product
    d = product * q1
    j = product * (q2 - q1**2)
    c5 = 24 * a**2 - 9 * t_mp * a * d + t_mp**2 * (5 * a * j - 4 * d**2)
    barrier = c5 / a**2
    return {
        "u": u,
        "t": t,
        "action_sign": int(mp.sign(action)),
        "action": mp.nstr(action, 24),
        "barrier": mp.nstr(barrier, 24),
        "barrier_float": float(barrier),
        "identity_error": mp.nstr(c5 / product**2 - action, 8),
    }


def c5_worker(task: tuple[float, list[float]]) -> dict:
    u, ts = task
    minimum = None
    minimum_interior = None
    minimum_seam_normalized = None
    negative = []
    errors = []
    for t in ts:
        try:
            record = c5_point(u, t)
            if minimum is None or record["barrier_float"] < minimum["barrier_float"]:
                minimum = record
            if t >= 1e-3 and (
                minimum_interior is None
                or record["barrier_float"] < minimum_interior["barrier_float"]
            ):
                minimum_interior = record
            if t <= 1e-3:
                seam_normalized = record["barrier_float"] / t**4
                if minimum_seam_normalized is None or seam_normalized < minimum_seam_normalized["value"]:
                    minimum_seam_normalized = {"value": seam_normalized, "point": record}
            if record["action_sign"] < 0:
                negative.append(record)
        except Exception as error:  # pragma: no cover - recorded for remote diagnostics
            errors.append({"u": u, "t": t, "error": repr(error)})
    return {
        "minimum": minimum,
        "minimum_interior": minimum_interior,
        "minimum_seam_normalized": minimum_seam_normalized,
        "negative": negative,
        "errors": errors,
        "count": len(ts),
    }


def run(args: argparse.Namespace) -> dict:
    started = time.time()
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)

    # S6F/TCD dense reconnaissance.
    chunk_size = max(1024, math.ceil(args.s6f_points / (args.workers * 8)))
    tasks = [
        (start, min(start + chunk_size, args.s6f_points), args.s6f_points)
        for start in range(0, args.s6f_points, chunk_size)
    ]
    with Pool(args.workers) as pool:
        s6f = merge_s6f(pool.imap_unordered(s6f_chunk, tasks, chunksize=1))

    mp.mp.dps = 100
    audit_points = {
        0.0,
        X_MAX,
        float(s6f["minimum"][0]),
        float(s6f["minimum_normalized"][0]),
    }
    for bracket in s6f["derivative_sign_change_brackets"]:
        audit_points.add(sum(bracket) / 2.0)
    s6f["high_precision_audit"] = [
        {
            "x": point,
            "determinant": mp.nstr(reflected_rank_three_mp(mp.mpf(point))[0], 50),
            "normalized": mp.nstr(reflected_rank_three_mp(mp.mpf(point))[1], 50),
        }
        for point in sorted(audit_points)
    ]

    # Arb interval boxes. Every box must prove positive for a compact certificate.
    arb_tasks = [(index, args.arb_boxes) for index in range(args.arb_boxes)]
    with Pool(args.workers, initializer=init_arb_worker, initargs=(args.arb_bits,)) as pool:
        arb_records = list(pool.imap_unordered(arb_s6f_box, arb_tasks, chunksize=4))
    arb_records.sort(key=lambda record: record["index"])
    unresolved = [record for record in arb_records if not record["positive"]]
    s6f["arb"] = {
        "bits": args.arb_bits,
        "boxes": args.arb_boxes,
        "all_positive": not unresolved,
        "unresolved_count": len(unresolved),
        "minimum_lower_box": min(arb_records, key=lambda record: record["lower"]),
        "minimum_accuracy_bits": min(record["relative_accuracy_bits"] for record in arb_records),
        "tail_radii": ARB_TAIL_RADII,
        "unresolved_first_20": unresolved[:20],
    }
    with (output / "s6f_arb_boxes.jsonl").open("w") as handle:
        for record in arb_records:
            handle.write(json.dumps(record, sort_keys=True) + "\n")

    # C5 extended scan: u in [0, 20], t in [1e-6, 100], with seam-focused additions.
    us = np.unique(
        np.concatenate(
            [
                np.linspace(0.0, 8.0, args.c5_u_points),
                np.geomspace(8.01, 20.0, max(16, args.c5_u_points // 4)),
            ]
        )
    )
    ts = np.unique(
        np.concatenate(
            [
                np.geomspace(1e-6, 100.0, args.c5_t_points),
                np.linspace(0.01, 4.0, max(128, args.c5_t_points // 3)),
            ]
        )
    )
    with Pool(args.workers) as pool:
        c5_records = list(
            pool.imap_unordered(c5_worker, [(float(u), [float(t) for t in ts]) for u in us], chunksize=1)
        )
    c5_minima = [record["minimum"] for record in c5_records if record["minimum"] is not None]
    c5_interior = [
        record["minimum_interior"] for record in c5_records if record["minimum_interior"] is not None
    ]
    c5_seam = [
        record["minimum_seam_normalized"]
        for record in c5_records
        if record["minimum_seam_normalized"] is not None
    ]
    c5 = {
        "points": sum(record["count"] for record in c5_records),
        "u_range": [float(us.min()), float(us.max())],
        "t_range": [float(ts.min()), float(ts.max())],
        "minimum": min(c5_minima, key=lambda record: record["barrier_float"]),
        "minimum_t_ge_1e-3": min(c5_interior, key=lambda record: record["barrier_float"]),
        "minimum_barrier_over_t4_t_le_1e-3": min(c5_seam, key=lambda record: record["value"]),
        "negative_count": sum(len(record["negative"]) for record in c5_records),
        "negative_first_20": [item for record in c5_records for item in record["negative"]][:20],
        "errors": [item for record in c5_records for item in record["errors"]],
    }

    result = {
        "scope": "diagnostic-only; forbidden as input to Lean proofs",
        "environment": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "workers": args.workers,
            "numpy": np.__version__,
        },
        "parameters": vars(args),
        "s6f_tcd": s6f,
        "c5": c5,
        "elapsed_seconds": time.time() - started,
    }
    with (output / "results.json").open("w") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="results")
    parser.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--s6f-points", type=int, default=1_000_001)
    parser.add_argument("--arb-boxes", type=int, default=13_700)
    parser.add_argument("--arb-bits", type=int, default=192)
    parser.add_argument("--c5-u-points", type=int, default=241)
    parser.add_argument("--c5-t-points", type=int, default=900)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
