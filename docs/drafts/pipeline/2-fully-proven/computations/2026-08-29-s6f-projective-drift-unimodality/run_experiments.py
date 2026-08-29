#!/usr/bin/env python3
"""Hostile follow-up for S6F/TCD projective drift and raw unimodality.

Diagnostic only. No output from this script may be imported into a Lean proof.
"""

from __future__ import annotations

import argparse
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
os.environ.setdefault("NUMEXPR_NUM_THREADS", "1")

import mpmath as mp
import numpy as np


X_MAX = 137.0 / 2000.0


def derivative_polynomials(a, order: int):
    p = [a * 0 + 1]
    out = [p]
    for _ in range(order):
        q = [a * 0] * (len(p) + 1)
        for j, value in enumerate(p):
            q[j] += a * value
            q[j + 1] -= 2 * value
            if j:
                q[j] += 2 * j * value
        p = q
        out.append(p)
    return out


POLY_FLOAT = (
    derivative_polynomials(4.5, 10),
    derivative_polynomials(2.5, 10),
)


def poly_eval(coefficients, x):
    answer = x * 0
    for coefficient in reversed(coefficients):
        answer = answer * x + coefficient
    return answer


def source_jets_float(xs: np.ndarray, nmax: int = 14) -> list[np.ndarray]:
    jets = [np.zeros_like(xs) for _ in range(11)]
    e2x = np.exp(2 * xs)
    for n in range(1, nmax + 1):
        nn = float(n)
        c = math.pi * nn * nn * e2x
        for amplitude, exponent, polynomials in (
            (4 * math.pi**2 * nn**4, 4.5, POLY_FLOAT[0]),
            (-6 * math.pi * nn**2, 2.5, POLY_FLOAT[1]),
        ):
            base = amplitude * np.exp(exponent * xs - c)
            for order in range(11):
                jets[order] += base * poly_eval(polynomials[order], c)
    return jets


def jet_mul(a, b):
    return (
        a[0] * b[0],
        a[1] * b[0] + a[0] * b[1],
        a[2] * b[0] + 2 * a[1] * b[1] + a[0] * b[2],
    )


def jet_add(a, b):
    return tuple(a[i] + b[i] for i in range(3))


def jet_sub(a, b):
    return tuple(a[i] - b[i] for i in range(3))


def jet_scale(c, a):
    return tuple(c * a[i] for i in range(3))


def jet_pow(a, exponent: int):
    one = a[0] * 0 + 1
    result = (one, one * 0, one * 0)
    for _ in range(exponent):
        result = jet_mul(result, a)
    return result


def reflected_rank_three_jets(f):
    p0 = (
        f[0] ** 2,
        2 * f[0] * f[1],
        2 * (f[1] ** 2 + f[0] * f[2]),
    )
    p2 = (
        2 * (f[0] * f[2] - f[1] ** 2),
        2 * (f[0] * f[3] - f[1] * f[2]),
        2 * (f[0] * f[4] - f[2] ** 2),
    )
    p4 = (
        2 * f[0] * f[4] - 8 * f[1] * f[3] + 6 * f[2] ** 2,
        2 * f[0] * f[5] - 6 * f[1] * f[4] + 4 * f[2] * f[3],
        2 * f[0] * f[6] - 4 * f[1] * f[5] - 2 * f[2] * f[4] + 4 * f[3] ** 2,
    )
    p6 = (
        2 * f[0] * f[6] - 12 * f[1] * f[5] + 30 * f[2] * f[4] - 20 * f[3] ** 2,
        2 * f[0] * f[7] - 10 * f[1] * f[6] + 18 * f[2] * f[5] - 10 * f[3] * f[4],
        2 * f[0] * f[8] - 8 * f[1] * f[7] + 8 * f[2] * f[6] +
        8 * f[3] * f[5] - 10 * f[4] ** 2,
    )
    p8 = (
        2 * f[0] * f[8] - 16 * f[1] * f[7] + 56 * f[2] * f[6] -
        112 * f[3] * f[5] + 70 * f[4] ** 2,
        2 * f[0] * f[9] - 14 * f[1] * f[8] + 40 * f[2] * f[7] -
        56 * f[3] * f[6] + 28 * f[4] * f[5],
        2 * f[0] * f[10] - 12 * f[1] * f[9] + 26 * f[2] * f[8] -
        16 * f[3] * f[7] - 28 * f[4] * f[6] + 28 * f[5] ** 2,
    )
    determinant = jet_sub(
        jet_add(
            jet_sub(jet_mul(jet_mul(p0, p4), p8), jet_mul(p0, jet_pow(p6, 2))),
            jet_scale(2, jet_mul(jet_mul(p2, p4), p6)),
        ),
        jet_add(jet_mul(jet_pow(p2, 2), p8), jet_pow(p4, 3)),
    )
    return determinant


def dense_chunk(task):
    start, stop, total = task
    xs = np.linspace(0, X_MAX, total, dtype=np.float64)[start:stop]
    f = source_jets_float(xs)
    determinant, raw_derivative, raw_second = reflected_rank_three_jets(f)
    projective_numerator = raw_derivative * f[0] - 6 * determinant * f[1]
    normalized_derivative = projective_numerator / f[0] ** 7

    def sign_changes(values):
        places = np.flatnonzero(np.signbit(values[:-1]) != np.signbit(values[1:]))
        return [[float(xs[i]), float(xs[i + 1])] for i in places]

    i_n = int(np.argmin(projective_numerator))
    i_nd = int(np.argmin(normalized_derivative))
    return {
        "count": len(xs),
        "projective_numerator_minimum": [float(xs[i_n]), float(projective_numerator[i_n])],
        "normalized_derivative_minimum": [float(xs[i_nd]), float(normalized_derivative[i_nd])],
        "projective_sign_changes": sign_changes(projective_numerator),
        "raw_derivative_sign_changes": sign_changes(raw_derivative),
        "raw_second_sign_changes": sign_changes(raw_second),
        "projective_negative_count": int(np.count_nonzero(projective_numerator < 0)),
    }


def merge_dense(records):
    return {
        "points": sum(r["count"] for r in records),
        "projective_numerator_minimum": min(
            (r["projective_numerator_minimum"] for r in records), key=lambda z: z[1]
        ),
        "normalized_derivative_minimum": min(
            (r["normalized_derivative_minimum"] for r in records), key=lambda z: z[1]
        ),
        "projective_sign_changes": [z for r in records for z in r["projective_sign_changes"]],
        "raw_derivative_sign_changes": [z for r in records for z in r["raw_derivative_sign_changes"]],
        "raw_second_sign_changes": [z for r in records for z in r["raw_second_sign_changes"]],
        "projective_negative_count": sum(r["projective_negative_count"] for r in records),
    }


mp.mp.dps = 100
POLY_ARB = (
    [[str(v) for v in p] for p in derivative_polynomials(mp.mpf(9) / 2, 10)],
    [[str(v) for v in p] for p in derivative_polynomials(mp.mpf(5) / 2, 10)],
)


def tail_radius(order: int, n0: int = 21) -> str:
    total = mp.mpf(0)
    for a, power, amplitude, polynomials in (
        (mp.mpf(9) / 2, 4, 4 * mp.pi**2, derivative_polynomials(mp.mpf(9) / 2, order)),
        (mp.mpf(5) / 2, 2, 6 * mp.pi, derivative_polynomials(mp.mpf(5) / 2, order)),
    ):
        n = mp.mpf(n0)
        cmax = mp.pi * n**2 * mp.exp(2 * X_MAX)
        pbound = sum(abs(v) * cmax**j for j, v in enumerate(polynomials[order]))
        total += amplitude * n**power * mp.exp(a * X_MAX - mp.pi * n**2) * pbound
    return mp.nstr(2 * total, 50)


TAIL_RADII = [tail_radius(order) for order in range(11)]


def init_arb(bits: int):
    from flint import ctx
    ctx.prec = bits


def arb_poly_eval(coefficients, x):
    from flint import arb

    answer = arb(0)
    for coefficient in reversed(coefficients):
        answer = answer * x + arb(coefficient)
    return answer


def arb_box(task):
    from flint import arb

    index, boxes = task
    lo = X_MAX * index / boxes
    hi = X_MAX * (index + 1) / boxes
    x = arb(str((lo + hi) / 2), str((hi - lo) / 2 + 2e-20))
    f = [arb(0) for _ in range(11)]
    e2x = (2 * x).exp()
    for n in range(1, 21):
        nn = arb(n)
        c = arb.pi() * nn**2 * e2x
        for amplitude, exponent, polynomials in (
            (4 * arb.pi() ** 2 * nn**4, arb(9) / 2, POLY_ARB[0]),
            (-6 * arb.pi() * nn**2, arb(5) / 2, POLY_ARB[1]),
        ):
            base = amplitude * (exponent * x - c).exp()
            for order in range(11):
                f[order] += base * arb_poly_eval(polynomials[order], c)
    for order, radius in enumerate(TAIL_RADII):
        f[order] += arb(0, radius)
    determinant, raw_derivative, raw_second = reflected_rank_three_jets(f)
    projective = raw_derivative * f[0] - 6 * determinant * f[1]

    def sign(z):
        if bool(z > 0):
            return 1
        if bool(z < 0):
            return -1
        return 0

    return {
        "index": index,
        "lo": lo,
        "hi": hi,
        "source_sign": sign(f[0]),
        "projective_sign": sign(projective),
        "raw_derivative_sign": sign(raw_derivative),
        "raw_second_sign": sign(raw_second),
        "projective_lower": float(projective.lower()),
        "projective_upper": float(projective.upper()),
    }


def contiguous_ranges(records, key: str, value: int):
    indices = [r["index"] for r in records if r[key] == value]
    if not indices:
        return []
    groups = []
    start = previous = indices[0]
    for index in indices[1:]:
        if index != previous + 1:
            groups.append([records[start]["lo"], records[previous]["hi"], previous - start + 1])
            start = index
        previous = index
    groups.append([records[start]["lo"], records[previous]["hi"], previous - start + 1])
    return groups


def run(args):
    started = time.time()
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)

    chunk = max(1024, math.ceil(args.points / (args.workers * 8)))
    tasks = [(i, min(i + chunk, args.points), args.points) for i in range(0, args.points, chunk)]
    with Pool(args.workers) as pool:
        dense = merge_dense(list(pool.imap_unordered(dense_chunk, tasks, chunksize=1)))

    tasks = [(i, args.boxes) for i in range(args.boxes)]
    with Pool(args.workers, initializer=init_arb, initargs=(args.bits,)) as pool:
        records = list(pool.imap_unordered(arb_box, tasks, chunksize=2))
    records.sort(key=lambda r: r["index"])
    with (output / "arb_boxes.jsonl").open("w") as handle:
        for record in records:
            handle.write(json.dumps(record, sort_keys=True) + "\n")

    arb_summary = {
        "bits": args.bits,
        "boxes": args.boxes,
        "tail_radii": TAIL_RADII,
        "source_nonpositive_ranges": contiguous_ranges(records, "source_sign", 0) +
            contiguous_ranges(records, "source_sign", -1),
        "projective_positive_count": sum(r["projective_sign"] == 1 for r in records),
        "projective_negative_count": sum(r["projective_sign"] == -1 for r in records),
        "projective_unresolved_ranges": contiguous_ranges(records, "projective_sign", 0),
        "raw_derivative_positive_ranges": contiguous_ranges(records, "raw_derivative_sign", 1),
        "raw_derivative_negative_ranges": contiguous_ranges(records, "raw_derivative_sign", -1),
        "raw_derivative_unresolved_ranges": contiguous_ranges(records, "raw_derivative_sign", 0),
        "raw_second_negative_ranges": contiguous_ranges(records, "raw_second_sign", -1),
        "raw_second_unresolved_ranges": contiguous_ranges(records, "raw_second_sign", 0),
        "minimum_projective_lower_box": min(records, key=lambda r: r["projective_lower"]),
    }
    result = {
        "scope": "diagnostic only; forbidden as input to Lean proofs",
        "parameters": vars(args),
        "environment": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "workers": args.workers,
            "numpy": np.__version__,
        },
        "dense": dense,
        "arb": arb_summary,
        "elapsed_seconds": time.time() - started,
    }
    with (output / "results.json").open("w") as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
    print(json.dumps(result, indent=2, sort_keys=True))


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="results")
    parser.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--points", type=int, default=1_000_001)
    parser.add_argument("--boxes", type=int, default=27_400)
    parser.add_argument("--bits", type=int, default=256)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
