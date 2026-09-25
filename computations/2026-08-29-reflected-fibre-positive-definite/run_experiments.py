#!/usr/bin/env python3
"""Hostile test of positive definiteness of completed-theta reflected fibres.

Diagnostic only. No output may be imported into Lean proofs.
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

import mpmath as mp
import numpy as np
from scipy.fft import dct


def theta_source_float(x):
    x = np.abs(np.asarray(x, dtype=np.float64))
    answer = np.zeros_like(x)
    e2x = np.exp(2 * x)
    for n in range(1, 17):
        nn = float(n)
        c = math.pi * nn * nn * e2x
        answer += (4 * math.pi**2 * nn**4 * np.exp(4.5 * x - c)
                   - 6 * math.pi * nn**2 * np.exp(2.5 * x - c))
    return answer


def reflected_fibre_float(x, t):
    center = float(theta_source_float(np.array([x]))[0])
    return theta_source_float(x + t) * theta_source_float(x - t) / center**2


def scan_center(task):
    x, t_max, samples, omega_max, toeplitz_max, step_count = task
    ts = np.linspace(0.0, t_max, samples)
    values = reflected_fibre_float(x, ts)
    transform = (t_max / (samples - 1)) * dct(values, type=1)
    omegas = math.pi * np.arange(samples) / t_max
    mask = omegas <= omega_max
    normalized = transform[mask] / transform[0]
    index = int(np.argmin(normalized))
    negative = np.flatnonzero(normalized < -1e-12)

    best_toeplitz = None
    toeplitz_by_size = []
    first_negative_size = None
    for size in range(4, toeplitz_max + 1):
        best_at_size = None
        for step in np.geomspace(0.005, 2.0, step_count):
            offsets = step * np.arange(size)
            row = reflected_fibre_float(x, offsets)
            matrix = row[np.abs(np.subtract.outer(np.arange(size), np.arange(size)))]
            eigenvalue = float(np.linalg.eigvalsh(matrix)[0])
            candidate = (eigenvalue, size, float(step))
            if best_at_size is None or candidate < best_at_size:
                best_at_size = candidate
            if best_toeplitz is None or candidate < best_toeplitz:
                best_toeplitz = candidate
        toeplitz_by_size.append({
            "size": size,
            "minimum_eigenvalue": best_at_size[0],
            "step": best_at_size[2],
        })
        if first_negative_size is None and best_at_size[0] < -1e-12:
            first_negative_size = size

    return {
        "x": float(x),
        "minimum_transform_ratio": float(normalized[index]),
        "minimum_transform_omega": float(omegas[mask][index]),
        "first_negative_transform_omega": (float(omegas[mask][negative[0]])
                                             if negative.size else None),
        "minimum_toeplitz_eigenvalue": best_toeplitz[0],
        "minimum_toeplitz_size": best_toeplitz[1],
        "minimum_toeplitz_step": best_toeplitz[2],
        "first_negative_toeplitz_size": first_negative_size,
        "toeplitz_by_size": toeplitz_by_size,
    }


def theta_source_mp(x):
    x = abs(mp.mpf(x))
    answer = mp.mpf(0)
    e2x = mp.exp(2 * x)
    for n in range(1, 25):
        nn = mp.mpf(n)
        c = mp.pi * nn**2 * e2x
        answer += 4 * mp.pi**2 * nn**4 * mp.exp(mp.mpf(9) * x / 2 - c)
        answer -= 6 * mp.pi * nn**2 * mp.exp(mp.mpf(5) * x / 2 - c)
    return answer


def reflected_fibre_mp(x, t):
    x, t = mp.mpf(x), mp.mpf(t)
    return theta_source_mp(x + t) * theta_source_mp(x - t) / theta_source_mp(x)**2


def cosine_transform_mp(x, omega, t_max):
    x, omega, t_max = mp.mpf(x), mp.mpf(omega), mp.mpf(t_max)
    integrand = lambda t: reflected_fibre_mp(x, t) * mp.cos(omega * t)
    if omega == 0:
        cuts = [mp.mpf(0), t_max]
    else:
        spacing = mp.pi / (2 * omega)
        cuts = [mp.mpf(0)]
        point = spacing
        while point < t_max:
            cuts.append(point)
            point += spacing
        cuts.append(t_max)
    return 2 * mp.fsum(mp.quad(integrand, [left, right])
                       for left, right in zip(cuts, cuts[1:]))


def toeplitz_mp(x, size, step):
    row = [reflected_fibre_mp(x, mp.mpf(step) * k) for k in range(size)]
    matrix = mp.matrix(size)
    for i in range(size):
        for j in range(size):
            matrix[i, j] = row[abs(i - j)]
    eigenvalues = mp.eigsy(matrix, eigvals_only=True)
    return min(eigenvalues)


def run(args):
    started = time.time()
    xs = np.unique(np.concatenate((
        np.linspace(0, 137 / 2000, args.centers),
        np.array([0.0, 0.01, 0.03, 0.05, 137 / 2000]),
    )))
    tasks = [(float(x), args.t_max, args.samples, args.omega_max,
              args.toeplitz_max, args.step_count) for x in xs]
    with Pool(args.workers) as pool:
        records = list(pool.imap_unordered(scan_center, tasks, chunksize=1))
    records.sort(key=lambda item: item["x"])
    transform_candidate = min(records, key=lambda item: item["minimum_transform_ratio"])
    toeplitz_candidate = min(records, key=lambda item: item["minimum_toeplitz_eigenvalue"])

    mp.mp.dps = args.dps
    transform_value = cosine_transform_mp(
        transform_candidate["x"], transform_candidate["minimum_transform_omega"], args.t_max)
    transform_zero = cosine_transform_mp(transform_candidate["x"], 0, args.t_max)
    toeplitz_value = toeplitz_mp(
        toeplitz_candidate["x"], toeplitz_candidate["minimum_toeplitz_size"],
        toeplitz_candidate["minimum_toeplitz_step"])
    rational_witnesses = []
    for size in (4, 5, 6):
        eigenvalue = toeplitz_mp(0, size, mp.mpf(1) / 50)
        rational_witnesses.append({
            "x": "0",
            "size": size,
            "step": "1/50",
            "minimum_eigenvalue": mp.nstr(eigenvalue, 70),
            "sign": int(mp.sign(eigenvalue)),
        })

    result = {
        "scope": "diagnostic only; forbidden as input to Lean proofs",
        "parameters": vars(args),
        "centers": len(records),
        "float_records": records,
        "strongest_transform_candidate": transform_candidate,
        "high_precision_transform": {
            "value": mp.nstr(transform_value, 70),
            "zero_frequency_value": mp.nstr(transform_zero, 70),
            "ratio": mp.nstr(transform_value / transform_zero, 70),
            "sign": int(mp.sign(transform_value)),
        },
        "strongest_toeplitz_candidate": toeplitz_candidate,
        "high_precision_toeplitz_min_eigenvalue": mp.nstr(toeplitz_value, 70),
        "high_precision_toeplitz_sign": int(mp.sign(toeplitz_value)),
        "rational_step_witnesses": rational_witnesses,
        "centers_with_negative_transform": sum(
            record["first_negative_transform_omega"] is not None for record in records),
        "centers_with_negative_toeplitz": sum(
            record["first_negative_toeplitz_size"] is not None for record in records),
        "environment": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "workers": args.workers,
            "numpy": np.__version__,
        },
        "elapsed_seconds": time.time() - started,
    }
    output = Path(args.output)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in (
        "centers", "strongest_transform_candidate", "high_precision_transform",
        "strongest_toeplitz_candidate", "high_precision_toeplitz_min_eigenvalue",
        "high_precision_toeplitz_sign", "elapsed_seconds")}, indent=2, sort_keys=True))


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="results.json")
    parser.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--centers", type=int, default=139)
    parser.add_argument("--t-max", type=float, default=4.0)
    parser.add_argument("--samples", type=int, default=32769)
    parser.add_argument("--omega-max", type=float, default=250.0)
    parser.add_argument("--toeplitz-max", type=int, default=18)
    parser.add_argument("--step-count", type=int, default=300)
    parser.add_argument("--dps", type=int, default=100)
    return parser.parse_args()


if __name__ == "__main__":
    run(parse_args())
