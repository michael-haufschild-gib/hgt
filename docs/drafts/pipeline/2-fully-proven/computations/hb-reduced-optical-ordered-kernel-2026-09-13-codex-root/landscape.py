#!/usr/bin/env python3
"""Actual-zero/off-axis landscape and boundary/onset ablation challenge."""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
from concurrent.futures import ProcessPoolExecutor
from statistics import median

import mpmath as mp

from common import coefficient, relative_residual


L_GRID = [2 * math.e * (60 / (2 * math.e)) ** (j / 31) for j in range(32)]
# x=0 makes q_plus=q_minus and every primitive difference zero identically.
# Keep that exact moving-characteristic endpoint as a separate boundary check,
# and exclude it from interior suppression statistics.
X_GRID = [j / 64 for j in range(1, 65)]
SIGMAS = [0.20, 0.35, 0.50, 0.65, 0.80]
VARIANTS = [
    ("complete", True, "difference"),
    ("no_onset", False, "difference"),
    ("plus_face_only", True, "plus"),
    ("minus_face_only", True, "minus"),
]


def zeta_zero(n: int) -> tuple[int, float]:
    mp.mp.dps = 40
    return n, float(mp.im(mp.zetazero(n)))


def quantile(values: list[float], p: float) -> float:
    a = sorted(values)
    return a[min(len(a) - 1, int(p * (len(a) - 1)))]


def evaluate(task: tuple[int, float, float, str, bool, str]) -> dict:
    n, gamma, sigma, name, onset, endpoint = task
    rho = complex(sigma, gamma)
    rels = []
    phases = []
    mags = []
    min_item = (float("inf"), None, None)
    for L in L_GRID:
        for x in X_GRID:
            c = coefficient(rho, L, x, onset=onset, endpoint=endpoint)
            rel = relative_residual(rho, L, x, onset=onset, endpoint=endpoint)
            rels.append(rel)
            if rel < min_item[0]:
                min_item = (rel, L, x)
            mags.append(abs(c))
            if abs(c) > 1e-280:
                phases.append(min(abs(c.real), abs(c.imag)) / abs(c))
    return {
        "n": n,
        "gamma": gamma,
        "sigma": sigma,
        "variant": name,
        "min_rel": min(rels),
        "min_L": min_item[1],
        "min_x": min_item[2],
        "q01_rel": quantile(rels, 0.01),
        "median_rel": median(rels),
        "q99_rel": quantile(rels, 0.99),
        "max_rel": max(rels),
        "near_zero_count": sum(v < 1e-10 for v in rels),
        "median_axis_distance": median(phases),
        "median_log10_abs": median([math.log10(max(v, 1e-300)) for v in mags]),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", type=int, default=1)
    ap.add_argument("--stop", type=int, default=128)
    ap.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    ap.add_argument("--out", default="results")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        zeros = dict(pool.map(zeta_zero, range(args.start, args.stop + 1)))
        tasks = [
            (n, zeros[n], sigma, name, onset, endpoint)
            for n in range(args.start, args.stop + 1)
            for sigma in SIGMAS
            for name, onset, endpoint in VARIANTS
        ]
        rows = list(pool.map(evaluate, tasks, chunksize=2))
    fields = list(rows[0])
    with open(os.path.join(args.out, "landscape.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)

    summary = {}
    for name, _, _ in VARIANTS:
        by_sigma = {}
        for sigma in SIGMAS:
            rr = [r for r in rows if r["variant"] == name and r["sigma"] == sigma]
            by_sigma[str(sigma)] = {
                "min_over_all_points": min(r["min_rel"] for r in rr),
                "median_of_pointwise_medians": median(r["median_rel"] for r in rr),
                "max_near_zero_count_per_zero": max(r["near_zero_count"] for r in rr),
                "median_axis_distance": median(r["median_axis_distance"] for r in rr),
            }
        summary[name] = by_sigma

    # Exact complementary-map covariance check and critical-line conjugacy check.
    challenges = []
    for n in [args.start, min(args.stop, 2), min(args.stop, 17), args.stop]:
        gamma = zeros[n]
        for L, x in [(2 * math.e, 0.0), (7.0, 0.37), (23.0, 0.5), (60.0, 1.0)]:
            rho = complex(0.5, gamma)
            c = coefficient(rho, L, x)
            cc = coefficient(1 - rho, L, x)
            challenges.append({
                "n": n, "L": L, "x": x,
                "complement_antisymmetry_rel": abs(c + cc) / max(abs(c) + abs(cc), 1e-300),
                "critical_real_fraction": abs(c.real) / max(abs(c), 1e-300),
                "critical_imag_fraction": abs(c.imag) / max(abs(c), 1e-300),
            })
    payload = {
        "formula": "HB-TWO-SIDED-SOURCE-CURRENT equations (13)-(14)",
        "ranges": {"zeros": [args.start, args.stop], "L": [L_GRID[0], L_GRID[-1]], "x": [0, 1]},
        "grid_points_per_parameter": len(L_GRID) * len(X_GRID),
        "summary": summary,
        "challenges": challenges,
        "excluded_boundary_fact": "At x=0, d=L-1 and q_plus=q_minus=L, so all complete primitive differences vanish identically.",
    }
    with open(os.path.join(args.out, "summary.json"), "w") as f:
        json.dump(payload, f, indent=2)


if __name__ == "__main__":
    main()
