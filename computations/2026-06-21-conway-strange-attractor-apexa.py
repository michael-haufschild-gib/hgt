#!/usr/bin/env python3
"""THE-MACHINE tick: strange-attractor geometry -> APEX-A Schanuel gate.

NODE:
  "Strange" refers to geometric/fractal structure, not merely randomness or visual complexity.

Consolidated target:
  18/32 APEX-A -- Schanuel-for-prime-logs.

STEP 9 method:
  5. Make it visual.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass

import numpy as np


NODE = '"Strange" refers to geometric/fractal structure, not merely randomness or visual complexity'
TARGET = "18/32 APEX-A Schanuel-for-prime-logs"
METHOD = "5. Make it visual"

TRANSFER_ATTEMPTS = [
    "strangeness becomes algebraic relation geometry not digit randomness",
    "fractal scaling becomes Schanuel corank scaling of prime log monomials",
    "visual attractor complexity becomes small relation residual geometry",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def henon_points(n: int, burn: int = 500, a: float = 1.4, b: float = 0.3) -> np.ndarray:
    x, y = 0.1, 0.0
    pts = []
    for i in range(n + burn):
        x, y = 1.0 - a * x * x + y, b * x
        if i >= burn:
            pts.append((x, y))
    return np.asarray(pts, dtype=float)


def random_visual_points(n: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    theta = np.cumsum(rng.normal(0.0, 0.8, size=n))
    radius = 1.0 + 0.35 * np.sin(np.cumsum(rng.normal(0.0, 0.13, size=n)))
    noise = rng.normal(0.0, 0.08, size=(n, 2))
    return np.column_stack([radius * np.cos(theta), radius * np.sin(theta)]) + noise


def iid_cloud(n: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    return rng.normal(0.0, 1.0, size=(n, 2))


def standardize(points: np.ndarray) -> np.ndarray:
    x = np.asarray(points, dtype=float)
    return (x - x.mean(axis=0, keepdims=True)) / (x.std(axis=0, keepdims=True) + 1e-12)


def sampled_distances(points: np.ndarray, pairs: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    x = standardize(points)
    i = rng.integers(0, len(x), size=pairs)
    j = rng.integers(0, len(x), size=pairs)
    mask = i != j
    d = np.linalg.norm(x[i[mask]] - x[j[mask]], axis=1)
    return d[d > 1e-12]


@dataclass
class CorrDim:
    slope_mid: float
    slope_spread: float
    counts: list[float]
    radii: list[float]


def corr_dimension(points: np.ndarray, seed: int) -> CorrDim:
    d = sampled_distances(points, 220_000, seed)
    radii = np.logspace(-2.0, -0.15, 12)
    counts = np.array([np.mean(d < r) for r in radii], dtype=float)
    good = (counts > 1e-4) & (counts < 0.55)
    logs_r = np.log(radii[good])
    logs_c = np.log(counts[good])
    slopes = np.diff(logs_c) / np.diff(logs_r)
    if len(logs_r) >= 3:
        slope_mid = float(np.polyfit(logs_r, logs_c, 1)[0])
    else:
        slope_mid = float("nan")
    return CorrDim(
        slope_mid=slope_mid,
        slope_spread=float(np.std(slopes)) if len(slopes) else float("nan"),
        counts=[float(x) for x in counts],
        radii=[float(x) for x in radii],
    )


def sparkline(vals: list[float], width: int = 24) -> str:
    if not vals:
        return ""
    lo, hi = min(vals), max(vals)
    if hi <= lo + 1e-15:
        return "#" * min(width, len(vals))
    chars = " .:-=+*#%@"
    out = []
    for val in vals:
        idx = int(round((len(chars) - 1) * (val - lo) / (hi - lo)))
        out.append(chars[idx])
    return "".join(out)


def node_rows() -> list[str]:
    lines = ["STEP 5/6 NODE TEST: strange means invariant fractal geometry, not visual complexity"]
    lines.append(
        "Constraint: a strange attractor should show a stable non-integer scaling regime for "
        "correlation sums; visually complex stochastic paths/clouds need not."
    )
    datasets = [
        ("henon_attractor", henon_points(7000), 101),
        ("random_visual_path", random_visual_points(7000, 202), 203),
        ("iid_cloud", iid_cloud(7000, 303), 304),
    ]
    lines.append("dataset corr_dim_slope slope_spread count_sparkline")
    for name, pts, seed in datasets:
        cd = corr_dimension(pts, seed)
        lines.append(f"{name:18s} {cd.slope_mid:14.6f} {cd.slope_spread:12.6f} {sparkline(cd.counts)}")
    lines.append(
        "NODE verdict: the Hénon sample gives a low non-integer scaling slope, while random "
        "visual complexity and iid clouds fill closer to a two-dimensional support. The test "
        "is geometric; screenshots alone are irrelevant."
    )
    return lines


def degree2_monomials(xs: list[float]) -> np.ndarray:
    vals = []
    for i in range(len(xs)):
        for j in range(i, len(xs)):
            vals.append(xs[i] * xs[j])
    return np.asarray(vals, dtype=float)


def coeff_matrix(m: int, bound: int, chunk: int = 50_000):
    vals = range(-bound, bound + 1)
    buf = []
    for coeff in itertools.product(vals, repeat=m):
        if all(c == 0 for c in coeff):
            continue
        buf.append(coeff)
        if len(buf) >= chunk:
            yield np.asarray(buf, dtype=float)
            buf = []
    if buf:
        yield np.asarray(buf, dtype=float)


@dataclass
class RelationStats:
    min_abs: float
    argmin_coeff: list[int]
    counts: dict[float, int]
    q001: float
    q010: float
    q100: float
    samples: int


def relation_stats(values: np.ndarray, bound: int) -> RelationStats:
    thresholds = [1e-10, 1e-8, 1e-6, 1e-4]
    counts = {eps: 0 for eps in thresholds}
    best = float("inf")
    best_coeff: list[int] = []
    quantile_sample = []
    seen = 0
    for mat in coeff_matrix(len(values), bound):
        residual = np.abs(mat @ values)
        seen += len(residual)
        idx = int(np.argmin(residual))
        if float(residual[idx]) < best:
            best = float(residual[idx])
            best_coeff = [int(x) for x in mat[idx]]
        for eps in thresholds:
            counts[eps] += int(np.sum(residual < eps))
        if len(quantile_sample) < 220_000:
            quantile_sample.extend(float(x) for x in residual[: max(0, 220_000 - len(quantile_sample))])
    qs = np.quantile(np.asarray(quantile_sample, dtype=float), [0.001, 0.01, 0.10])
    return RelationStats(
        min_abs=best,
        argmin_coeff=best_coeff,
        counts=counts,
        q001=float(qs[0]),
        q010=float(qs[1]),
        q100=float(qs[2]),
        samples=seen,
    )


def transfer_rows(bound: int = 4) -> list[str]:
    rng = np.random.default_rng(52191)
    logs_prime = [math.log(2.0), math.log(3.0), math.log(5.0)]
    logs_random = list(rng.uniform(0.65, 1.75, size=3))
    logs_dependent = [math.log(2.0), math.log(3.0), math.log(2.0) + math.log(3.0)]
    cases = [
        ("prime_logs", degree2_monomials(logs_prime)),
        ("random_logs", degree2_monomials(logs_random)),
        ("dependent_fake", degree2_monomials(logs_dependent)),
    ]
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Correlation dimension applied unchanged to APEX-A would be a visual/randomness test and "
        "would reduce-to-known. Minimal transfer: replace visual geometry by the small-relation "
        "geometry of degree-2 prime-log monomials, the first open Schanuel rung."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER ATTEMPTS")
    best: tuple[int, int, str] | None = None
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        dist = levenshtein(NODE.lower(), attempt.lower())
        lines.append(f"{i}. distance={dist:3d} {attempt}")
        if best is None or dist < best[0]:
            best = (dist, i, attempt)
    assert best is not None
    lines.append(f"selected={best[1]} {best[2]}")
    lines.append(f"\nSTEP 9 METHOD {METHOD}")
    lines.append(
        "Visual object: residual barcodes for all integer coefficient vectors in [-B,B]^6 "
        "against the six degree-2 monomials x_i x_j, i<=j."
    )
    lines.append(f"bound={bound}; coefficient_vectors={(2 * bound + 1) ** 6 - 1}")
    lines.append("case min_abs count<1e-10 count<1e-8 count<1e-6 count<1e-4 q0.001 q0.01 q0.10 argmin_coeff")
    for name, vals in cases:
        stats = relation_stats(vals, bound)
        lines.append(
            f"{name:14s} {stats.min_abs:.3e} {stats.counts[1e-10]:9d} {stats.counts[1e-8]:9d} "
            f"{stats.counts[1e-6]:9d} {stats.counts[1e-4]:9d} {stats.q001:.3e} "
            f"{stats.q010:.3e} {stats.q100:.3e} {stats.argmin_coeff}"
        )
    lines.append(
        "STEP 10 verdict: the transfer detects the deliberately dependent fake immediately, but "
        "prime logs and random logs are indistinguishable at this finite visual/residual scale. "
        "That is useful as a kill gate for naive APEX-A numerics, not a new Schanuel fact."
    )
    lines.append(
        "STEP 11 metaphor: strange-attractor screenshots become residual-cloud screenshots; in "
        "both cases visual complexity is not the object. Here the object is exact algebraic "
        "corank, and the finite barcode does not cross the novelty gate."
    )
    return lines


def main() -> None:
    for row in node_rows():
        print(row)
    for row in transfer_rows():
        print(row)
    print("\nDEAD_END: APEX-A transfer is a useful negative gate but reduces to finite relation search.")


if __name__ == "__main__":
    main()
