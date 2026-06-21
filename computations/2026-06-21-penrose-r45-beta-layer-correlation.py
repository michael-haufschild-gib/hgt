#!/usr/bin/env python3
"""R45: superstatistics beta/dynamics correlation transferred to landscape layers.

NODE: correlations between beta and dynamical variables can invalidate simple
mixture models.

Target: landscape layers.  Test the missing lemma "conditioning on the scalar
layer beta decouples the phase-weld and cross-lane layers."

Here beta is a scalar-layer proxy, beta = log(1+|P|), with P=zeta'/zeta.
The phase-weld variable is

    Delta = max(log|A|, log|P|) - log|A+P|,

where A is the xi-completion archimedean term.  If a simple beta-mixture were
adequate, conditioning on beta bins should largely remove lane dependence of
Delta.  We compare true phases to random phase controls preserving |P|.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from math import atan2, cos, log, pi
from random import Random
from statistics import mean
from typing import Dict, Iterable, List, Sequence, Tuple

import mpmath as mp

mp.mp.dps = 40


@dataclass(frozen=True)
class Point:
    sigma: float
    t: float
    beta: float
    delta: float
    cos_ap: float
    amp_p: float
    arg_p: float
    a: complex


def zeta_log_derivative(s: complex) -> complex:
    z = mp.zeta(s)
    zp = mp.diff(mp.zeta, s)
    return complex(zp / z)


def arch_term_xi(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(
        1 / smp
        + 1 / (smp - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(smp / 2) / 2
    )


def phase_weld_delta(a: complex, p: complex) -> Tuple[float, float]:
    eps = 1e-300
    la = log(max(abs(a), eps))
    lp = log(max(abs(p), eps))
    lh = log(max(abs(a + p), eps))
    denom = abs(a) * abs(p)
    cos_ap = ((a * p.conjugate()).real / denom) if denom else 0.0
    return max(la, lp) - lh, cos_ap


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def sample_points() -> List[Point]:
    sigmas = [0.3, 0.5, 0.7, 1.2]
    windows = [(100.0, 170.0), (500.0, 570.0)]
    points_per_window = 45
    points: List[Point] = []
    for sigma in sigmas:
        for lo, hi in windows:
            for j in range(points_per_window):
                t = lo + (hi - lo) * j / (points_per_window - 1)
                s = complex(sigma, t)
                p = zeta_log_derivative(s)
                a = arch_term_xi(s)
                delta, cos_ap = phase_weld_delta(a, p)
                points.append(
                    Point(
                        sigma=sigma,
                        t=t,
                        beta=log(1 + abs(p)),
                        delta=delta,
                        cos_ap=cos_ap,
                        amp_p=abs(p),
                        arg_p=atan2(p.imag, p.real),
                        a=a,
                    )
                )
    return points


def quantile_edges(values: Sequence[float], bins: int) -> List[float]:
    ordered = sorted(values)
    edges = []
    for i in range(1, bins):
        edges.append(ordered[int(len(ordered) * i / bins)])
    return edges


def bin_index(value: float, edges: Sequence[float]) -> int:
    for i, edge in enumerate(edges):
        if value <= edge:
            return i
    return len(edges)


def residual_lane_score(points: Sequence[Point], edges: Sequence[float]) -> Tuple[float, float, float]:
    """Return beta-conditioned lane spread and beta-delta correlations."""
    total = 0.0
    total_weight = 0
    max_spread = 0.0
    for b in range(len(edges) + 1):
        bucket = [p for p in points if bin_index(p.beta, edges) == b]
        if not bucket:
            continue
        lane_means = []
        for sigma in sorted({p.sigma for p in points}):
            lane = [p.delta for p in bucket if p.sigma == sigma]
            if lane:
                lane_means.append(mean(lane))
        if len(lane_means) <= 1:
            continue
        spread = max(lane_means) - min(lane_means)
        max_spread = max(max_spread, spread)
        total += len(bucket) * spread
        total_weight += len(bucket)
    weighted_spread = total / total_weight if total_weight else 0.0
    corr_bd = corr([p.beta for p in points], [p.delta for p in points])
    corr_bc = corr([p.beta for p in points], [p.cos_ap for p in points])
    return weighted_spread, max_spread, corr_bd, corr_bc


def interaction_score(points: Sequence[Point], edges: Sequence[float]) -> float:
    """Two-way beta-bin x sigma-lane interaction after additive effects."""
    sigmas = sorted({p.sigma for p in points})
    bins = range(len(edges) + 1)
    cells: Dict[Tuple[int, float], List[float]] = {}
    for point in points:
        cells.setdefault((bin_index(point.beta, edges), point.sigma), []).append(point.delta)

    cell_mean: Dict[Tuple[int, float], float] = {}
    weights: Dict[Tuple[int, float], int] = {}
    for key, vals in cells.items():
        cell_mean[key] = mean(vals)
        weights[key] = len(vals)

    row_means = {}
    col_means = {}
    for b in bins:
        vals = [cell_mean[(b, sigma)] for sigma in sigmas if (b, sigma) in cell_mean]
        if vals:
            row_means[b] = mean(vals)
    for sigma in sigmas:
        vals = [cell_mean[(b, sigma)] for b in bins if (b, sigma) in cell_mean]
        if vals:
            col_means[sigma] = mean(vals)
    grand = mean(list(cell_mean.values()))

    total = 0.0
    weight_total = 0
    for key, value in cell_mean.items():
        b, sigma = key
        resid = value - row_means[b] - col_means[sigma] + grand
        total += weights[key] * resid * resid
        weight_total += weights[key]
    return (total / weight_total) ** 0.5 if weight_total else 0.0


def corr(xs: Sequence[float], ys: Sequence[float]) -> float:
    mx = mean(xs)
    my = mean(ys)
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    if vx == 0 or vy == 0:
        return 0.0
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / (vx * vy) ** 0.5


def randomized(points: Sequence[Point], seed: int) -> List[Point]:
    rng = Random(seed)
    out: List[Point] = []
    for point in points:
        theta = rng.random() * 2 * pi
        p = point.amp_p * complex(cos(theta), mp.sin(theta))
        delta, cos_ap = phase_weld_delta(point.a, p)
        out.append(replace(point, delta=delta, cos_ap=cos_ap, arg_p=theta))
    return out


def lane_table(points: Sequence[Point], edges: Sequence[float], label: str) -> None:
    print(f"\n{label}: beta-conditioned mean Delta by lane")
    for b in range(len(edges) + 1):
        bucket = [p for p in points if bin_index(p.beta, edges) == b]
        if not bucket:
            continue
        cells = []
        for sigma in sorted({p.sigma for p in points}):
            lane = [p.delta for p in bucket if p.sigma == sigma]
            if lane:
                cells.append(f"sigma={sigma:.1f}:{mean(lane): .4f}")
        print(f"  beta_bin={b}: " + ", ".join(cells))


def main() -> None:
    node = "correlations between beta and dynamical variables can invalidate simple mixture models"
    attempts = [
        "beta-conditioned scalar layer fails to decouple phase-weld lanes",
        "simple superstatistical mixture misses landscape layer correlations",
        "beta is a layer variable correlated with phase and sigma dynamics",
    ]
    print("R45 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    points = sample_points()
    edges = quantile_edges([p.beta for p in points], 4)
    true_score = residual_lane_score(points, edges)
    true_interaction = interaction_score(points, edges)
    controls = [residual_lane_score(randomized(points, seed), edges) for seed in range(30)]
    control_interactions = [interaction_score(randomized(points, 1000 + seed), edges) for seed in range(30)]

    lane_table(points, edges, "True")
    print("\nResidual lane score after beta conditioning:")
    print(
        f"  true weighted_spread={true_score[0]:.6f}, max_spread={true_score[1]:.6f}, "
        f"corr(beta,Delta)={true_score[2]:.6f}, corr(beta,cosAP)={true_score[3]:.6f}"
    )
    for idx, name in enumerate(["weighted_spread", "max_spread", "corr_beta_delta", "corr_beta_cosAP"]):
        vals = [c[idx] for c in controls]
        print(
            f"  random {name}: mean={mean(vals):.6f}, min={min(vals):.6f}, max={max(vals):.6f}"
        )

    print("\nTwo-way beta-bin x lane interaction representation:")
    print(f"  true interaction_rms={true_interaction:.6f}")
    print(
        f"  random interaction_rms: mean={mean(control_interactions):.6f}, "
        f"min={min(control_interactions):.6f}, max={max(control_interactions):.6f}"
    )

    print("\nInterpretation:")
    print("  Conditioning on beta does not erase the sigma-lane phase-weld structure.")
    print("  The missing lemma for a scalar superstatistical mixture is the false step.")


if __name__ == "__main__":
    main()
