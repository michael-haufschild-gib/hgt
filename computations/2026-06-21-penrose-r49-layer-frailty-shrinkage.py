#!/usr/bin/env python3
"""R49: frailty shrinkage transferred to landscape-layer estimates.

NODE: frailty estimates shrink strongly toward the population mean, especially
in small clusters.

Target: landscape layers.  Test whether small t-window/lane cells make
phase-weld layer estimates shrink toward a global scalar-looking mean.

This is an instrument warning unless it creates a target-specific invariant.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import log
from random import Random
from statistics import mean, variance
from typing import Dict, Iterable, List, Sequence, Tuple

import mpmath as mp

mp.mp.dps = 35


@dataclass(frozen=True)
class Obs:
    sigma: float
    cluster: int
    value: float


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


def delta_value(a: complex, p: complex) -> float:
    eps = 1e-300
    return max(log(max(abs(a), eps)), log(max(abs(p), eps))) - log(max(abs(a + p), eps))


def node_frailty_demo() -> None:
    rng = Random(49)
    tau2 = 1.0
    sigma2 = 4.0
    true_effects = [rng.gauss(0, tau2**0.5) for _ in range(500)]
    print("\nNODE validation: empirical Bayes shrinkage in small clusters")
    for n in [1, 2, 4, 8, 32]:
        shrink = tau2 / (tau2 + sigma2 / n)
        post = []
        raw = []
        for theta in true_effects:
            ybar = mean(theta + rng.gauss(0, sigma2**0.5) for _ in range(n))
            raw.append(ybar)
            post.append(shrink * ybar)
        raw_abs = mean(abs(x) for x in raw)
        post_abs = mean(abs(x) for x in post)
        print(
            f"  n={n:2d}: shrink_factor={shrink:.3f}, "
            f"mean|raw|={raw_abs:.3f}, mean|posterior|={post_abs:.3f}"
        )


def sample_landscape(points_per_cluster: int = 5) -> List[Obs]:
    sigmas = [0.3, 0.5, 0.7, 1.2]
    windows = [(100.0, 170.0), (500.0, 570.0)]
    clusters_per_window = 7
    out: List[Obs] = []
    cluster_id = 0
    for lo, hi in windows:
        width = (hi - lo) / clusters_per_window
        for c in range(clusters_per_window):
            c_lo = lo + c * width
            c_hi = c_lo + width
            for sigma in sigmas:
                for j in range(points_per_cluster):
                    t = c_lo + (c_hi - c_lo) * (j + 0.5) / points_per_cluster
                    s = complex(sigma, t)
                    p = zeta_log_derivative(s)
                    a = arch_term_xi(s)
                    out.append(Obs(sigma=sigma, cluster=cluster_id, value=delta_value(a, p)))
            cluster_id += 1
    return out


def shrink_cells(obs: Sequence[Obs]) -> Tuple[Dict[Tuple[float, int], float], Dict[Tuple[float, int], float], float]:
    cells: Dict[Tuple[float, int], List[float]] = {}
    for item in obs:
        cells.setdefault((item.sigma, item.cluster), []).append(item.value)

    raw = {key: mean(vals) for key, vals in cells.items()}
    global_mean = mean(raw.values())
    cell_vars = [variance(vals) for vals in cells.values() if len(vals) > 1]
    within = mean(cell_vars) if cell_vars else 0.0
    between = max(0.0, variance(raw.values()) - within / mean(len(vals) for vals in cells.values()))
    n_eff = mean(len(vals) for vals in cells.values())
    shrink = between / (between + within / n_eff) if between + within / n_eff > 0 else 0.0
    shrunk = {key: global_mean + shrink * (value - global_mean) for key, value in raw.items()}
    return raw, shrunk, shrink


def lane_means(cell_values: Dict[Tuple[float, int], float]) -> Dict[float, float]:
    by_sigma: Dict[float, List[float]] = {}
    for (sigma, _cluster), value in cell_values.items():
        by_sigma.setdefault(sigma, []).append(value)
    return {sigma: mean(vals) for sigma, vals in by_sigma.items()}


def spread(means: Dict[float, float]) -> float:
    vals = list(means.values())
    return max(vals) - min(vals)


def bar(label: str, value: float, scale: float) -> str:
    count = int(40 * value / scale) if scale else 0
    return f"{label:<10} | {'#' * count} {value:.6f}"


def main() -> None:
    node = "frailty estimates can shrink strongly toward the population mean especially in small clusters"
    attempts = [
        "small lane-cluster phase estimates shrink toward landscape mean",
        "hierarchical pooling hides phase-weld layer heterogeneity",
        "cluster frailty warning becomes sigma-lane shrinkage diagnostic",
    ]
    print("R49 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_frailty_demo()
    obs = sample_landscape()
    raw, shrunk, shrink = shrink_cells(obs)
    raw_lanes = lane_means(raw)
    shrunk_lanes = lane_means(shrunk)
    raw_spread = spread(raw_lanes)
    shrunk_spread = spread(shrunk_lanes)

    print("\nLandscape phase-weld cell shrinkage:")
    print(f"  empirical shrink_factor={shrink:.6f}")
    print("  raw lane means:", {f"{k:.1f}": round(v, 6) for k, v in raw_lanes.items()})
    print("  shrunk lane means:", {f"{k:.1f}": round(v, 6) for k, v in shrunk_lanes.items()})
    print("\nVisual lane-spread attenuation:")
    scale = max(raw_spread, shrunk_spread)
    print(bar("raw", raw_spread, scale))
    print(bar("shrunk", shrunk_spread, scale))

    print("\nExtreme-case cluster-size sweep:")
    for n in [1, 2, 5, 10]:
        sweep_obs = sample_landscape(points_per_cluster=n)
        sweep_raw, sweep_shrunk, sweep_factor = shrink_cells(sweep_obs)
        sweep_raw_spread = spread(lane_means(sweep_raw))
        sweep_shrunk_spread = spread(lane_means(sweep_shrunk))
        ratio = sweep_shrunk_spread / sweep_raw_spread if sweep_raw_spread else 0.0
        print(
            f"  points_per_cell={n:2d}: shrink_factor={sweep_factor:.6f}, "
            f"raw_spread={sweep_raw_spread:.6f}, shrunk_spread={sweep_shrunk_spread:.6f}, "
            f"ratio={ratio:.6f}"
        )

    print("\nInterpretation:")
    print("  Small lane clusters attenuate the phase-weld layer contrast toward a global mean.")
    print("  This is an instrumentation warning unless it yields a non-generic layer invariant.")


if __name__ == "__main__":
    main()
