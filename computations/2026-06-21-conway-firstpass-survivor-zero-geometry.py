#!/usr/bin/env python3
"""THE-MACHINE tick: absorbing-boundary survivor bias -> zero geometry.

NODE:
  Absorbing boundaries alter the ensemble of surviving trajectories over time.

Consolidated target:
  Where the zeros live in the geometry.

STEP 9 method:
  15. Strengthen the conjecture.
"""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np


NODE = "absorbing boundaries alter the ensemble of surviving trajectories over time"

TRANSFER_ATTEMPTS = [
    "zero source geometry must not be inferred from survivor trajectories that avoid absorbing zeros",
    "conditioning on nonzero survival can fabricate apparent repulsion from the critical seam",
    "zeros as absorbing boundaries bias the sampled geometry away from source support",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_rows() -> list[str]:
    rng = np.random.default_rng(2606216401)
    n = 30000
    x = rng.uniform(0.05, 1.0, size=n)
    alive = np.ones(n, dtype=bool)
    lines = ["STEP 6 NODE TEST: absorbing boundary reshapes survivors"]
    lines.append("time alive_frac survivor_mean_x survivor_q10_x")
    for step in [0, 10, 30, 60, 100, 160]:
        while getattr(node_rows, "_step", 0) < step:
            x[alive] += rng.normal(scale=0.035, size=int(np.sum(alive)))
            alive &= x > 0
            node_rows._step = getattr(node_rows, "_step", 0) + 1  # type: ignore[attr-defined]
        xs = x[alive]
        lines.append(f"{step:03d} {float(np.mean(alive)):.4f} {float(np.mean(xs)):.4f} {float(np.quantile(xs,0.10)):.4f}")
    if hasattr(node_rows, "_step"):
        delattr(node_rows, "_step")
    lines.append(
        "NODE verdict: the absorbing boundary removes near-boundary paths; surviving trajectories "
        "move away from the boundary even without any repulsive drift."
    )
    return lines


def zeta_zero_imags(max_t: float) -> np.ndarray:
    vals = []
    k = 1
    while True:
        rho = complex(mp.zetazero(k))
        if rho.imag > max_t:
            break
        vals.append(float(rho.imag))
        k += 1
    return np.array(vals)


def simulate_survivors(
    rng: np.random.Generator,
    zero_points: np.ndarray,
    sigma_range: tuple[float, float],
    t_range: tuple[float, float],
    n: int = 20000,
    steps: int = 140,
    step_sigma: float = 0.018,
    step_t: float = 0.42,
    radius_sigma: float = 0.030,
    radius_t: float = 0.75,
) -> dict[str, float]:
    sigma = rng.uniform(sigma_range[0], sigma_range[1], size=n)
    t = rng.uniform(t_range[0], t_range[1], size=n)
    alive = np.ones(n, dtype=bool)
    for _ in range(steps):
        idx = np.where(alive)[0]
        sigma[idx] += rng.normal(scale=step_sigma, size=len(idx))
        t[idx] += rng.normal(scale=step_t, size=len(idx))
        alive &= (sigma >= sigma_range[0]) & (sigma <= sigma_range[1]) & (t >= t_range[0]) & (t <= t_range[1])
        idx = np.where(alive)[0]
        if len(idx) == 0:
            break
        ds = (sigma[idx, None] - zero_points[:, 0][None, :]) / radius_sigma
        dt = (t[idx, None] - zero_points[:, 1][None, :]) / radius_t
        hit = np.any(ds * ds + dt * dt <= 1.0, axis=1)
        alive[idx[hit]] = False
    surv_sigma = sigma[alive]
    return {
        "alive": float(np.mean(alive)),
        "mean_abs_seam_dist": float(np.mean(np.abs(surv_sigma - 0.5))) if len(surv_sigma) else float("nan"),
        "near_seam_frac": float(np.mean(np.abs(surv_sigma - 0.5) < 0.06)) if len(surv_sigma) else float("nan"),
        "left_right_balance": float(np.mean(surv_sigma > 0.5)) if len(surv_sigma) else float("nan"),
    }


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "First-passage formulas do not apply unchanged to zero geometry. The transfer keeps the "
        "conditioning warning: samples of points/paths that survive around zeros can create apparent "
        "geometry not present in the source measure."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")
    lines.append("\nSTEP 9 METHOD 15: STRENGTHEN THE CONJECTURE")
    lines.append(
        "Strengthened warning: zero geometry cannot be inferred from survivor paths that avoid "
        "absorbing disks around candidate zeros; compare true seam zeros to random seam and off-seam controls."
    )

    rng = np.random.default_rng(2606216511)
    imags = zeta_zero_imags(170.0)
    imags = imags[imags >= 14.0]
    true_points = np.column_stack([np.full(len(imags), 0.5), imags])
    random_seam = np.column_stack([np.full(len(imags), 0.5), rng.uniform(14.0, 170.0, size=len(imags))])
    off_seam = np.column_stack([rng.choice([0.42, 0.58], size=len(imags)), imags])
    no_absorb = np.empty((0, 2))
    controls = {
        "no_absorb": no_absorb,
        "true_seam_zeros": true_points,
        "random_seam_points": random_seam,
        "off_seam_points": off_seam,
    }
    lines.append("control alive mean_abs_seam_dist near_seam_frac right_frac")
    for name, points in controls.items():
        stats = simulate_survivors(rng, points, (0.30, 0.70), (14.0, 170.0))
        lines.append(
            f"{name:18s} {stats['alive']:.4f} {stats['mean_abs_seam_dist']:.4f} "
            f"{stats['near_seam_frac']:.4f} {stats['left_right_balance']:.4f}"
        )
    lines.append(
        "\nProvisional interpretation: if random seam absorbers reproduce the survivor bias, this is "
        "not zero-specific geometry. Use argument-principle/source-measure tests, not survivor ensembles."
    )
    return lines


def main() -> None:
    out = []
    out.append("THE-MACHINE tick: first-passage survivor bias -> zero geometry")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 6/32 Where the zeros live in the geometry")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
