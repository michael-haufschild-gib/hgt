#!/usr/bin/env python3
"""THE-MACHINE run: high-dimensional basin projection and zero-source geometry."""

from __future__ import annotations

import argparse
import math

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_projection_basin() -> None:
    print("NODE simulation: ball-in-cup projection hides high-dimensional basin membership")
    print("hidden_weight projection_accuracy full_accuracy ambiguous_projection_frac")
    rng = np.random.default_rng(506011)
    n = 6000
    x = rng.normal(0.0, 1.0, n)
    y = rng.normal(0.0, 1.0, n)
    z = rng.normal(0.0, 1.0, n)
    for hidden_weight in [0.0, 0.8, 1.6, 2.4]:
        score = x + 0.4 * y + hidden_weight * z
        basin = score > 0.0
        projected_pred = x + 0.4 * y > 0.0
        full_pred = score > 0.0
        near_boundary = np.abs(x + 0.4 * y) < 0.25
        ambiguous = float(np.mean(projected_pred[near_boundary] != basin[near_boundary])) if np.any(near_boundary) else 0.0
        print(f"{hidden_weight:13.2f} {np.mean(projected_pred == basin):19.4f} {np.mean(full_pred == basin):13.4f} {ambiguous:25.4f}")


def run_levenshtein() -> str:
    node_sig = "ball in cup diagram hides real basins are high dimensional"
    candidates = [
        "critical line diagram hides zero source geometry is transverse dimensional",
        "seam projection hides where zeros live in transverse geometry",
        "one dimensional zero profile hides high dimensional source basin",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best = None
    for i, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{i} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, i, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")
    return best[2]


def pole_profile(beta: float, gamma: float, tgrid: np.ndarray, smooth: float) -> np.ndarray:
    # Measured seam-only magnitude with finite resolution smoothing.
    tau = tgrid - gamma
    a = abs(beta - 0.5)
    return 1.0 / np.sqrt(tau * tau + a * a + smooth * smooth)


def transverse_curvature(beta: float, gamma: float, tgrid: np.ndarray, delta: float, smooth: float) -> np.ndarray:
    # Central second difference in sigma of a local source potential log |s-rho|.
    vals = []
    for t in tgrid:
        def potential(sig: float) -> float:
            return -0.5 * math.log((sig - beta) ** 2 + (t - gamma) ** 2 + smooth * smooth)
        vals.append((potential(0.5 + delta) - 2.0 * potential(0.5) + potential(0.5 - delta)) / (delta * delta))
    return np.asarray(vals)


def ht_zero_projection(samples: int) -> None:
    print("\nStanding-order consolidated target: Where the zeros live in the geometry")
    print("STEP8 transfer: seam projection hides where zeros live in transverse geometry")
    print("STEP9 method 11: run experiments")
    print(f"samples={samples}")
    gamma = 25.01085758014569
    tgrid = np.linspace(gamma - 1.2, gamma + 1.2, samples)
    print("offseam_a smooth profile_corr profile_l2 curvature_peak curvature_sign_changes projection_blind")
    for a in [0.02, 0.05, 0.10, 0.18]:
        for smooth in [0.02, 0.05, 0.10, 0.18]:
            seam = pole_profile(0.5, gamma, tgrid, smooth)
            off = pole_profile(0.5 + a, gamma, tgrid, smooth)
            seam_n = seam / max(float(np.linalg.norm(seam)), 1e-12)
            off_n = off / max(float(np.linalg.norm(off)), 1e-12)
            corr = float(np.dot(seam_n, off_n))
            l2 = float(np.linalg.norm(seam_n - off_n))
            curv = transverse_curvature(0.5 + a, gamma, tgrid, 0.04, smooth)
            signs = int(np.sum(np.diff(np.signbit(curv)) != 0))
            peak = float(np.max(np.abs(curv)))
            projection_blind = int(corr > 0.97 and l2 < 0.25 and peak > 50.0)
            print(f"{a:9.3f} {smooth:6.3f} {corr:12.6f} {l2:10.6f} {peak:14.4f} {signs:20d} {projection_blind:d}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=420)
    args = parser.parse_args()
    node_projection_basin()
    run_levenshtein()
    print("\nSTEP7 formula check: low-dimensional projection accuracy formulas are NODE-side diagnostics; unchanged use is geometry-blind.")
    ht_zero_projection(args.samples)


if __name__ == "__main__":
    main()
