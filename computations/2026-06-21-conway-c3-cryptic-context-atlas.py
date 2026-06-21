#!/usr/bin/env python3
"""Workflow pass: cryptic allosteric sites -> C3 condition atlas."""

from __future__ import annotations

import math
import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-hawkes-edge-c3.py")
phase_series = BASE["phase_series"]
phase_stats = BASE["phase_stats"]


def node_cryptic_allostery(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    conditions = ["apo", "ligand", "low_pH", "membrane"]
    # A cryptic pocket exists only in one ensemble condition; pooled structure
    # dilutes it below detection.
    occupancy = {
        "apo": rng.beta(1.0, 28.0, size=500),
        "ligand": rng.beta(8.0, 5.0, size=500),
        "low_pH": rng.beta(2.0, 18.0, size=500),
        "membrane": rng.beta(3.0, 15.0, size=500),
    }
    pooled = np.concatenate([occupancy[c] for c in conditions])
    print("NODE: allosteric sites can be transient/cryptic and condition-formed")
    print("condition mean_occupancy active_frac_gt_0.35")
    for c in conditions:
        x = occupancy[c]
        print(f"{c:8s} {float(np.mean(x)):.3f} {float(np.mean(x > 0.35)):.3f}")
    print(f"pooled   {float(np.mean(pooled)):.3f} {float(np.mean(pooled > 0.35)):.3f}")


def energy_tail_gap(t_true: np.ndarray, th_true: np.ndarray, t_fin: np.ndarray, th_fin: np.ndarray) -> tuple[float, float, float]:
    st_true = phase_stats(t_true, th_true, crop_frac=0.10)
    st_fin = phase_stats(t_fin, th_fin, crop_frac=0.10)
    full_gap = abs(st_true["h1_interior"] - st_fin["h1_interior"])
    dtheta = np.gradient(th_true, t_true)
    energy = dtheta * dtheta
    threshold = np.quantile(energy, 0.95)
    core = energy >= threshold
    # Dilate by four samples.
    for shift in range(1, 5):
        core[:-shift] |= core[shift:]
        core[shift:] |= core[:-shift]
    tail = ~core
    true_tail = math.sqrt(float(np.mean(energy[tail])))
    fin_energy = np.gradient(th_fin, t_fin) ** 2
    fin_tail = math.sqrt(float(np.mean(fin_energy[tail])))
    tail_gap = abs(true_tail - fin_tail)
    return full_gap, tail_gap, float(np.mean(core))


def transfer_atlas() -> None:
    print()
    print("TRANSFER: ResearchNode #25 C3 phase-Sobolev")
    print("method #15 strengthen: require a sigma/window activation atlas, not a single-condition C3 claim")
    rng = np.random.default_rng(260621971)
    windows = [(100.0, 170.0), (500.0, 570.0)]
    sigmas = [0.30, 0.40, 0.50, 0.60, 0.70, 0.90, 1.15, 1.30]
    print("window sigma full_gap tail_gap tail_retention core_frac verdict")
    active = 0
    total = 0
    for window in windows:
        for sigma in sigmas:
            t_true, th_true = phase_series("true", sigma, window, 520, rng)
            t_fin, th_fin = phase_series("finite", sigma, window, 520, rng)
            full_gap, tail_gap, core_frac = energy_tail_gap(t_true, th_true, t_fin, th_fin)
            retention = tail_gap / (full_gap + 1e-300)
            verdict = int(full_gap > 0.35 and tail_gap > 0.20 and retention > 0.35)
            active += verdict
            total += 1
            print(
                f"[{window[0]:.0f},{window[1]:.0f}] {sigma:.2f} {full_gap:.4f} "
                f"{tail_gap:.4f} {retention:.3f} {core_frac:.3f} {verdict}"
            )
    print(f"ACTIVE_CONTEXTS {active}/{total}")


def main() -> None:
    node_cryptic_allostery()
    transfer_atlas()


if __name__ == "__main__":
    main()
