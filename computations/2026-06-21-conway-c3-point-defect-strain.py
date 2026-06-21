#!/usr/bin/env python3
"""Workflow pass: split C3 phase-Sobolev into point-defect core and tail."""

from __future__ import annotations

import math
import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-hawkes-edge-c3.py")
phase_series = BASE["phase_series"]


def node_strain_field(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    n = 240
    x = np.linspace(-1.0, 1.0, n)
    y = np.linspace(-1.0, 1.0, n)
    xx, yy = np.meshgrid(x, y)
    centers = rng.uniform(-0.55, 0.55, size=(5, 2))
    field = np.zeros_like(xx)
    core = np.zeros_like(xx, dtype=bool)
    for cx, cy in centers:
        r2 = (xx - cx) ** 2 + (yy - cy) ** 2
        field += np.exp(-r2 / 0.004) + 0.08 / np.sqrt(r2 + 0.006)
        core |= r2 < 0.018
    total = float(np.sum(field * field))
    core_energy = float(np.sum(field[core] ** 2))
    tail_energy = total - core_energy
    print("NODE: strain fields around point-defect clusters")
    print(
        "NODE_ROW",
        f"defects={len(centers)}",
        f"core_area={float(np.mean(core)):.3f}",
        f"core_energy_frac={core_energy / total:.3f}",
        f"tail_energy_frac={tail_energy / total:.3f}",
    )
    print("constraint: a bulk strain statistic must split defect-core energy from elastic-tail energy")


def energy_trace(t: np.ndarray, theta: np.ndarray) -> np.ndarray:
    dtheta = np.gradient(theta, t)
    return dtheta * dtheta


def dilate(mask: np.ndarray, radius: int) -> np.ndarray:
    out = mask.copy()
    for shift in range(1, radius + 1):
        out[:-shift] |= mask[shift:]
        out[shift:] |= mask[:-shift]
    return out


def core_mask(energy: np.ndarray, q: float, radius: int) -> np.ndarray:
    threshold = float(np.quantile(energy, 1.0 - q))
    return dilate(energy >= threshold, radius)


def rms_energy(t: np.ndarray, energy: np.ndarray, mask: np.ndarray | None = None) -> float:
    if mask is None:
        mask = np.ones_like(energy, dtype=bool)
    if np.sum(mask) < 4:
        return float("nan")
    return math.sqrt(float(np.mean(energy[mask])))


def transfer_c3() -> None:
    print()
    print("TRANSFER: ResearchNode #25 phase-Sobolev guard-band / regularity functional")
    print("method #1 split into subclaims: full H1 gap, point-defect core, residual tail")
    rng = np.random.default_rng(260621901)
    cases = [
        ("zero_strip", 0.50, (14.0, 84.0)),
        ("critical_low", 0.50, (100.0, 170.0)),
        ("critical_high", 0.50, (500.0, 570.0)),
        ("right_low", 1.30, (100.0, 170.0)),
    ]
    print(
        "case q core_frac true_full finite_full full_gap true_tail finite_tail "
        "tail_gap tail_retention true_core_energy_frac"
    )
    for label, sigma, window in cases:
        series = {}
        for kind in ["true", "finite", "random_phase"]:
            t, theta = phase_series(kind, sigma, window, 900, rng)
            series[kind] = (t, energy_trace(t, theta))
        true_t, true_energy = series["true"]
        true_full = rms_energy(true_t, true_energy)
        finite_full = rms_energy(series["finite"][0], series["finite"][1])
        full_gap = abs(true_full - finite_full)
        for q in [0.02, 0.05, 0.10]:
            cmask = core_mask(true_energy, q=q, radius=4)
            tail = ~cmask
            true_tail = rms_energy(true_t, true_energy, tail)
            finite_tail = rms_energy(series["finite"][0], series["finite"][1], tail)
            tail_gap = abs(true_tail - finite_tail)
            core_frac = float(np.mean(cmask))
            core_energy_frac = float(np.sum(true_energy[cmask]) / (np.sum(true_energy) + 1e-300))
            print(
                f"{label:13s} {q:.2f} {core_frac:.3f} {true_full:.4f} {finite_full:.4f} "
                f"{full_gap:.4f} {true_tail:.4f} {finite_tail:.4f} {tail_gap:.4f} "
                f"{tail_gap / (full_gap + 1e-300):.3f} {core_energy_frac:.3f}"
            )


def main() -> None:
    node_strain_field()
    transfer_c3()


if __name__ == "__main__":
    main()
