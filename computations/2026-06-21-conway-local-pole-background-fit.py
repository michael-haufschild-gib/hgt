#!/usr/bin/env python3
"""Workflow pass: enhancer-shaped bursts -> local pole detector with background."""

from __future__ import annotations

import importlib.util
import math
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-poincare-contour-root-gate.py")
spec = importlib.util.spec_from_file_location("root_gate", BASE)
root_gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(root_gate)


def node_enhancer_bursts(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    n = 500
    promoter = rng.random(n) < 0.18
    enhancer = np.zeros(n, dtype=bool)
    state = False
    for i in range(n):
        if rng.random() < (0.05 if not state else 0.12):
            state = not state
        enhancer[i] = state
    bursts = promoter & (rng.random(n) < np.where(enhancer, 0.82, 0.18))
    print("NODE: transcriptional bursts can be shaped by enhancer dynamics, not only promoter switching")
    print(
        "NODE_ROW",
        f"promoter_on_frac={float(np.mean(promoter)):.3f}",
        f"enhancer_on_frac={float(np.mean(enhancer)):.3f}",
        f"burst_if_enhancer_on={float(np.mean(bursts[enhancer])):.3f}",
        f"burst_if_enhancer_off={float(np.mean(bursts[~enhancer])):.3f}",
    )


def sample_annulus(center: complex, radius: float, n_angles: int = 72) -> np.ndarray:
    angles = np.linspace(0.0, 2 * math.pi, n_angles, endpoint=False)
    return np.asarray([center + radius * complex(math.cos(a), math.sin(a)) for a in angles])


def fit_residual(points: np.ndarray, values: np.ndarray, rho: complex, mode: str) -> float:
    z = points - rho
    if np.any(np.abs(z) < 1e-8):
        return float("inf")
    if mode == "pole":
        cols = [1.0 / z]
    elif mode == "pole_const":
        cols = [1.0 / z, np.ones_like(z)]
    elif mode == "pole_affine":
        cols = [1.0 / z, np.ones_like(z), z]
    else:
        raise ValueError(mode)
    a = np.column_stack(cols)
    coef, *_ = np.linalg.lstsq(a, values, rcond=None)
    resid = values - a @ coef
    return float(np.linalg.norm(resid) / max(np.linalg.norm(values), 1e-300))


def best_center(points: np.ndarray, values: np.ndarray, true_center: complex, mode: str) -> tuple[complex, float]:
    best = (0j, float("inf"))
    for dx in np.linspace(-0.012, 0.012, 25):
        for dt in np.linspace(-0.012, 0.012, 25):
            rho = true_center + complex(float(dx), float(dt))
            r = fit_residual(points, values, rho, mode)
            if r < best[1]:
                best = (rho, r)
    return best


def transfer_local_detection() -> None:
    print()
    print("TRANSFER: ResearchNode #19 local pole detection")
    print("method #14 weaken: local pole detection should fit pole plus smooth background, not a naked pole")
    zero = complex(0.5, 14.134725141734693790457251983562)

    # Synthetic enhancer/background check.
    points = sample_annulus(zero, 0.045)
    distal = zero + complex(0.18, 0.05)
    synthetic = 1.0 / (points - zero) + 0.23 / (points - distal) + 0.35 + 0.20 * (points - zero)
    print("synthetic mode center_error residual")
    for mode in ["pole", "pole_const", "pole_affine"]:
        rho, resid = best_center(points, synthetic, zero, mode)
        print(f"synthetic {mode:11s} {abs(rho - zero):.5f} {resid:.5f}")

    # Xi local check on an annulus: no zero location is used in the values, only
    # in measuring the resulting center error for this experiment.
    values = np.asarray([complex(root_gate.xi_log_deriv(z)) for z in points])
    print("xi mode center_error residual")
    for mode in ["pole", "pole_const", "pole_affine"]:
        rho, resid = best_center(points, values, zero, mode)
        print(f"xi        {mode:11s} {abs(rho - zero):.5f} {resid:.5f}")


def main() -> None:
    node_enhancer_bursts()
    transfer_local_detection()


if __name__ == "__main__":
    main()
