#!/usr/bin/env python3
"""Workflow pass: full multivariate kernel vs pairwise phase-event tests."""

from __future__ import annotations

import importlib.util
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-thin-bridge-sampling.py")
spec = importlib.util.spec_from_file_location("thin_bridge", BASE)
thin_bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(thin_bridge)


def node_multivariate_hawkes(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    n = 6000
    x = np.zeros((n, 3), dtype=float)
    # Row = source lane at time t, column = target lane at time t+1.
    kernel = np.array([[0.05, 0.35, 0.00], [0.00, 0.05, 0.35], [0.00, 0.00, 0.05]])
    base = np.array([0.03, 0.02, 0.02])
    for t in range(n - 1):
        p = np.clip(base + x[t] @ kernel, 0.0, 0.85)
        x[t + 1] = rng.random(3) < p
    pair = np.corrcoef(x.T)
    # Full least-squares kernel recovers direct lagged influence; pairwise correlation
    # makes lane 1 and 3 look connected through the 1->2->3 cascade.
    a = np.c_[x[:-1], np.ones(n - 1)]
    coef, *_ = np.linalg.lstsq(a, x[1:], rcond=None)
    k_hat = coef[:-1].T
    print("NODE: multivariate Hawkes requires the full kernel matrix")
    print(
        "NODE_ROW",
        f"pair_corr_1_3={pair[0,2]:.3f}",
        f"direct_kernel_1_3={k_hat[2,0]:.3f}",
        f"direct_kernel_1_2={k_hat[1,0]:.3f}",
        f"direct_kernel_2_3={k_hat[2,1]:.3f}",
    )


def phase_events(kind: str, window: tuple[float, float], q: float, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    sigmas = np.linspace(0.25, 0.90, 10)
    ts = np.linspace(window[0], window[1], 520)
    primes = thin_bridge.first_primes(160)
    values = np.zeros((len(ts), len(sigmas)))
    for j, t in enumerate(ts):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            g = thin_bridge.gamma_part(s)
            p = thin_bridge.component(kind, s, primes, rng)
            values[j, i] = thin_bridge.phase_defect(g, p)
    thresholds = np.quantile(values, q, axis=0)
    return values >= thresholds


def full_kernel(events: np.ndarray, ridge: float = 0.08) -> np.ndarray:
    x = events[:-1].astype(float)
    y = events[1:].astype(float)
    x_aug = np.c_[x, np.ones(len(x))]
    eye = np.eye(x_aug.shape[1])
    eye[-1, -1] = 0.0
    coef = np.linalg.solve(x_aug.T @ x_aug + ridge * eye, x_aug.T @ y)
    return coef[:-1].T


def pairwise_edges(events: np.ndarray, threshold: float = 0.055) -> int:
    x = events[:-1].astype(float)
    y = events[1:].astype(float)
    count = 0
    for i in range(x.shape[1]):
        for j in range(y.shape[1]):
            if i == j:
                continue
            if abs(np.corrcoef(x[:, i], y[:, j])[0, 1]) > threshold:
                count += 1
    return count


def transfer_full_kernel() -> None:
    print()
    print("TRANSFER: ResearchNode #4/#5/#6 holonomy/cross-lane kernel")
    print("method #18 look for the right theorem: use full directed excitation kernel, not pairwise co-event tests")
    print("kind window q event_density pair_edges spectral_radius offdiag_l1 asymmetry rank2_energy")
    for q in [0.80, 0.88]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            for kind in ["true", "finite", "random"]:
                ev = phase_events(kind, window, q, 66000 + int(window[0]) + int(100 * q) + len(kind))
                k = full_kernel(ev)
                eig = np.linalg.eigvals(k)
                off = k.copy()
                np.fill_diagonal(off, 0.0)
                _, svals, _ = np.linalg.svd(off, full_matrices=False)
                rank2 = float(np.sum(svals[:2] ** 2) / (np.sum(svals ** 2) + 1e-300))
                asym = float(np.sum(np.abs(off - off.T)) / (np.sum(np.abs(off)) + 1e-300))
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {q:.2f} "
                    f"{float(np.mean(ev)):.3f} {pairwise_edges(ev):02d} "
                    f"{float(np.max(np.abs(eig))):.3f} {float(np.sum(np.abs(off))):.3f} "
                    f"{asym:.3f} {rank2:.3f}"
                )


def main() -> None:
    node_multivariate_hawkes()
    transfer_full_kernel()


if __name__ == "__main__":
    main()
