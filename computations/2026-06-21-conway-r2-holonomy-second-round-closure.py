#!/usr/bin/env python3
"""Run-2 finding 52 candidate: second-round closure for holonomy kernels."""

from __future__ import annotations

import importlib.util
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-holonomy-full-kernel.py")
spec = importlib.util.spec_from_file_location("holonomy_kernel", BASE)
holonomy_kernel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(holonomy_kernel)


def spectral_radius(a: np.ndarray) -> float:
    return float(np.max(np.abs(np.linalg.eigvals(a))))


def node_stress_test_feedback(seed: int = 20260621) -> None:
    """Validate the NODE: first-round portfolio stress misses feedback losses."""
    rng = np.random.default_rng(seed)
    n_assets = 12
    raw = rng.gamma(shape=1.5, scale=0.25, size=(n_assets, n_assets))
    np.fill_diagonal(raw, 0.0)
    base = rng.uniform(0.01, 0.04, size=n_assets)

    print("NODE: second-round redemptions/deleveraging/collateral chains break first-round stress")
    print("target_rho first_loss closed_loss amplification max_asset_loss")
    for target_rho in [0.10, 0.35, 0.60, 0.82, 0.94]:
        a = raw * (target_rho / spectral_radius(raw))
        closed = np.linalg.solve(np.eye(n_assets) - a, base)
        print(
            f"{target_rho:.2f} {float(base.sum()):.4f} {float(closed.sum()):.4f} "
            f"{float(closed.sum() / base.sum()):.2f} {float(np.max(closed)):.4f}"
        )
    print("constraint: the right theorem is the Leontief/resolvent stability condition rho(A)<1")


def signed_closure_gain(k: np.ndarray) -> float:
    b = np.abs(np.diag(k)) + 1e-6
    y = np.linalg.solve(np.eye(k.shape[0]) - k, b)
    return float(np.linalg.norm(y) / np.linalg.norm(b))


def positive_closure_status(k: np.ndarray) -> tuple[float, str]:
    off = np.maximum(k, 0.0)
    np.fill_diagonal(off, 0.0)
    rho = spectral_radius(off)
    status = "stable" if rho < 1.0 else "supercritical"
    return rho, status


def transfer_holonomy_closure() -> None:
    """Transfer: one-step kernels need a second-round closure passport."""
    print()
    print("TRANSFER: ResearchNode #19 carrier-holonomy cohomology")
    print(
        "method #18 look for the right theorem: Leontief/Perron-Frobenius closure, "
        "not only one-step signed kernel mass"
    )
    print(
        "kind window q signed_rho signed_gain positive_rho positive_status "
        "offdiag_l1 diag_mean"
    )
    for q in [0.80, 0.88, 0.93]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            for kind in ["true", "finite", "random"]:
                seed = 88000 + int(window[0]) + int(100 * q) + len(kind)
                events = holonomy_kernel.phase_events(kind, window, q, seed)
                k = holonomy_kernel.full_kernel(events)
                off = k.copy()
                np.fill_diagonal(off, 0.0)
                pos_rho, status = positive_closure_status(k)
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {q:.2f} "
                    f"{spectral_radius(k):.3f} {signed_closure_gain(k):.3f} "
                    f"{pos_rho:.3f} {status:13s} "
                    f"{float(np.sum(np.abs(off))):.3f} {float(np.mean(np.abs(np.diag(k)))):.3f}"
                )
    print()
    print("GATE SUMMARY")
    print(
        "a Master-1 kernel can look signed-stable while its positive second-round "
        "feedback closure is supercritical"
    )
    print(
        "report the closure passport rho(K_+) and finite/random controls before treating "
        "a one-step event kernel as cohomology content"
    )


def main() -> None:
    node_stress_test_feedback()
    transfer_holonomy_closure()


if __name__ == "__main__":
    main()
