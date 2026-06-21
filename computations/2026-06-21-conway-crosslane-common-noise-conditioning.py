#!/usr/bin/env python3
"""Common-noise conditioning gate for cross-lane phase kernels."""

from __future__ import annotations

import importlib.util
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-holonomy-full-kernel.py")
spec = importlib.util.spec_from_file_location("holonomy_full_kernel", BASE)
holonomy_full_kernel = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(holonomy_full_kernel)


def offdiag_l1(matrix: np.ndarray) -> float:
    off = matrix.copy()
    np.fill_diagonal(off, 0.0)
    return float(np.sum(np.abs(off)))


def mean_offdiag_corr(samples: np.ndarray) -> float:
    corr = np.corrcoef(samples.T)
    off = corr.copy()
    np.fill_diagonal(off, np.nan)
    return float(np.nanmean(off))


def node_common_noise_sde(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    steps = 20_000
    particles = 60
    common_sigma = 0.80
    private_sigma = 0.60

    common_increments = rng.normal(0.0, 1.0, size=steps)
    private_increments = rng.normal(0.0, 1.0, size=(steps, particles))
    increments = (
        common_sigma * common_increments[:, None]
        + private_sigma * private_increments
    )
    conditioned = increments - common_sigma * common_increments[:, None]

    print("NODE: common-noise SDE conditional independence")
    print(
        f"particles={particles} steps={steps} "
        f"common_sigma={common_sigma:.2f} private_sigma={private_sigma:.2f}"
    )
    print(
        f"unconditional_mean_pair_corr={mean_offdiag_corr(increments):+.4f} "
        f"conditioned_mean_pair_corr={mean_offdiag_corr(conditioned):+.4f}"
    )
    print(
        "constraint: particles become approximately independent only after the "
        "shared noise path is conditioned out"
    )
    print()


def fit_kernel(x: np.ndarray, y: np.ndarray, ridge: float = 0.08) -> np.ndarray:
    x_aug = np.c_[x, np.ones(len(x))]
    eye = np.eye(x_aug.shape[1])
    eye[-1, -1] = 0.0
    coef = np.linalg.solve(x_aug.T @ x_aug + ridge * eye, x_aug.T @ y)
    return coef[:-1].T


def residualize_common_field(values: np.ndarray) -> np.ndarray:
    common = values.mean(axis=1, keepdims=True)
    design = np.c_[np.ones(len(values)), common[:, 0]]
    beta, *_ = np.linalg.lstsq(design, values, rcond=None)
    return values - design @ beta


def kernel_pair(events: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    x = events[:-1].astype(float)
    y = events[1:].astype(float)
    raw = fit_kernel(x, y)

    x_conditioned = residualize_common_field(x)
    y_conditioned = residualize_common_field(y)
    conditioned = fit_kernel(x_conditioned, y_conditioned)
    return raw, conditioned


def transfer_cross_lane_conditioning() -> None:
    print("TRANSFER: ResearchNode #26 cross-lane kernel K(sigma,sigma')")
    print(
        "method #11 run experiments: compare raw directed kernel with kernel after "
        "conditioning on the shared per-time event field"
    )
    print(
        "kind window q density raw_offdiag conditioned_offdiag retention common_share"
    )

    rows: list[tuple[float, tuple[float, float], str, float, float]] = []
    for q in [0.80, 0.88, 0.92]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            for kind in ["true", "finite", "random"]:
                events = holonomy_full_kernel.phase_events(
                    kind,
                    window,
                    q,
                    88000 + int(window[0]) + int(q * 100) + len(kind),
                )
                raw, conditioned = kernel_pair(events)
                raw_mass = offdiag_l1(raw)
                conditioned_mass = offdiag_l1(conditioned)
                retention = conditioned_mass / raw_mass if raw_mass else 0.0
                common_share = 1.0 - retention
                rows.append((q, window, kind, raw_mass, conditioned_mass))
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {q:.2f} "
                    f"{float(events.mean()):.3f} {raw_mass:.3f} "
                    f"{conditioned_mass:.3f} {retention:.3f} {common_share:.3f}"
                )

    print()
    print("TRUE/FINITE SEPARATION RATIOS")
    for q in [0.80, 0.88, 0.92]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            record = {
                kind: (raw, conditioned)
                for qq, ww, kind, raw, conditioned in rows
                if qq == q and ww == window
            }
            raw_ratio = record["true"][0] / record["finite"][0]
            conditioned_ratio = record["true"][1] / record["finite"][1]
            print(
                f"[{window[0]:.0f},{window[1]:.0f}] q={q:.2f} "
                f"raw_true_over_finite={raw_ratio:.3f} "
                f"conditioned_true_over_finite={conditioned_ratio:.3f}"
            )

    print()
    print("GATE SUMMARY")
    print(
        "raw cross-lane offdiag mass mixes direct lane memory with a common event-field mode"
    )
    print(
        "a cross-lane passport must report both raw and common-conditioned kernels; "
        "otherwise common-mode phase shocks can masquerade as sigma-to-sigma coupling"
    )


def main() -> None:
    node_common_noise_sde()
    transfer_cross_lane_conditioning()


if __name__ == "__main__":
    main()
