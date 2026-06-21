#!/usr/bin/env python3
"""Workflow pass: path-dependent reinforcement as a holonomy-class gate."""

from __future__ import annotations

import importlib.util
import math
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-thin-bridge-sampling.py")
spec = importlib.util.spec_from_file_location("thin_bridge", BASE)
thin_bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(thin_bridge)


def node_polya(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)

    def run(red0: int, blue0: int, trials: int = 500, reps: int = 400) -> np.ndarray:
        out = []
        for _ in range(reps):
            red = red0
            blue = blue0
            for _ in range(trials):
                if rng.random() < red / (red + blue):
                    red += 1
                else:
                    blue += 1
            out.append(red / (red + blue))
        return np.asarray(out)

    neutral = run(1, 1)
    red_shock = run(3, 1)
    blue_shock = run(1, 3)
    print("NODE: small initial advantages compound through reinforcement")
    print(
        "NODE_ROW",
        f"neutral_mean={neutral.mean():.3f}",
        f"red_shock_mean={red_shock.mean():.3f}",
        f"blue_shock_mean={blue_shock.mean():.3f}",
        f"red_minus_blue={red_shock.mean() - blue_shock.mean():.3f}",
        f"red_q10_q90=({np.quantile(red_shock, 0.1):.3f},{np.quantile(red_shock, 0.9):.3f})",
    )


def dlog_xi(s: complex) -> complex:
    return thin_bridge.gamma_part(s) + thin_bridge.dlog_zeta(s)


def side_points(side: int, n: int, sigma0: float, sigma1: float, t0: float, t1: float) -> tuple[np.ndarray, np.ndarray]:
    u = np.linspace(0.0, 1.0, max(2, n), endpoint=True)
    if side == 0:  # bottom, left to right
        s = sigma0 + (sigma1 - sigma0) * u + 1j * t0
        ds = np.full_like(s, (sigma1 - sigma0) / (len(u) - 1), dtype=complex)
    elif side == 1:  # right, bottom to top
        s = sigma1 + 1j * (t0 + (t1 - t0) * u)
        ds = np.full_like(s, 1j * (t1 - t0) / (len(u) - 1), dtype=complex)
    elif side == 2:  # top, right to left
        s = sigma1 - (sigma1 - sigma0) * u + 1j * t1
        ds = np.full_like(s, -(sigma1 - sigma0) / (len(u) - 1), dtype=complex)
    elif side == 3:  # left, top to bottom
        s = sigma0 + 1j * (t1 - (t1 - t0) * u)
        ds = np.full_like(s, -1j * (t1 - t0) / (len(u) - 1), dtype=complex)
    else:
        raise ValueError(side)
    ds[0] *= 0.5
    ds[-1] *= 0.5
    return s, ds


def contour_measure(budgets: list[int], window: tuple[float, float]) -> dict[str, object]:
    sigma0, sigma1 = 0.2, 0.8
    t0, t1 = window
    integrals = []
    raw_masses = []
    mean_masses = []
    for side, n in enumerate(budgets):
        pts, ds = side_points(side, n, sigma0, sigma1, t0, t1)
        vals = np.asarray([dlog_xi(complex(z)) for z in pts])
        integrals.append(np.sum(vals * ds))
        mag = np.abs(vals)
        raw_masses.append(float(np.sum(mag)))
        mean_masses.append(float(np.mean(mag)))
    total_int = complex(np.sum(integrals))
    raw = np.asarray(raw_masses)
    mean = np.asarray(mean_masses)
    return {
        "winding_like": total_int / (2j * math.pi),
        "raw_shape": raw / raw.sum(),
        "mean_shape": mean / mean.sum(),
    }


def polya_budgets(seed: int, early_side: int, total: int = 720, base: int = 2) -> list[int]:
    rng = np.random.default_rng(seed)
    counts = np.full(4, base, dtype=int)
    counts[early_side] += 2
    while counts.sum() < total:
        side = int(rng.choice(4, p=counts / counts.sum()))
        counts[side] += 1
    return counts.tolist()


def l1(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.sum(np.abs(a - b)))


def transfer_holonomy() -> None:
    print()
    print("TRANSFER: ResearchNode #4/#5/#6 cohomology of carrier holonomy modulo passport")
    print(
        "method #20 name the missing lemma: a Master-1 holonomy class must be invariant under refinement history, "
        "not only under total passport size"
    )
    windows = [(100.0, 170.0), (500.0, 570.0)]
    print("window schedule budgets winding_real winding_imag raw_L1_vs_uniform mean_L1_vs_uniform")
    for window in windows:
        uniform_budget = [180, 180, 180, 180]
        ref = contour_measure(uniform_budget, window)
        for name, budgets in [
            ("uniform", uniform_budget),
            ("bottom_shock", polya_budgets(301 + int(window[0]), 0)),
            ("right_shock", polya_budgets(302 + int(window[0]), 1)),
            ("top_shock", polya_budgets(303 + int(window[0]), 2)),
            ("left_shock", polya_budgets(304 + int(window[0]), 3)),
        ]:
            m = contour_measure(budgets, window)
            wind = m["winding_like"]
            print(
                f"[{window[0]:.0f},{window[1]:.0f}] {name:12s} {budgets} "
                f"{wind.real:+.4f} {wind.imag:+.4f} "
                f"{l1(m['raw_shape'], ref['raw_shape']):.3f} {l1(m['mean_shape'], ref['mean_shape']):.3f}"
            )


def main() -> None:
    node_polya()
    transfer_holonomy()


if __name__ == "__main__":
    main()
