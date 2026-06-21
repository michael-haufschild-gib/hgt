#!/usr/bin/env python3
"""Workflow pass: strange-attractor recurrence for zero-shadow topology."""

from __future__ import annotations

import importlib.util
import math
import pathlib
from dataclasses import dataclass

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-thin-bridge-sampling.py")
spec = importlib.util.spec_from_file_location("thin_bridge", BASE)
thin_bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(thin_bridge)


def lorenz_step(x: np.ndarray, dt: float = 0.01) -> np.ndarray:
    sigma = 10.0
    rho = 28.0
    beta = 8.0 / 3.0

    def f(v: np.ndarray) -> np.ndarray:
        return np.array(
            [
                sigma * (v[1] - v[0]),
                v[0] * (rho - v[2]) - v[1],
                v[0] * v[1] - beta * v[2],
            ],
            dtype=float,
        )

    k1 = f(x)
    k2 = f(x + 0.5 * dt * k1)
    k3 = f(x + 0.5 * dt * k2)
    k4 = f(x + dt * k3)
    return x + dt * (k1 + 2 * k2 + 2 * k3 + k4) / 6.0


def lorenz_trace(x0: np.ndarray, steps: int = 6000, burn: int = 1000) -> np.ndarray:
    x = x0.astype(float).copy()
    out = []
    for i in range(steps + burn):
        x = lorenz_step(x)
        if i >= burn:
            out.append(x.copy())
    return np.asarray(out)


def node_strange_attractor(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    a = lorenz_trace(np.array([1.0, 1.0, 1.0]))
    b = lorenz_trace(np.array([1.0 + 1e-7, 1.0, 1.0]))
    d = np.linalg.norm(a[:1200] - b[:1200], axis=1)
    usable = (d > 1e-8) & (d < 10.0)
    t = np.arange(len(d))[usable] * 0.01
    lyap_slope = float(np.polyfit(t, np.log(d[usable]), 1)[0])

    lo = a.min(axis=0)
    hi = a.max(axis=0)
    iid = rng.uniform(lo, hi, size=a.shape)
    bins = 18
    scale = np.maximum(hi - lo, 1e-12)
    box_a = np.floor((a - lo) / scale * bins).clip(0, bins - 1).astype(int)
    box_iid = np.floor((iid - lo) / scale * bins).clip(0, bins - 1).astype(int)
    key_a = box_a[:, 0] * bins * bins + box_a[:, 1] * bins + box_a[:, 2]
    key_iid = box_iid[:, 0] * bins * bins + box_iid[:, 1] * bins + box_iid[:, 2]
    occ_a = len(set(map(int, key_a)))
    occ_iid = len(set(map(int, key_iid)))
    recurrence_a = 1.0 - occ_a / len(key_a)
    recurrence_iid = 1.0 - occ_iid / len(key_iid)

    print("NODE: strange attractor constraint")
    print(
        "Lorenz has exponential separation but bounded recurring structure:",
        f"lyap_slope={lyap_slope:.3f}",
        f"range_x=({lo[0]:.2f},{hi[0]:.2f})",
        f"range_z=({lo[2]:.2f},{hi[2]:.2f})",
    )
    print(
        "NODE_ROW",
        f"lorenz_boxes={occ_a}",
        f"iid_boxes={occ_iid}",
        f"lorenz_recurrence={recurrence_a:.3f}",
        f"iid_recurrence={recurrence_iid:.3f}",
    )


@dataclass
class ProfileMetrics:
    occupied: float
    components: float
    span_t: float
    unique_profiles: int
    recurrence: float
    nn_next_error: float
    shuffled_next_error: float
    dependency_gain: float
    mean_profile_jump: float


def hamming(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.mean(a != b))


def nearest_next_error(profiles: np.ndarray) -> float:
    n = len(profiles)
    if n < 4:
        return float("nan")
    errors = []
    for i in range(n - 1):
        best_j = None
        best_d = float("inf")
        for j in range(n - 1):
            if abs(i - j) <= 1:
                continue
            d = hamming(profiles[i], profiles[j])
            if d < best_d:
                best_d = d
                best_j = j
        if best_j is not None:
            errors.append(hamming(profiles[i + 1], profiles[best_j + 1]))
    return float(np.mean(errors)) if errors else float("nan")


def profile_metrics(mask: np.ndarray, seed: int) -> ProfileMetrics:
    # Columns are time profiles across sigma lanes.
    profiles = mask.T.astype(np.uint8)
    rng = np.random.default_rng(seed)
    shuffled = profiles.copy()
    rng.shuffle(shuffled, axis=0)
    st = thin_bridge.bridge_stats(mask)
    uniq = {tuple(map(int, row)) for row in profiles}
    recurrence = 1.0 - len(uniq) / max(1, len(profiles))
    nn_err = nearest_next_error(profiles)
    shuf_err = nearest_next_error(shuffled)
    jumps = [hamming(profiles[i], profiles[i + 1]) for i in range(len(profiles) - 1)]
    return ProfileMetrics(
        occupied=st["occupied"],
        components=st["components"],
        span_t=st["span_t"],
        unique_profiles=len(uniq),
        recurrence=recurrence,
        nn_next_error=nn_err,
        shuffled_next_error=shuf_err,
        dependency_gain=shuf_err - nn_err,
        mean_profile_jump=float(np.mean(jumps)) if jumps else float("nan"),
    )


def mask_for(kind: str, window: tuple[float, float], threshold: float, seed: int) -> np.ndarray:
    sigmas = np.linspace(0.2, 0.9, 17)
    ts = np.linspace(window[0], window[1], 180)
    primes = thin_bridge.first_primes(160)
    rng = np.random.default_rng(seed)
    return thin_bridge.zero_shadow_mask(kind, sigmas, ts, primes, rng, threshold)


def transfer_zero_shadow() -> None:
    print()
    print("TRANSFER: ResearchNode 27 zero-shadow topology")
    print(
        "method #21 build dependency chain: full span is not enough; require bounded irregular "
        "zero-shadow masks to have profile recurrence and one-step dependency beyond time-shuffle controls"
    )
    print(
        "kind window threshold occupied components span_t unique_profiles recurrence "
        "nn_next_error shuffled_next_error dependency_gain mean_profile_jump"
    )
    for threshold in [0.85, 1.00, 1.15]:
        for window in [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]:
            for kind in ["true", "finite", "random"]:
                seed = 20260621 + int(window[0]) + int(100 * threshold) + {"true": 1, "finite": 2, "random": 3}[kind]
                m = profile_metrics(mask_for(kind, window, threshold, seed), seed + 17)
                print(
                    f"{kind:6s} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} "
                    f"{m.occupied:.3f} {m.components:.0f} {m.span_t:.0f} {m.unique_profiles:03d} "
                    f"{m.recurrence:.3f} {m.nn_next_error:.3f} {m.shuffled_next_error:.3f} "
                    f"{m.dependency_gain:+.3f} {m.mean_profile_jump:.3f}"
                )


def main() -> None:
    node_strange_attractor()
    transfer_zero_shadow()


if __name__ == "__main__":
    main()
