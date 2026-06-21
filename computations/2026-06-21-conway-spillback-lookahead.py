#!/usr/bin/env python3
"""THE-MACHINE run: landing spillback masks downstream route choices."""

from __future__ import annotations

import argparse
import math
import runpy
from pathlib import Path

import numpy as np


def load_base():
    remote = Path("/tmp/2026-06-21-conway-kinetic-proofreading-lifetime.py")
    local = Path("computations/2026-06-21-conway-kinetic-proofreading-lifetime.py")
    return runpy.run_path(str(remote if remote.exists() else local))


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = cur
    return prev[-1]


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    n = 20000
    # Two routes: A looks short. When the landing spillback is high, the
    # downstream choice after A is hidden and A is often the wrong route.
    spillback = rng.gamma(shape=2.0, scale=1.0, size=n)
    downstream_blocked = rng.random(n) < np.clip((spillback - 1.0) / 4.0, 0.0, 0.95)
    visible_short = np.ones(n, dtype=bool)
    choose_a_without_visibility = visible_short
    choose_a_with_visibility = visible_short & ~downstream_blocked
    wrong_without = choose_a_without_visibility & downstream_blocked
    wrong_with = choose_a_with_visibility & downstream_blocked
    print("NODE simulation: landing spillback masks downstream route choices")
    print("spillback_bin wrong_no_visibility wrong_with_visibility blocked_rate")
    bins = [(0, 1), (1, 2), (2, 4), (4, 99)]
    for lo, hi in bins:
        idx = (spillback >= lo) & (spillback < hi)
        print(
            f"[{lo},{hi}) {float(np.mean(wrong_without[idx])):.3f} "
            f"{float(np.mean(wrong_with[idx])):.3f} {float(np.mean(downstream_blocked[idx])):.3f}"
        )


def lookahead_metrics(mask: np.ndarray, horizon: int) -> dict[str, float]:
    starts = np.arange(0, len(mask) - horizon + 1)
    displayed = mask[starts]
    downstream = np.array([bool(np.all(mask[i : i + horizon])) for i in starts])
    hidden_fail = displayed & ~downstream
    return {
        "displayed": float(np.mean(displayed)),
        "downstream": float(np.mean(downstream)),
        "hidden_fail": float(np.mean(hidden_fail) / max(np.mean(displayed), 1e-12)),
    }


def ht_run(samples: int, prime_count: int, threshold: float) -> None:
    kernel = "landing spillback masks downstream route choice local visible hidden failure"
    attempts = {
        "A_phase_lookahead_spillback": "local phase cue masks downstream survival choice visible hidden failure",
        "B_amplitude_barrier_occlusion": "local amplitude barrier masks downstream magnitude route visible hidden failure",
        "C_sigma_route_spillback": "sigma route congestion masks downstream strip choice visible hidden failure",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("\nSTEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:30s} distance={dist}")
    print(f"selected={selected}")

    ns = load_base()
    primes = ns["first_primes"](prime_count)
    rng = np.random.default_rng(8901)
    windows = [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]
    print("\nSTEP8/9 HT transfer: local phase cue vs downstream phase availability")
    print(f"samples={samples} threshold={threshold}")
    print("kind sigma horizon displayed downstream hidden_fail")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for kind in ["true", "finite", "random"]:
            masks = []
            for window in windows:
                defects = ns["defects_for"](kind, sigma, window, samples, primes, rng)
                masks.append(defects > threshold)
            for horizon in [2, 4, 8, 16, 32]:
                rows = [lookahead_metrics(mask, horizon) for mask in masks]
                print(
                    f"{kind:6s} {sigma:.1f} {horizon:2d} "
                    f"{float(np.mean([r['displayed'] for r in rows])):.3f} "
                    f"{float(np.mean([r['downstream'] for r in rows])):.3f} "
                    f"{float(np.mean([r['hidden_fail'] for r in rows])):.3f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=520)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=0.0)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count, args.threshold)


if __name__ == "__main__":
    main()
