#!/usr/bin/env python3
"""R60: coarse-graining warning for the Berry seam layer.

NODE: coarse-graining can erase microscopic determinism or introduce artifacts.

Target: Berry seam layer.  Weakened transfer: do not average the two mirror
lanes before reading relative phase; completion equalizes magnitudes, so the
remaining information is carried by the lane-resolved phase.
"""

from __future__ import annotations

from math import atan2, cos, log, pi
from statistics import mean, median
from typing import List, Tuple

import mpmath as mp
import numpy as np

mp.mp.dps = 35


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_validation() -> None:
    print("\nNODE validation: deterministic CA looks different after coarse-graining")
    n = 121
    state = np.zeros(n, dtype=np.uint8)
    state[n // 2] = 1
    densities = []
    block_entropies = []
    for _ in range(36):
        blocks = state.reshape(-1, 11)
        block_density = blocks.mean(axis=1)
        densities.append(float(state.mean()))
        p = np.clip(block_density, 1e-12, 1 - 1e-12)
        block_entropies.append(float(np.mean(-(p * np.log2(p) + (1 - p) * np.log2(1 - p)))))
        left = np.roll(state, 1)
        right = np.roll(state, -1)
        state = left ^ right  # Rule 90, deterministic.
    print(f"  microscopic rule: Rule 90 from one seed, deterministic XOR update")
    print(f"  density range over time: {min(densities):.4f}..{max(densities):.4f}")
    print(f"  block entropy range     : {min(block_entropies):.4f}..{max(block_entropies):.4f}")


def zeta_log_derivative(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(mp.diff(mp.zeta, smp) / mp.zeta(smp))


def arch_term_xi(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(
        1 / smp
        + 1 / (smp - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(smp / 2) / 2
    )


def completed_log_derivative(s: complex) -> complex:
    return arch_term_xi(s) + zeta_log_derivative(s)


def angle(z: complex) -> float:
    return atan2(z.imag, z.real)


def wrap(x: float) -> float:
    while x <= -pi:
        x += 2 * pi
    while x > pi:
        x -= 2 * pi
    return x


def berry_lane_stats(window: Tuple[float, float], delta: float, points: int = 36) -> Tuple[float, float, float, float]:
    rel_phases: List[float] = []
    mag_imbalances: List[float] = []
    coarse_mags: List[float] = []
    mean_lane_mags: List[float] = []
    lo, hi = window
    for j in range(points):
        t = lo + (hi - lo) * j / (points - 1)
        left = completed_log_derivative(complex(0.5 - delta, t))
        right = completed_log_derivative(complex(0.5 + delta, t))
        rel_phases.append(abs(wrap(angle(right) - angle(left))))
        mag_imbalances.append(abs(log(max(abs(right), 1e-300)) - log(max(abs(left), 1e-300))))
        coarse_mags.append(abs(0.5 * (left + right)))
        mean_lane_mags.append(0.5 * (abs(left) + abs(right)))
    cancellation = [1 - c / max(m, 1e-300) for c, m in zip(coarse_mags, mean_lane_mags)]
    return median(rel_phases), mean(mag_imbalances), median(cancellation), max(cancellation)


def berry_test() -> None:
    print("\nTarget test: Berry lanes before and after coarse-graining")
    print("  window     delta  median_rel_phase  mean_mag_imbalance  median_coarse_cancel  max_cancel")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for delta in [0.05, 0.10, 0.20]:
            rel, imb, canc_med, canc_max = berry_lane_stats(window, delta)
            print(
                f"  {int(window[0]):4d}-{int(window[1]):4d}  {delta:5.2f}      "
                f"{rel:8.4f}          {imb:10.3e}          {canc_med:8.4f}    {canc_max:8.4f}"
            )


def main() -> None:
    node = "coarse-graining can erase microscopic determinism, but it can also introduce artifacts mistaken for physical laws"
    attempts = [
        "coarse-graining mirror lanes erases Berry relative phase",
        "Berry seam must be read before lane averaging",
        "completed lane magnitudes hide phase after coarse-graining",
    ]
    print("R60 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    berry_test()

    print("\nInterpretation:")
    print("  Completion makes mirror-lane magnitudes equal, so lane-averaged scalars")
    print("  erase or distort the remaining Berry relative phase. This is a valid")
    print("  warning, but it is a weakened restatement of the existing Berry seam")
    print("  result rather than a new invariant.")


if __name__ == "__main__":
    main()
