#!/usr/bin/env python3
"""R61: synchronous spectral artifacts as a B2 bridge warning.

NODE: spectral artifacts can appear from synchronous updating in deterministic
cellular automata.

Target: B2 two-lemma bridge.  Minimal counterexample: a source-free oscillatory
artifact can trigger a defect detector on a synchronized grid but disappear
under sampling phase desynchronization.  Therefore B2's "detect" lemma needs a
source-carrying / offset-robust condition, not just a grid-visible signal.
"""

from __future__ import annotations

from math import cos, pi
from random import Random
from statistics import mean
from typing import List, Tuple

import numpy as np


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def rule90_spectrum(width: int = 256, steps: int = 160) -> Tuple[float, float]:
    state = np.zeros(width, dtype=np.uint8)
    state[width // 2] = 1
    center_series = []
    random_projection = []
    rng = np.random.default_rng(61)
    weights = rng.choice([-1.0, 1.0], size=width)
    for _ in range(steps):
        center_series.append(float(state[width // 2]))
        random_projection.append(float(np.dot(weights, state) / width))
        state = np.roll(state, 1) ^ np.roll(state, -1)
    center_fft = np.abs(np.fft.rfft(np.array(center_series) - mean(center_series)))
    proj_fft = np.abs(np.fft.rfft(np.array(random_projection) - mean(random_projection)))
    return float(center_fft.max()), float(proj_fft.max())


def source_free_artifact(t: np.ndarray, update_period: float) -> np.ndarray:
    return np.cos(2 * pi * t / update_period)


def defect_count(offset: float, step: float, update_period: float, threshold: float = 0.98) -> int:
    t = offset + np.arange(80) * step
    signal = source_free_artifact(t, update_period)
    return int(np.sum(signal > threshold))


def b2_minimal_counterexample() -> None:
    update_period = 1.0
    step = 1.0
    rng = Random(610)
    counts = [defect_count(rng.random() * step, step, update_period) for _ in range(200)]
    sync = defect_count(0.0, step, update_period)
    half = defect_count(0.5, step, update_period)
    print("\nTarget minimal counterexample: source-free synchronized defect")
    print(f"  synchronized offset 0       count={sync}")
    print(f"  half-period offset 0.5       count={half}")
    print(f"  random offsets count range   {min(counts)}..{max(counts)}, mean={mean(counts):.3f}")
    print("  true source charge/residue   0 (constructed as a pure oscillatory artifact)")


def main() -> None:
    node = "spectral artifacts can appear from synchronous updating"
    attempts = [
        "B2 defect detectors need sampling-phase robustness",
        "synchronous grid artifacts can fake off-seam transport defects",
        "source-carrying means offset-robust not just grid-visible",
    ]
    print("R61 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    center_peak, projection_peak = rule90_spectrum()
    print("\nNODE validation: Rule-90 synchronous spectral peaks")
    print(f"  center-cell time-series FFT peak      {center_peak:.3f}")
    print(f"  random full-state projection FFT peak {projection_peak:.3f}")

    b2_minimal_counterexample()

    print("\nInterpretation:")
    print("  A grid-visible defect is not yet source-carrying. B2 must require")
    print("  offset/desynchronization robustness or an actual logarithmic residue.")
    print("  This is a useful kill condition, but it repeats prior grid-stability")
    print("  and sampling-alias warnings rather than proving either B2 lemma.")


if __name__ == "__main__":
    main()
