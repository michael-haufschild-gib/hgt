#!/usr/bin/env python3
"""R57: modulation-neutral directions as a faithful-index readout warning.

NODE: singularity/blowup analysis tracks modulation equations for scale,
phase, center, and frequency.

Target: G-C18 faithful-index rigidity.  Weakened transfer: before using a
faithful integer index as the readout, quotient or fix the neutral modulation
directions; otherwise gauge-scale dust can change raw inertia while a measured
trace remains essentially controlled.
"""

from __future__ import annotations

from math import cos, sin, sqrt
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


def blowup_modulation_demo() -> None:
    """A minimal log-log style modulation toy."""
    print("\nNODE validation: four blowup modulation coordinates")
    T = 1.0
    rows = []
    for t in [0.0, 0.5, 0.8, 0.95, 0.99]:
        scale = sqrt(T - t)
        phase_rate = 1.0 / (scale * scale)
        center = 0.1 * sin(phase_rate)
        frequency = 1.0 / scale
        rows.append((t, scale, phase_rate, center, frequency))
    for t, scale, phase_rate, center, frequency in rows:
        print(
            f"  t={t:4.2f}: scale={scale:8.5f}, phase_rate={phase_rate:8.3f}, "
            f"center={center: .5f}, frequency={frequency:8.3f}"
        )


def inertia(vals: np.ndarray, tol: float = 1e-10) -> Tuple[int, int, int]:
    return (
        int(np.sum(vals > tol)),
        int(np.sum(vals < -tol)),
        int(np.sum(np.abs(vals) <= tol)),
    )


def quotient_matrix(Q: np.ndarray, keep: int) -> np.ndarray:
    """Project to the physical block; neutral modes are the final coordinates."""
    return Q[:keep, :keep]


def faithful_index_modulation_demo() -> None:
    physical = np.diag([-0.05, 0.25, 0.55, 0.90])
    keep = physical.shape[0]
    n_neutral = 4
    print("\nTarget test: raw inertia versus modulation-quotiented inertia")
    print("  physical block has one true negative direction; four neutral modulation coordinates carry tiny gauge dust")
    print("  theta    raw_neg  quotient_neg  trace       min_eig       neutral_dust")
    for theta in np.linspace(0, 2 * np.pi, 9):
        dust = 0.015 * np.diag([sin(theta + j * 0.9) for j in range(n_neutral)])
        coupling = np.zeros((keep, n_neutral))
        for j in range(n_neutral):
            coupling[j % keep, j] = 0.006 * cos(theta + j)
        Q = np.block([[physical, coupling], [coupling.T, dust]])
        vals = np.linalg.eigvalsh(Q)
        qvals = np.linalg.eigvalsh(quotient_matrix(Q, keep))
        _, raw_neg, _ = inertia(vals)
        _, quotient_neg, _ = inertia(qvals)
        neutral_signs = "".join("-" if dust[j, j] < 0 else "+" for j in range(n_neutral))
        print(
            f"  {theta:5.2f}      {raw_neg:2d}          {quotient_neg:2d}      "
            f"{np.trace(Q): .6f}  {vals[0]: .6f}       {neutral_signs}"
        )

    print("\nControl: no physical negative direction, only neutral dust")
    positive_physical = np.diag([0.05, 0.25, 0.55, 0.90])
    raw_counts: List[int] = []
    quotient_counts: List[int] = []
    for theta in np.linspace(0, 2 * np.pi, 33):
        dust = 0.015 * np.diag([sin(theta + j * 0.9) for j in range(n_neutral)])
        Q = np.block(
            [
                [positive_physical, np.zeros((keep, n_neutral))],
                [np.zeros((n_neutral, keep)), dust],
            ]
        )
        raw_counts.append(inertia(np.linalg.eigvalsh(Q))[1])
        quotient_counts.append(inertia(np.linalg.eigvalsh(quotient_matrix(Q, keep)))[1])
    print(f"  raw negative-count range from neutral dust: {min(raw_counts)}..{max(raw_counts)}")
    print(f"  quotient negative-count range           : {min(quotient_counts)}..{max(quotient_counts)}")


def main() -> None:
    node = "modulation equations for blowup parameters such as scale, phase, center, and frequency"
    attempts = [
        "modulation-neutral modes must be quotiented before reading faithful index",
        "scale phase center frequency drift creates spurious near-zero index dust",
        "faithful index is stable only after fixing blowup-parameter gauge",
    ]
    print("R57 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    blowup_modulation_demo()
    faithful_index_modulation_demo()

    print("\nInterpretation:")
    print("  The weakened G-C18 gate is a modulation-gauge requirement: an index")
    print("  readout must specify the neutral parameter quotient.  Otherwise tiny")
    print("  scale/phase/center/frequency dust changes raw inertia while trace-level")
    print("  data stay nearly unchanged.  This is useful but generic Morse-index")
    print("  discipline, not a source-built proof of faithful-index rigidity.")


if __name__ == "__main__":
    main()
