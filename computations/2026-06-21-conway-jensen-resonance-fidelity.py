#!/usr/bin/env python3
"""Workflow pass: stochastic resonance -> Jensen/Hankel fidelity gate."""

from __future__ import annotations

import math

import numpy as np


def node_stochastic_resonance(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    t = np.linspace(0.0, 80.0, 4000)
    signal = 0.82 * np.sin(2 * math.pi * t / 8.0)
    target = signal > 0.0
    print("NODE: stochastic resonance can improve detectability while degrading waveform fidelity")
    print("noise detection_rate waveform_corr")
    for noise in [0.0, 0.15, 0.30, 0.50, 0.80, 1.20]:
        obs = signal + rng.normal(0.0, noise, size=len(signal))
        detected = obs > 0.95
        # Detection: did each positive half-cycle have at least one threshold crossing?
        cycle = np.floor(t / 8.0).astype(int)
        rates = []
        for c in sorted(set(cycle)):
            m = (cycle == c) & target
            if np.any(m):
                rates.append(float(np.any(detected[m])))
        corr = float(np.corrcoef(signal, obs)[0, 1])
        print(f"{noise:.2f} {np.mean(rates):.3f} {corr:.3f}")


def coeffs() -> np.ndarray:
    # Recorded from computations/2026-06-21-connes-jensen-turan-apexb.txt.
    # Enough precision for the detection-vs-fidelity gate; this script does not
    # certify Jensen positivity.
    return np.asarray(
        [
            4.97121e-1,
            1.149e-2,
            1.235e-4,
            8.324e-7,
            3.992e-9,
            1.462e-11,
            4.275e-14,
            1.031e-16,
            2.100e-19,
            3.678e-22,
            5.623e-25,
            7.592e-28,
            9.143e-31,
            9.906e-34,
        ],
        dtype=float,
    )


def hankel(a: np.ndarray, start: int, size: int) -> np.ndarray:
    return np.asarray([[a[start + i + j] for j in range(size)] for i in range(size)], dtype=float)


def normalized_profile(a: np.ndarray, start: int, size: int) -> np.ndarray:
    vals = a[start : start + 2 * size - 1]
    return vals / max(abs(vals[0]), 1e-300)


def transfer_jensen() -> None:
    print()
    print("TRANSFER: ResearchNode 15 Uniform Jensen/Hankel positivity")
    print("method #11 run experiments: PSD detection can be improved by ridge noise while Hankel fidelity degrades")
    a = coeffs()
    start = 2
    size = 4
    h = hankel(a, start, size)
    base_eigs = np.linalg.eigvalsh(h)
    # Make a near-boundary observed form by a tiny tail perturbation.
    margin = max(abs(float(base_eigs[0])), 1e-12)
    observed = h.copy()
    observed[-1, -1] -= 1.15 * margin
    base_profile = normalized_profile(a, start, size)
    print("ridge min_eig psd_pass rel_frobenius_error profile_error")
    for ridge_scale in [0.0, 0.25, 0.50, 0.75, 1.00, 1.25, 2.00, 4.00]:
        ridge = ridge_scale * margin
        reg = observed + ridge * np.eye(size)
        eig = np.linalg.eigvalsh(reg)
        # Diagonal ridge is not a legal Hankel sequence perturbation; measure
        # object fidelity directly in matrix and anti-diagonal profile terms.
        rel = float(np.linalg.norm(reg - h) / np.linalg.norm(h))
        # Recover anti-diagonal means as the implied Hankel profile.
        implied = []
        for k in range(2 * size - 1):
            entries = [reg[i, j] for i in range(size) for j in range(size) if i + j == k]
            implied.append(float(np.mean(entries)))
        implied = np.asarray(implied) / max(abs(implied[0]), 1e-300)
        prof_err = float(np.linalg.norm(implied - base_profile) / np.linalg.norm(base_profile))
        print(f"{ridge_scale:.2f} {eig[0]:+.4e} {int(eig[0] > 0)} {rel:.3e} {prof_err:.3e}")


def main() -> None:
    node_stochastic_resonance()
    transfer_jensen()


if __name__ == "__main__":
    main()
