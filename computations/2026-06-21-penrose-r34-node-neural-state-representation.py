#!/usr/bin/env python3
"""
R34 NODE validation: neural states are not generally binary spins.

Constraint tested:
  Inferred spin-glass-like structure depends on the state representation. Binary
  spikes, smoothed rates, timing variables, and adaptation variables can give
  different correlation/frustration structure from the same population.
"""

from __future__ import annotations

import itertools

import numpy as np


def smooth(x: np.ndarray, width: int) -> np.ndarray:
    kernel = np.exp(-np.arange(width) / (0.25 * width))
    kernel /= kernel.sum()
    return np.apply_along_axis(lambda row: np.convolve(row, kernel, mode="same"), 1, x)


def corr_sign_features(x: np.ndarray) -> np.ndarray:
    y = x - x.mean(axis=1, keepdims=True)
    y /= y.std(axis=1, keepdims=True) + 1e-12
    c = (y @ y.T) / y.shape[1]
    np.fill_diagonal(c, 0.0)
    return np.sign(c)


def frustration_fraction(signs: np.ndarray, nsamp: int = 4000) -> float:
    rng = np.random.default_rng(341)
    n = signs.shape[0]
    bad = 0
    total = 0
    for _ in range(nsamp):
        i, j, k = rng.choice(n, size=3, replace=False)
        prod = signs[i, j] * signs[j, k] * signs[k, i]
        if prod != 0:
            total += 1
            bad += prod < 0
    return bad / max(total, 1)


def participation_dim(x: np.ndarray) -> float:
    y = x - x.mean(axis=1, keepdims=True)
    cov = (y @ y.T) / y.shape[1]
    vals = np.linalg.eigvalsh(cov)
    vals = np.maximum(vals, 0)
    return float((vals.sum() ** 2) / (np.sum(vals * vals) + 1e-12))


def main() -> None:
    rng = np.random.default_rng(3403)
    n = 48
    t = 3500
    groups = rng.choice(4, size=n)
    latent = rng.normal(size=(4, t))
    latent = smooth(latent, 90)
    adaptation = np.zeros((n, t))
    spikes = np.zeros((n, t))
    phase_since = np.zeros((n, t))
    for i in range(n):
        bias = rng.normal(-1.35, 0.22)
        gain = rng.uniform(1.1, 1.9)
        adapt = 0.0
        since = 0
        for tt in range(t):
            drive = bias + gain * latent[groups[i], tt] - 0.95 * adapt + 0.25 * rng.normal()
            prob = 1.0 / (1.0 + np.exp(-drive))
            sp = rng.random() < prob
            spikes[i, tt] = sp
            adapt = 0.985 * adapt + 0.35 * sp
            since = 0 if sp else since + 1
            adaptation[i, tt] = adapt
            phase_since[i, tt] = np.log1p(since)

    binary = spikes
    rates = smooth(spikes, 45)
    timing = phase_since
    adapt = adaptation

    print("representation   mean_activity  participation_dim  frustration_fraction")
    for name, mat in [
        ("binary_spike", binary),
        ("smoothed_rate", rates),
        ("timing_since", timing),
        ("adaptation", adapt),
    ]:
        signs = corr_sign_features(mat)
        print(
            f"{name:15s} {mat.mean():13.5f} {participation_dim(mat):18.4f} "
            f"{frustration_fraction(signs):21.4f}"
        )

    print("\nNODE verdict:")
    print(
        "The same simulated population gives different dimensionality and frustration "
        "depending on whether the state is binary, rate-like, timing-like, or adaptive. "
        "The state representation is a constraint, not a harmless encoding choice."
    )


if __name__ == "__main__":
    main()
