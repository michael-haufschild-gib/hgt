#!/usr/bin/env python3
"""THE-MACHINE Step 11: attack phase boundary-domain sensitivity as false.

Metaphor:
    A confined diffusion experiment is not only the particle; it is the room.
    For the HT transfer, the "room" is the chosen sigma-domain of the
    continuum phase field.

Scientific method #2:
    Attack it as false. Test whether true zeta's larger domain-sensitivity
    survives lane-wise normalization and time shuffling. If the signal is only
    lane amplitude/marginal distribution, z-scoring or shuffling should explain
    it.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def first_primes(n: int) -> tuple[int, ...]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def build_fields(
    sigmas: list[float],
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    fields = {kind: np.zeros((len(sigmas), samples), dtype=float) for kind in ["true", "finite", "random"]}
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(np.linspace(window[0], window[1], samples)):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            fp = dlog_finite(s, primes)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            fields["true"][i, j] = phase_defect(g, zp)
            fields["finite"][i, j] = phase_defect(g, fp)
            fields["random"][i, j] = phase_defect(g, rp)
    return fields


def transform(field: np.ndarray, mode: str, rng: np.random.Generator) -> np.ndarray:
    if mode == "raw":
        return field.copy()
    if mode == "lane_zscore":
        mu = np.mean(field, axis=1, keepdims=True)
        sd = np.std(field, axis=1, keepdims=True) + 1e-12
        return (field - mu) / sd
    if mode == "lane_shuffle":
        out = field.copy()
        for i in range(out.shape[0]):
            rng.shuffle(out[i])
        return out
    if mode == "zscore_shuffle":
        out = transform(field, "lane_zscore", rng)
        for i in range(out.shape[0]):
            rng.shuffle(out[i])
        return out
    raise ValueError(mode)


def fit_alpha(field: np.ndarray) -> float:
    lags = np.asarray([1, 2, 4, 8, 16, 32], dtype=int)
    msd = []
    for lag in lags:
        d = field[:, lag:] - field[:, :-lag]
        msd.append(float(np.mean(d * d)))
    return float(np.polyfit(np.log(lags), np.log(np.maximum(msd, 1e-300)), 1)[0])


def domain_range(field: np.ndarray) -> tuple[float, float, dict[str, float]]:
    domains = {
        "left_boundary": [0, 1, 2],
        "critical_core": [1, 2, 3],
        "middle": [2, 3, 4],
        "right": [4, 5, 6],
        "wide": [0, 1, 2, 3, 4, 5, 6],
        "boundary_removed": [1, 2, 3, 4, 5],
    }
    values = {name: fit_alpha(field[idxs, :]) for name, idxs in domains.items()}
    arr = np.asarray(list(values.values()), dtype=float)
    return float(np.max(arr) - np.min(arr)), float(np.std(arr)), values


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=384)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606210202)
    primes = first_primes(args.prime_count)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    windows = [(100.0, 170.0), (260.0, 330.0), (500.0, 570.0)]
    modes = ["raw", "lane_zscore", "lane_shuffle", "zscore_shuffle"]

    print("STEP11 attack phase boundary-domain sensitivity")
    print(f"samples={args.samples} prime_count={args.prime_count} method=2 attack_false")
    print("window kind mode range sd left critical middle right wide removed")
    for window in windows:
        fields = build_fields(sigmas, window, args.samples, primes, rng)
        for kind in ["true", "finite", "random"]:
            for mode in modes:
                tr = transform(fields[kind], mode, rng)
                span, sd, vals = domain_range(tr)
                print(
                    f"[{window[0]:.0f},{window[1]:.0f}] {kind:6s} {mode:14s} "
                    f"{span:.4f} {sd:.4f} "
                    f"{vals['left_boundary']:.4f} {vals['critical_core']:.4f} "
                    f"{vals['middle']:.4f} {vals['right']:.4f} "
                    f"{vals['wide']:.4f} {vals['boundary_removed']:.4f}"
                )

    print("\ninterpretation gate")
    print("If true raw range is large but zscore/shuffle erase it, it is not a robust new HT constraint; if zscore keeps it while shuffles erase it, the candidate is temporal-correlation domain sensitivity and needs Step 12.")


if __name__ == "__main__":
    main()
