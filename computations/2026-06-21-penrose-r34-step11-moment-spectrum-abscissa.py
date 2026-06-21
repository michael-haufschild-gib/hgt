#!/usr/bin/env python3
"""
R34 STEP 11: strip state-encoding abscissa to the moment spectrum.

Method #7: keep only the essential object. For
    L(sigma)=sum_p -log(1-X_p p^-sigma),
the deterministic mean has a wall at sigma=1/k0, where k0 is the first
positive integer with E[X^k0] != 0. The fluctuation wall remains sigma=1/2
when the first random term has nonzero variance.
"""

from __future__ import annotations

import cmath
import math

import numpy as np


def primes_upto(n: int) -> np.ndarray:
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    return np.flatnonzero(sieve).astype(float)


def moments(samples: np.ndarray, kmax: int = 10) -> list[complex]:
    return [complex(np.mean(samples**k)) for k in range(1, kmax + 1)]


def first_nonzero_moment(samples: np.ndarray, tol: float = 1e-10) -> int | None:
    for k, m in enumerate(moments(samples, 12), start=1):
        if abs(m) > tol:
            return k
    return None


def mean_log_sum(p: np.ndarray, sigma: float, samples: np.ndarray, kmax: int = 16) -> float:
    ms = moments(samples, kmax)
    total = 0.0
    for k, mk in enumerate(ms, start=1):
        total += float((mk.real / k) * np.sum(p ** (-k * sigma)))
    return total


def main() -> None:
    roots3 = np.array([cmath.exp(2j * math.pi * j / 3) for j in range(3)], dtype=complex)
    roots4 = np.array([cmath.exp(2j * math.pi * j / 4) for j in range(4)], dtype=complex)
    encodings = {
        "u1_64point": np.array([cmath.exp(2j * math.pi * j / 64) for j in range(64)], dtype=complex),
        "rademacher": np.array([-1, 1], dtype=complex),
        "third_roots": roots3,
        "fourth_roots": roots4,
        "positive_rate": np.array([0.5, 1.5], dtype=complex),
        "centered_asym": np.array([-2.0, 1.0, 1.0], dtype=complex),
    }
    cut0, cut1 = 1_000, 200_000
    p0, p1 = primes_upto(cut0), primes_upto(cut1)
    sigmas = [0.40, 0.50, 0.55, 0.75, 1.05]
    print("encoding       k0  predicted_mean_wall  predicted_total_wall")
    for name, samples in encodings.items():
        k0 = first_nonzero_moment(samples)
        mean_wall = 0.0 if k0 is None else 1.0 / k0
        total_wall = max(0.5, mean_wall)
        print(f"{name:14s} {str(k0):>3s} {mean_wall:20.4f} {total_wall:21.4f}")

    print("\nMean-drift growth from cutoff 1e3 to 2e5")
    print("encoding       sigma  abs_mean_1e3  abs_mean_2e5  growth")
    for name, samples in encodings.items():
        for sigma in sigmas:
            m0 = abs(mean_log_sum(p0, sigma, samples))
            m1 = abs(mean_log_sum(p1, sigma, samples))
            growth = (m1 + 1e-12) / (m0 + 1e-12)
            print(f"{name:14s} {sigma:5.2f} {m0:13.6g} {m1:13.6g} {growth:8.3f}")

    print("\nInterpretation")
    print(
        "The abscissa is controlled by the moment spectrum of the prime-state law. "
        "U(1) is special because all nonzero moments vanish; Rademacher has k0=2, "
        "so deterministic drift is born exactly at the variance seam; q>=3 root "
        "states push drift below the variance wall; positive-rate states move the "
        "total convergence wall to sigma=1."
    )


if __name__ == "__main__":
    main()
