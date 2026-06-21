#!/usr/bin/env python3
"""
R34 STEP 8/9 transfer to:
  critical-line abscissa of a.s. convergence.

NODE constraint:
  binary-spin state encoding is not harmless; rates/timing/adaptation can change
  inferred structure.

Target transfer:
  the random Euler abscissa uses U(1) prime phases. Replace those states by
  binary signs or rate-like variables and inspect which convergence wall is
  preserved, shifted, or supplemented by drift.

Method #5: make it visual.
"""

from __future__ import annotations

import math

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        row = [i]
        for j, cb in enumerate(b, start=1):
            row.append(min(prev[j] + 1, row[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = row
    return prev[-1]


def primes_upto(n: int) -> np.ndarray:
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    return np.flatnonzero(sieve).astype(float)


def u1_phase_log_stats(p: np.ndarray, sigma: float) -> tuple[float, float]:
    r = p ** (-sigma)
    # Sum Li_2(r^2) by a short absolutely convergent series; k=1 dominates.
    var = np.zeros_like(r)
    term = r * r
    for k in range(1, 28):
        if k > 1:
            term *= r * r
        var += term / (k * k)
    return 0.0, float(np.sum(var))


def binary_sign_log_stats(p: np.ndarray, sigma: float) -> tuple[float, float]:
    r = p ** (-sigma)
    mean = -0.5 * np.log1p(-r * r)
    spread = 0.5 * np.log((1.0 + r) / (1.0 - r))
    return float(np.sum(mean)), float(np.sum(spread * spread))


def centered_rate_linear_stats(p: np.ndarray, sigma: float) -> tuple[float, float]:
    r = p ** (-sigma)
    return 0.0, float(np.sum(r * r))


def positive_rate_linear_stats(p: np.ndarray, sigma: float) -> tuple[float, float]:
    r = p ** (-sigma)
    # Unit-mean exponential-like rate: mean wall at sigma=1, variance wall at 1/2.
    return float(np.sum(r)), float(np.sum(r * r))


def bar(growth: float) -> str:
    if growth < 1.05:
        return "."
    if growth < 1.25:
        return "+"
    if growth < 1.75:
        return "++"
    if growth < 3.0:
        return "###"
    return "######"


def main() -> None:
    source = "neural_state_not_binary_spin_representation"
    attempts = [
        "state_representation_abscissa_random_euler",
        "binary_spin_prime_phase_threshold",
        "rate_coded_euler_drift_seam_shift",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:44s} distance={levenshtein(source, a)}")
    print(f"selected={min(attempts, key=lambda x: levenshtein(source, x))}")

    cutoffs = [1_000, 10_000, 100_000, 200_000]
    prime_sets = {x: primes_upto(x) for x in cutoffs}
    sigmas = [0.45, 0.50, 0.55, 0.75, 0.95, 1.10]
    encodings = [
        ("u1_phase_log", u1_phase_log_stats),
        ("binary_sign_log", binary_sign_log_stats),
        ("centered_rate_linear", centered_rate_linear_stats),
        ("positive_rate_linear", positive_rate_linear_stats),
    ]

    print("\nVisual growth map from cutoff 1e3 to 2e5")
    print("encoding              sigma  mean_growth  var_growth   visual(mean|var)")
    for name, fn in encodings:
        for sigma in sigmas:
            m0, v0 = fn(prime_sets[1_000], sigma)
            m1, v1 = fn(prime_sets[200_000], sigma)
            mg = (abs(m1) + 1e-12) / (abs(m0) + 1e-12)
            vg = (abs(v1) + 1e-12) / (abs(v0) + 1e-12)
            print(f"{name:22s} {sigma:5.2f} {mg:12.4f} {vg:11.4f}   {bar(mg):6s}|{bar(vg):6s}")

    print("\nCutoff values at sigma=.55 and .95")
    print("encoding              sigma cutoff     mean          variance")
    for name, fn in encodings:
        for sigma in [0.55, 0.95]:
            for cutoff in cutoffs:
                m, v = fn(prime_sets[cutoff], sigma)
                print(f"{name:22s} {sigma:5.2f} {cutoff:6d} {m:13.6f} {v:15.6f}")

    print("\nInterpretation")
    print(
        "The seam at sigma=1/2 is robust for centered fluctuation variance, but the full U(1) "
        "phase law is special: it kills every prime-power mean. Binary signs keep a 1/2 "
        "variance wall but create an even-power drift there, while positive rate states add "
        "a separate mean wall at sigma=1. State encoding changes the abscissa data."
    )


if __name__ == "__main__":
    main()
