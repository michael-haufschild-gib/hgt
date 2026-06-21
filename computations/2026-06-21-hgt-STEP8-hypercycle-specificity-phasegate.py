#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer.

NODE: broad/promiscuous catalysis lets parasites exploit a hypercycle.

Minimal HT edit: compare two catalysts for continuum differential data:
- phase-specific catalyst: rewards the relative phase carrier between Gamma_inf
  and a prime/log-derivative part (positive phase-defect Delta);
- amplitude-promiscuous catalyst: rewards large scalar magnitude regardless of
  the missing phase carrier.

Candidates: true zeta'/zeta, finite Euler, and a random-phase parasite with the
same true magnitudes.
"""

import argparse
import math

import mpmath as mp
import numpy as np


def first_primes(n):
    primes = []
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


def gamma_part(s):
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g, p):
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def candidate_series(kind, sigma, window, samples, primes, rng):
    t0, t1 = window
    phase_scores = []
    amp_scores = []
    for t in np.linspace(t0, t1, samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        delta = phase_defect(g, p)
        phase_scores.append(max(0.0, delta))
        amp_scores.append(math.log1p(max(abs(g), abs(p))))
    return np.array(phase_scores), np.array(amp_scores)


def normalize_scores(raw):
    vals = np.array(raw, dtype=float)
    lo, hi = float(vals.min()), float(vals.max())
    if hi - lo < 1e-12:
        return np.ones_like(vals) * 0.5
    return (vals - lo) / (hi - lo)


def compete(scores, parasite_bonus=0.18, steps=2400, dt=0.008):
    # Three candidates compete for catalytic support. Candidate 0 is true; the
    # other two are parasites/non-reciprocal surrogates with a small rate bonus.
    x = np.array([0.34, 0.33, 0.33], dtype=float)
    rate = np.array([1.0, 1.0 + parasite_bonus, 1.0 + parasite_bonus])
    scores = np.array(scores, dtype=float)
    for _ in range(steps):
        growth = rate * scores * x
        mean = float(np.dot(growth, np.ones_like(x)))
        x = x + dt * x * (growth - mean)
        x = np.maximum(1e-12, x)
        x /= x.sum()
    return x


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.5, (100.0, 170.0)), (0.7, (100.0, 170.0)), (0.3, (500.0, 570.0))]
    kinds = ["true", "finite", "random-phase"]
    print("STEP8/9 hypercycle specificity phase-gate transfer")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("case phase_raw amp_raw phase_norm amp_norm final_phase_competition final_amp_competition")
    for sigma, window in cases:
        phase_raw = []
        amp_raw = []
        for kind in kinds:
            ph, amp = candidate_series(kind, sigma, window, args.samples, primes, rng)
            phase_raw.append(float(np.median(ph)))
            amp_raw.append(float(np.median(amp)))
        phase_norm = normalize_scores(phase_raw)
        amp_norm = normalize_scores(amp_raw)
        phase_final = compete(phase_norm)
        amp_final = compete(amp_norm)
        print(
            f"sigma={sigma} window={window} "
            f"phase_raw={','.join(f'{x:.4g}' for x in phase_raw)} "
            f"amp_raw={','.join(f'{x:.4g}' for x in amp_raw)} "
            f"phase_norm={','.join(f'{x:.3f}' for x in phase_norm)} "
            f"amp_norm={','.join(f'{x:.3f}' for x in amp_norm)} "
            f"phase_final={','.join(f'{x:.3f}' for x in phase_final)} "
            f"amp_final={','.join(f'{x:.3f}' for x in amp_final)}"
        )


if __name__ == "__main__":
    main()
