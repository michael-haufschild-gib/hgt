#!/usr/bin/env python3
"""Step 11 control for catalyst-poisoning HT transfer.

Method #1: split into subclaims.
Subclaim A: the phase-defect distribution is strong.
Subclaim B: the ordering/timing of that defect is load-bearing, as in the NODE.

If shuffling/sorting the same defect values gives comparable survival, the
NODE's order-dependent content did not transfer.
"""

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


def defect_series(kind, sigma, t0, t1, samples=180, prime_count=160):
    primes = first_primes(prime_count)
    vals = []
    for t in np.linspace(t0, t1, samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p = dlog_zeta(s) if kind == "true" else dlog_finite_euler(s, primes)
        vals.append(phase_defect(g, p))
    return np.array(vals)


def poison_run(signal, poison_index, dose, seed=0.025):
    C = seed
    P = 0.0
    peak = C
    for i, d in enumerate(signal):
        if i == poison_index:
            P += dose
        drive = max(0.0, d - 0.18)
        growth = (0.018 + 0.34 * drive) * C * (1.0 - C)
        poison = 0.42 * C * P
        C = max(0.0, min(1.5, C + growth - poison - 0.010 * C))
        P = max(0.0, P - poison)
        peak = max(peak, C)
    return C > 0.45 or peak > 0.80


def survival_score(signal):
    doses = np.linspace(0.04, 0.52, 13)
    positions = np.linspace(0, len(signal) - 1, 28).astype(int)
    grid = np.zeros((len(doses), len(positions)), dtype=float)
    for i, dose in enumerate(doses):
        for j, pos in enumerate(positions):
            grid[i, j] = 1.0 if poison_run(signal, int(pos), float(dose)) else 0.0
    # First half survival measures whether early order matters.
    early = float(np.mean(grid[:, : len(positions) // 2]))
    total = float(np.mean(grid))
    first_by_dose = []
    for row in grid:
        idx = np.flatnonzero(row)
        first_by_dose.append(np.nan if len(idx) == 0 else float(idx[0]))
    finite_first = [x for x in first_by_dose if not np.isnan(x)]
    mean_first = float(np.mean(finite_first)) if finite_first else float("nan")
    return total, early, mean_first


def main():
    rng = np.random.default_rng(20260621)
    print("STEP11 catalyst-poisoning order controls")
    print("kind transform total_survival early_survival mean_first_survival_pos median_defect")
    for kind in ("true", "finite"):
        sig = defect_series(kind, 0.3, 100.0, 170.0)
        variants = {
            "natural": sig,
            "shuffled": rng.permutation(sig),
            "ascending": np.sort(sig),
            "descending": np.sort(sig)[::-1],
            "blockswap": np.r_[sig[len(sig)//2 :], sig[: len(sig)//2]],
        }
        for name, arr in variants.items():
            total, early, mean_first = survival_score(arr)
            print(f"{kind:6s} {name:10s} {total:.4f} {early:.4f} {mean_first:.4f} {np.median(arr):.4g}")


if __name__ == "__main__":
    main()
