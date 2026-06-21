#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: existing pits/corrosion products can sustain localized corrosion after
external chloride exposure is reduced.

Selected minimal HT edit: drive a bounded memory state with an initial pulse of
continuum differential stress, then remove the external driver and measure tail
growth.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "damage state is driven by chloride pulse; after exposure is reduced, "
    "existing products/pits can sustain tail growth"
)

ATTEMPTS = {
    "stress-pulse-memory": (
        "HT memory state is driven by differential-stress pulse; after external "
        "driver is reduced, existing phase defects can sustain tail growth"
    ),
    "zero-scar-hysteresis": (
        "zero-neighborhood scars are created by a pulse and then tested for "
        "hysteretic persistence after the perturbation is removed"
    ),
    "finite-euler-rust": (
        "finite Euler artifacts are treated as corrosion products that may keep "
        "local defects active after cutoff stress is reduced"
    ),
}


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


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
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def stress_series(kind, sigma, window, primes, rng):
    vals = []
    for t in np.linspace(window[0], window[1], 240):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true-zeta":
            p = dlog_zeta(s)
        elif kind == "finite-euler":
            p = dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(phase_defect(g, p))
    arr = np.array(vals)
    return arr / (np.quantile(arr, 0.9) + 1e-12)


def memory_response(driver, memory_strength=0.08):
    pit = 0.02
    acid = 0.0
    rates = []
    for k, raw in enumerate(driver):
        # first half is exposure; second half has external driver reduced
        chloride = float(raw) if k < len(driver) // 2 else 0.05
        acid = 0.90 * acid + memory_strength * pit + 0.10 * chloride
        repair = 0.020 / (1.0 + 5.0 * acid)
        growth = (0.006 * chloride + 0.016 * acid) * (1.0 - pit)
        pit = min(1.0, max(0.0, pit + growth - repair))
        rates.append(growth)
    return float(pit), float(np.mean(rates[-40:])), float(acid)


def attempt_report():
    rows = []
    for name, text in ATTEMPTS.items():
        d = levenshtein(BASE_TRANSFER, text)
        rows.append((d, d / max(len(BASE_TRANSFER), len(text)), name))
    rows.sort()
    print("STEP8 three HT-transfer attempts by Levenshtein from NODE test")
    for d, norm, name in rows:
        marker = "SELECTED" if name == rows[0][2] else "rejected"
        print(f"attempt={name:24s} levenshtein={d:3d} normalized={norm:.4f} {marker}")
    print()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    attempt_report()
    print("STEP8/9 concrete corrosion-memory HT transfer")
    print("method=18 look-for-right-theorem; test bounded hysteresis threshold after driver removal")
    print(f"finite_prime_count={args.prime_count}")
    print("sigma window kind final_state tail_growth final_memory sustained")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.3, 0.5, 0.7]:
            for kind in ["true-zeta", "finite-euler", "random-phase"]:
                driver = stress_series(kind, sigma, window, primes, rng)
                pit, tail, acid = memory_response(driver)
                print(
                    f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {kind:12s} "
                    f"{pit:.6f} {tail:.6f} {acid:.6f} {int(tail > 0.003)}"
                )


if __name__ == "__main__":
    main()
