#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer.

NODE: catalyst poisoning before cycle amplification.

Minimal HT edit: chemical time becomes vertical height t in C; the catalyst
growth rate is driven by the continuum differential phase-carrier defect

    Delta=max(log|Gamma_infty|,log|P|)-log|Gamma_infty+P|

for P=true zeta'/zeta or a finite Euler log-derivative. Poison is injected at
different heights. Method #5: make the survival boundary visual.
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
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g, p):
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def defect_series(kind, sigma, t0, t1, samples, prime_count):
    primes = first_primes(prime_count)
    ts = np.linspace(t0, t1, samples)
    vals = []
    for t in ts:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        else:
            raise ValueError(kind)
        vals.append(phase_defect(g, p))
    return ts, np.array(vals)


def poison_run(signal, poison_index, dose, seed=0.025):
    C = seed
    P = 0.0
    peak = C
    threshold_index = None
    # Fixed across true/finite: only signal changes.
    base_growth = 0.018
    signal_gain = 0.34
    defect_threshold = 0.18
    poison_rate = 0.42
    loss = 0.010
    for i, d in enumerate(signal):
        if i == poison_index:
            P += dose
        drive = max(0.0, d - defect_threshold)
        growth = (base_growth + signal_gain * drive) * C * (1.0 - C)
        poison = poison_rate * C * P
        C = max(0.0, min(1.5, C + growth - poison - loss * C))
        P = max(0.0, P - poison)
        peak = max(peak, C)
        if threshold_index is None and C > 0.35:
            threshold_index = i
    survived = C > 0.45 or peak > 0.80
    return C, peak, threshold_index, survived


def summarize(kind, sigma, window, samples, prime_count):
    ts, defect = defect_series(kind, sigma, window[0], window[1], samples, prime_count)
    # Turn exact values into a visual amplification medium.
    doses = np.linspace(0.04, 0.52, 13)
    poison_positions = np.linspace(0, samples - 1, 28).astype(int)
    rows = []
    first_survive = []
    for dose in doses:
        row = []
        first = None
        for idx in poison_positions:
            final, peak, threshold_idx, survived = poison_run(defect, int(idx), float(dose))
            row.append("#" if survived else ".")
            if survived and first is None:
                first = int(idx)
        rows.append("".join(row))
        first_survive.append(first)
    return {
        "ts": ts,
        "defect": defect,
        "doses": doses,
        "positions": poison_positions,
        "rows": rows,
        "first_survive": first_survive,
        "median_defect": float(np.median(defect)),
        "pos_frac": float(np.mean(defect > 0.0)),
        "big_frac": float(np.mean(defect > 0.5)),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    cases = [
        (0.3, (100.0, 170.0)),
        (0.5, (100.0, 170.0)),
        (0.7, (100.0, 170.0)),
        (0.3, (500.0, 570.0)),
    ]
    print("STEP8/9 catalyst poisoning phase-carrier transfer")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("symbol: # cycle survives, . poisoned before amplification")
    for sigma, window in cases:
        for kind in ("true", "finite"):
            res = summarize(kind, sigma, window, args.samples, args.prime_count)
            print(f"\ncase kind={kind} sigma={sigma} window={window} med_defect={res['median_defect']:.4g} pos={res['pos_frac']:.3f} big={res['big_frac']:.3f}")
            for dose, row, first in zip(res["doses"], res["rows"], res["first_survive"]):
                first_t = "none" if first is None else f"{res['ts'][first]:.2f}"
                print(f"dose={dose:.2f} first={first_t:>7s} {row}")


if __name__ == "__main__":
    main()
