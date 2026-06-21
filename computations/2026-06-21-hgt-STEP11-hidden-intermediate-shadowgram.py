#!/usr/bin/env python3
"""STEP 11 visual metaphor: hidden intermediates as detector shadowgrams.

NODE metaphor:
    a transient chemical intermediate can be missed by a detector that samples
    too sparsely or averages overlapping bands.

HT visual experiment:
    compare point-sampling, blur/average, and max-hold detectors on
    log(1+|d/ds log f(s)|) along vertical continuum lines.
"""

import argparse
import math

import mpmath as mp
import numpy as np


CHARS = " .:-=+*#%@"


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


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def line(kind, sigma, ts, primes):
    vals = []
    for t in ts:
        s = complex(float(sigma), float(t))
        p = dlog_zeta(s) if kind == "true" else dlog_finite_euler(s, primes)
        vals.append(math.log1p(abs(p)))
    return np.array(vals, dtype=float)


def bin_reduce(vals, bins, mode):
    chunks = np.array_split(vals, bins)
    if mode == "point":
        return np.array([c[len(c) // 2] for c in chunks], dtype=float)
    if mode == "blur":
        return np.array([np.mean(c) for c in chunks], dtype=float)
    if mode == "maxhold":
        return np.array([np.max(c) for c in chunks], dtype=float)
    raise ValueError(mode)


def spark(vals):
    vals = np.asarray(vals, dtype=float)
    lo = float(np.quantile(vals, 0.05))
    hi = float(np.quantile(vals, 0.98))
    if hi <= lo:
        hi = lo + 1e-12
    idx = np.clip(((vals - lo) / (hi - lo) * (len(CHARS) - 1)).astype(int), 0, len(CHARS) - 1)
    return "".join(CHARS[i] for i in idx)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=float, default=100.0)
    parser.add_argument("--t-max", type=float, default=170.0)
    parser.add_argument("--fine-count", type=int, default=2400)
    parser.add_argument("--bins", type=int, default=80)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    ts = np.linspace(args.t_min, args.t_max, args.fine_count)
    print("STEP11 visual shadowgram, method 5 = make it visual")
    print(f"window=[{args.t_min},{args.t_max}] fine_count={args.fine_count} bins={args.bins}")
    print("Each row is an 80-bin detector: point sample, blur average, or max-hold.")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        print(f"\nsigma={sigma}")
        for kind in ["true", "finite"]:
            vals = line(kind, sigma, ts, primes)
            fine_max = float(np.max(vals))
            print(f"{kind}: fine_max={fine_max:.5g} q99={float(np.quantile(vals,0.99)):.5g}")
            for mode in ["point", "blur", "maxhold"]:
                red = bin_reduce(vals, args.bins, mode)
                capture = float(np.max(red) / max(fine_max, 1e-300))
                print(f"  {mode:7s} capture={capture:.5g} {spark(red)}")


if __name__ == "__main__":
    main()
