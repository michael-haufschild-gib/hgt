#!/usr/bin/env python3
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
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def obs(kind, sigma, t, primes):
    s = complex(float(sigma), float(t))
    g = gamma_part(s)
    if kind == "true-zeta":
        p = dlog_zeta(s)
    elif kind == "finite-euler":
        p = dlog_finite_euler(s, primes)
    else:
        raise ValueError(kind)
    return phase_defect(g, p)


def ratios(kind, strip, window, prime_count):
    primes = first_primes(prime_count)
    sigmas = np.linspace(strip[0], strip[1], 9)
    left = []
    right = []
    for t in np.linspace(window[0], window[1], 160):
        row = np.array([obs(kind, sigma, t, primes) for sigma in sigmas])
        bulk = float(row.mean() + 1e-12)
        left.append(row[0] / bulk)
        right.append(row[-1] / bulk)
    return float(np.median(left)), float(np.median(right))


def main():
    strips = [(0.1, 0.9), (0.2, 0.8), (0.4, 0.6), (0.8, 1.4), (1.1, 1.7)]
    counts = [30, 160, 240]
    print("STEP11 crystal-interface extreme cases")
    print("method=10 test-extreme-cases; vary strip span and prime cutoff")
    print("kind window strip prime_count left_ratio right_ratio")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for strip in strips:
            for kind in ["true-zeta", "finite-euler"]:
                for count in counts:
                    l, r = ratios(kind, strip, window, count)
                    print(
                        f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] "
                        f"[{strip[0]:.1f},{strip[1]:.1f}] {count:11d} {l:.6f} {r:.6f}"
                    )


if __name__ == "__main__":
    main()
