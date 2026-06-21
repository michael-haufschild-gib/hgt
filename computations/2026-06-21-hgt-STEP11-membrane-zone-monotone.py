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


def row_defects(kind, t, primes):
    sigmas = np.linspace(0.2, 0.8, 7)
    vals = []
    for sigma in sigmas:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true-zeta":
            p = dlog_zeta(s)
        elif kind == "finite-euler":
            p = dlog_finite_euler(s, primes)
        else:
            raise ValueError(kind)
        vals.append(phase_defect(g, p))
    return sigmas, np.array(vals)


def center_bias(kind, window, prime_count, quantile):
    primes = first_primes(prime_count)
    centers = []
    for t in np.linspace(window[0], window[1], 150):
        sigmas, row = row_defects(kind, t, primes)
        q = float(np.quantile(row, quantile))
        p = 1.0 / (1.0 + np.exp(-(row - q) / 0.12))
        centers.append(float(sigmas[int(np.argmax(p))]))
    centers = np.array(centers)
    return float(np.mean(centers < 0.5)), float(centers.std())


def trend(vals):
    diffs = np.diff(vals)
    if np.all(diffs >= -1e-9):
        return "nondecreasing"
    if np.all(diffs <= 1e-9):
        return "nonincreasing"
    return "nonmonotone"


def main():
    qs = [0.50, 0.60, 0.70, 0.80]
    counts = [10, 30, 80, 160, 240]
    print("STEP11 membrane-zone monotone test")
    print("method=13 find-a-monotone-quantity; test threshold and prime-count trends")
    print("kind window axis values trend")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["true-zeta", "finite-euler"]:
            vals = [center_bias(kind, window, 160, q)[0] for q in qs]
            print(f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] quantile " + ",".join(f"{v:.4f}" for v in vals) + f" {trend(vals)}")
            vals = [center_bias(kind, window, c, 0.65)[0] for c in counts]
            print(f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] prime_count " + ",".join(f"{v:.4f}" for v in vals) + f" {trend(vals)}")


if __name__ == "__main__":
    main()
