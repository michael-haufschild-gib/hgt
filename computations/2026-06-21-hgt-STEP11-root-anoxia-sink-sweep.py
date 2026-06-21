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


def dlog_finite_euler(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g, p):
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def scores(alpha, window, primes):
    relief = []
    phase = []
    for t in np.linspace(window[0], window[1], 220):
        s = complex(0.3, float(t))
        g = gamma_part(s)
        p = dlog_finite_euler(s, primes)
        relief.append(math.log1p(max(abs(g), abs(p))) + alpha)
        phase.append(phase_defect(g, p))
    return float(np.median(relief)), float(np.median(phase))


def main():
    primes = first_primes(160)
    alphas = [0.0, 0.25, 0.50, 1.0, 2.0]
    print("STEP11 root-anoxia alternate-sink sweep")
    print("method=13 find-a-monotone-quantity; scalar relief can rise while phase function stays deficient")
    print("window alpha relief_proxy phase_function")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for alpha in alphas:
            relief, phase = scores(alpha, window, primes)
            print(f"[{window[0]:.0f},{window[1]:.0f}] {alpha:.2f} {relief:.6f} {phase:.6f}")


if __name__ == "__main__":
    main()
