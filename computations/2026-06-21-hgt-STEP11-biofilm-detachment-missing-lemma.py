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


def driver(kind, primes):
    vals = []
    rng = np.random.default_rng(20260621)
    for t in np.linspace(100.0, 170.0, 240):
        s = complex(0.3, float(t))
        g = gamma_part(s)
        if kind == "true-zeta":
            p = dlog_zeta(s)
        elif kind == "finite-euler":
            p = dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        vals.append(phase_defect(g, p))
    arr = np.array(vals)
    return arr / (np.quantile(arr, 0.9) + 1e-12)


def active_cv(x, threshold):
    y = x * (1.0 / (1.0 + np.exp(-18.0 * (x - threshold))))
    return float(y.std() / (y.mean() + 1e-12))


def main():
    primes = first_primes(160)
    thresholds = [0.35, 0.45, 0.55, 0.65, 0.75]
    print("STEP11 biofilm-detachment missing lemma falsifier")
    print("method=20 name-the-missing-lemma; lemma would require true burstiness > controls across thresholds")
    print("threshold true_cv finite_cv random_cv true_dominates")
    d = {kind: driver(kind, primes) for kind in ["true-zeta", "finite-euler", "random-phase"]}
    for th in thresholds:
        vals = {kind: active_cv(arr, th) for kind, arr in d.items()}
        print(f"{th:.2f} {vals['true-zeta']:.6f} {vals['finite-euler']:.6f} {vals['random-phase']:.6f} {int(vals['true-zeta'] > vals['finite-euler'] and vals['true-zeta'] > vals['random-phase'])}")


if __name__ == "__main__":
    main()
