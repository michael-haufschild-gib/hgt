#!/usr/bin/env python3
"""STEP 11 subclaim split for survival-collider zero-shadow conditioning."""

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


def dlog_finite(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def corr(a, b):
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return 0.0
    return float(np.corrcoef(a, b)[0, 1])


def data(kind, sigma, ts, primes, rng):
    rows = []
    for t in ts:
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite(s, primes)
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        elif kind == "amplitude-matched-finite":
            pf = dlog_finite(s, primes)
            pt = dlog_zeta(s)
            p = (abs(pt) / max(abs(pf), 1e-300)) * pf
        else:
            raise ValueError(kind)
        rows.append((math.log(abs(g) + 1e-300), math.log(abs(p) + 1e-300), math.log(abs(g + p) + 1e-300)))
    return np.array(rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    primes = first_primes(args.prime_count)
    ts = np.linspace(100.0, 170.0, args.samples)
    print("STEP11 survival collider, method 1 = split into subclaims")
    print("Subclaims: zero-shadow genericity; true-vs-finite specificity; amplitude-matched control.")
    print("columns: sigma kind q source_corr shadow_corr shift")
    for sigma in [0.2, 0.3, 0.5, 0.7, 1.2]:
        for q in [0.05, 0.10, 0.20, 0.30]:
            for kind in ["true", "finite", "amplitude-matched-finite", "random-phase"]:
                arr = data(kind, sigma, ts, primes, rng)
                lg, lp, combined = arr.T
                source = corr(lg, lp)
                mask = combined <= np.quantile(combined, q)
                shadow = corr(lg[mask], lp[mask])
                print(
                    f"sigma={sigma:.1f} q={q:.2f} {kind:24s} "
                    f"source_corr={source:+.5f} shadow_corr={shadow:+.5f} shift={shadow-source:+.5f}"
                )


if __name__ == "__main__":
    main()
