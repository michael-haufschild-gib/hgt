#!/usr/bin/env python3
"""STEP 11 fake-proof gap for descendant tolerance mismatch."""

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


def rows(kind, sigma, ts, primes, rng):
    out = []
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
        elif kind == "amp-matched-finite":
            pf = dlog_finite(s, primes)
            pt = dlog_zeta(s)
            p = (abs(pt) / max(abs(pf), 1e-300)) * pf
        else:
            raise ValueError(kind)
        amp = math.log1p(abs(g + p))
        phase = max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))
        out.append((amp, phase))
    return np.array(out)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=300)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    primes = first_primes(args.prime_count)
    ts = np.linspace(100.0, 170.0, args.samples)
    print("STEP11 descendant tolerance, method 19 = write the fake proof")
    print("Fake proof: refuge-conditioned tolerance bias is HT-specific. Gap test: controls should not reproduce it.")
    print("columns: sigma q kind source_phase survivor_phase bias")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for q in [0.1, 0.3, 0.5]:
            for kind in ["true", "finite", "amp-matched-finite", "random-phase"]:
                dat = rows(kind, sigma, ts, primes, rng)
                refuge = dat[:, 0] <= np.quantile(dat[:, 0], q)
                src = float(np.median(dat[:, 1]))
                surv = float(np.median(dat[refuge, 1]))
                print(
                    f"sigma={sigma:.1f} q={q:.1f} {kind:20s} "
                    f"source_phase={src:.5g} survivor_phase={surv:.5g} bias={surv-src:+.5g}"
                )


if __name__ == "__main__":
    main()
