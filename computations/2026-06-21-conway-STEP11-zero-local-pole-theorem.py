#!/usr/bin/env python3
"""STEP11 right-theorem check: local pole/source geometry near zeros."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


ZEROS = [14.134725141734693, 21.022039638771554, 25.01085758014569, 30.424876125859513, 32.93506158773919]


def first_primes(n: int) -> tuple[int, ...]:
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


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 1e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def field(kind: str, s: complex, primes) -> float:
    if kind == "true_xi":
        val = gamma_part(s) + dlog_zeta(s)
    elif kind == "finite_xi":
        val = gamma_part(s) + dlog_finite_euler(s, primes)
    elif kind == "gamma_only":
        val = gamma_part(s)
    else:
        raise ValueError(kind)
    return math.log1p(abs(val))


def transverse_curvature(kind: str, gamma: float, width: float, samples: int, primes, delta: float) -> float:
    vals = []
    for t in np.linspace(gamma - width, gamma + width, samples):
        c = field(kind, complex(0.5, float(t)), primes)
        l = field(kind, complex(0.5 - delta, float(t)), primes)
        r = field(kind, complex(0.5 + delta, float(t)), primes)
        vals.append(abs((l - 2 * c + r) / (delta * delta)))
    return float(np.max(vals))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--samples", type=int, default=120)
    args = parser.parse_args()
    primes = first_primes(args.prime_count)
    print("STEP11 right theorem: local pole/source transverse curvature near zeros")
    print(f"samples={args.samples} prime_count={args.prime_count}")
    print("kind width mean_peak max_peak")
    for width in [0.8, 0.4, 0.2, 0.1]:
        for kind in ["true_xi", "finite_xi", "gamma_only"]:
            peaks = [transverse_curvature(kind, z, width, args.samples, primes, 0.04) for z in ZEROS]
            print(f"{kind:10s} {width:5.2f} {np.mean(peaks):10.4f} {np.max(peaks):10.4f}")


if __name__ == "__main__":
    main()
