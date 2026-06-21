#!/usr/bin/env python3
"""THE-MACHINE run: crosslink compliance/unbinding/slip under load."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    thresholds = rng.lognormal(mean=0.0, sigma=0.45, size=1500)
    print("NODE simulation: load-dependent crosslink slip changes apparent rigidity")
    print("load bound_fraction compliance_proxy")
    for load in [0.25, 0.5, 0.75, 1.0, 1.5, 2.25, 3.0]:
        bound = thresholds > load
        compliance = 1.0 / max(1e-9, np.mean(bound))
        print(f"{load:.2f} {np.mean(bound):.4f} {compliance:.3f}")


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


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        else:
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        vals.append(phase_defect(g, p))
    return np.asarray(vals)


def ht_run(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    loads = [0.0, 0.10, 0.20, 0.35, 0.50]
    print("\nSTEP8/9 HT transfer: phase crosslink survival under load")
    print("kind sigma load bound_fraction compliance_proxy")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(222000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            vals = []
            for window in [(100.0, 170.0), (500.0, 570.0)]:
                vals.extend(trace(kind, sigma, window, samples, primes, rng))
            vals = np.asarray(vals)
            for load in loads:
                bound = vals > load
                print(f"{kind:6s} {sigma:.1f} {load:.2f} {np.mean(bound):.4f} {1.0 / max(1e-9, np.mean(bound)):.3f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
