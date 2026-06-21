#!/usr/bin/env python3
"""THE-MACHINE run: coarse-graining creates apparent entropy production."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def entropy_rate_from_sequence(seq: np.ndarray, nstates: int) -> float:
    counts = np.ones((nstates, nstates)) * 0.5
    for a, b in zip(seq[:-1], seq[1:]):
        counts[int(a), int(b)] += 1.0
    P = counts / counts.sum(axis=1, keepdims=True)
    pi = np.bincount(seq, minlength=nstates).astype(float) + 0.5
    pi /= pi.sum()
    F = pi[:, None] * P
    mask = (F > 1e-12) & (F.T > 1e-12)
    return float(np.sum(np.where(mask, F * np.log(F / F.T), 0.0)) / 2.0)


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    P = np.asarray([[0.75, 0.20, 0.05], [0.05, 0.75, 0.20], [0.20, 0.05, 0.75]])
    seq = [0]
    for _ in range(5000):
        seq.append(int(rng.choice(3, p=P[seq[-1]])))
    full = np.asarray(seq)
    coarse_a = (full > 0).astype(int)
    coarse_b = np.where(full == 1, 0, 1)
    print("NODE simulation: same trajectory has description-dependent apparent entropy production")
    print(f"full_3state={entropy_rate_from_sequence(full,3):.5f}")
    print(f"coarse_0_vs_12={entropy_rate_from_sequence(coarse_a,2):.5f}")
    print(f"coarse_1_vs_02={entropy_rate_from_sequence(coarse_b,2):.5f}")


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


def trace_seq(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
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
    q1, q2 = np.quantile(vals, [1/3, 2/3])
    return np.digitize(vals, [q1, q2])


def ht_run(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    print("\nSTEP8/9 HT transfer: coarse-grained apparent entropy on phase-defect trajectories")
    print("kind sigma window full3 coarse_low_vs_midhi coarse_mid_vs_lowhi")
    for sigma in [0.3, 0.5, 1.2]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            for kind in ["true", "finite", "random"]:
                rng = np.random.default_rng(991000 + int(100*sigma) + int(window[0]) + {"true":1,"finite":2,"random":3}[kind])
                seq = trace_seq(kind, sigma, window, samples, primes, rng)
                coarse_a = (seq > 0).astype(int)
                coarse_b = (seq == 1).astype(int)
                print(
                    f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{entropy_rate_from_sequence(seq,3):.5f} "
                    f"{entropy_rate_from_sequence(coarse_a,2):.5f} "
                    f"{entropy_rate_from_sequence(coarse_b,2):.5f}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    ht_run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
