#!/usr/bin/env python3
"""THE-MACHINE run: LDP open/closed boundary regularity."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def bernoulli_rate(x: float, p: float = 0.5) -> float:
    if x <= 0.0 or x >= 1.0:
        return math.inf
    return x * math.log(x / p) + (1.0 - x) * math.log((1.0 - x) / (1.0 - p))


def binom_log_prob_singleton(n: int, k: int, p: float = 0.5) -> float:
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * math.log(p) + (n - k) * math.log(1 - p)


def node_simulation() -> None:
    print("NODE simulation: LDP boundary regularity for Bernoulli sample mean")
    print("n event scaled_log_prob rate_bound note")
    for n in [40, 80, 160, 320, 640]:
        k = int(round(0.60 * n))
        scaled = binom_log_prob_singleton(n, k) / n
        print(f"{n:3d} singleton_0.60 {scaled: .5f} {-bernoulli_rate(k / n): .5f} lower_bound_open_empty")
        lo = int(math.ceil(0.58 * n))
        hi = int(math.floor(0.62 * n))
        logs = [binom_log_prob_singleton(n, j) for j in range(lo, hi + 1)]
        m = max(logs)
        prob_log = m + math.log(sum(math.exp(x - m) for x in logs))
        inf_rate = min(bernoulli_rate(j / n) for j in range(lo, hi + 1))
        print(f"{n:3d} thick_0.58_0.62 {prob_log / n: .5f} {-inf_rate: .5f} boundary_regularized")


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


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


def sample_defects(kind: str, sigma: float, samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for t in np.linspace(window[0], window[1], samples):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            if kind == "true":
                p = dlog_zeta(s)
            elif kind == "finite":
                p = dlog_finite_euler(s, primes)
            else:
                z = dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p = abs(z) * complex(math.cos(theta), math.sin(theta))
            vals.append(phase_defect(g, p))
    return np.asarray(vals)


def run_levenshtein() -> None:
    node_sig = "upper bound closed sets lower bound open sets boundary regularity"
    candidates = [
        "closed open phase threshold boundary regularity",
        "path topology zero shadow boundary regularity",
        "cumulant rate function exposed point regularity",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best = None
    for i, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{i} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, i, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")


def ht_boundary(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    epsilons = [0.04, 0.08, 0.16]
    print("\nSTEP8/9 HT transfer: open/closed phase-threshold boundary ambiguity")
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print("kind sigma quantile threshold eps tail open_tail closed_tail boundary_mass ambiguity")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(731000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            vals = sample_defects(kind, sigma, samples, primes, rng)
            for quantile in [0.75, 0.90, 0.95]:
                tau = float(np.quantile(vals, quantile))
                tail = float(np.mean(vals > tau))
                for eps in epsilons:
                    open_tail = float(np.mean(vals > tau + eps))
                    closed_tail = float(np.mean(vals >= tau - eps))
                    boundary = max(0.0, closed_tail - open_tail)
                    ambiguity = boundary / max(tail, 1e-12)
                    print(f"{kind:6s} {sigma:.1f} {quantile:.2f} {tau:.4f} {eps:.2f} {tail:.4f} {open_tail:.4f} {closed_tail:.4f} {boundary:.4f} {ambiguity:.3f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_boundary(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
