#!/usr/bin/env python3
"""THE-MACHINE run: dynamic biofilm stratification."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def js_divergence(p: np.ndarray, q: np.ndarray) -> float:
    p = p / max(np.sum(p), 1e-12)
    q = q / max(np.sum(q), 1e-12)
    m = 0.5 * (p + q)
    def kl(a, b):
        mask = a > 0
        return float(np.sum(a[mask] * np.log(a[mask] / np.maximum(b[mask], 1e-12))))
    return 0.5 * kl(p, m) + 0.5 * kl(q, m)


def node_simulation() -> None:
    depth = np.linspace(0.0, 1.0, 160)
    biomass = np.exp(-2.0 * depth)
    print("NODE simulation: growth/erosion reshapes stratification")
    print("time aerobic microaerobic anaerobic js_from_previous")
    prev = None
    for step in range(8):
        oxygen = np.exp(-3.5 * depth * (1.0 + 0.8 * biomass)) * (1.0 + 0.25 * math.sin(step))
        aerobic = oxygen > 0.55
        micro = (oxygen > 0.18) & (oxygen <= 0.55)
        anaerobic = oxygen <= 0.18
        dist = np.asarray([np.mean(aerobic), np.mean(micro), np.mean(anaerobic)])
        js = 0.0 if prev is None else js_divergence(dist, prev)
        print(f"{step:2d} {dist[0]:.4f} {dist[1]:.4f} {dist[2]:.4f} {js:.4f}")
        growth = 0.05 * oxygen * (1.0 - biomass)
        erosion = 0.04 * (depth < 0.18) * (1.0 + 0.7 * math.cos(step))
        biomass = np.clip(biomass + growth - erosion, 0.0, 1.5)
        prev = dist


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


def run_levenshtein() -> None:
    node_sig = "stratification changes over time growth erosion sloughing environmental conditions"
    candidates = [
        "sigma stratification changes over t windows phase environmental conditions",
        "zero shadow stratification changes over t windows topology conditions",
        "amplitude stratification changes over t windows bulk conditions",
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


def window_distribution(kind: str, sigmas: list[float], window: tuple[float, float], samples: int, primes, rng) -> np.ndarray:
    counts = np.zeros(3)
    for t in np.linspace(window[0], window[1], samples):
        for sigma in sigmas:
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
            d = phase_defect(g, p)
            if d > 1.0:
                counts[0] += 1
            elif d > 0.2:
                counts[1] += 1
            else:
                counts[2] += 1
    return counts / np.sum(counts)


def ht_dynamic(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    sigmas = [0.3, 0.5, 0.8, 1.2]
    windows = [(100.0, 170.0), (500.0, 570.0), (1000.0, 1070.0)]
    print("\nSTEP8/9 HT transfer: time-changing sigma stratification")
    print("kind js_100_500 js_500_1000 wet_100 wet_500 wet_1000 gel_100 gel_500 gel_1000 dry_100 dry_500 dry_1000")
    for kind in ["true", "finite", "random"]:
        rng = np.random.default_rng(1410000 + {"true": 1, "finite": 2, "random": 3}[kind])
        dists = [window_distribution(kind, sigmas, window, samples, primes, rng) for window in windows]
        print(
            f"{kind:6s} {js_divergence(dists[0], dists[1]):.4f} {js_divergence(dists[1], dists[2]):.4f} "
            f"{dists[0][0]:.4f} {dists[1][0]:.4f} {dists[2][0]:.4f} "
            f"{dists[0][1]:.4f} {dists[1][1]:.4f} {dists[2][1]:.4f} "
            f"{dists[0][2]:.4f} {dists[1][2]:.4f} {dists[2][2]:.4f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_dynamic(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
