#!/usr/bin/env python3
"""THE-MACHINE run: droplet-size distribution and evaporation delay."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    omega = 2.7
    print("NODE simulation: polydisperse evaporation delay shifts Rayleigh index")
    print("log_sigma mean_delay mono_index poly_index bias")
    for log_sigma in [0.0, 0.15, 0.35, 0.60, 0.90]:
        diam = rng.lognormal(mean=0.0, sigma=log_sigma, size=30000)
        delays = diam * diam
        mean_delay = float(np.mean(delays))
        mono = math.cos(omega * mean_delay)
        poly = float(np.mean(np.cos(omega * delays)))
        print(f"{log_sigma:.2f} {mean_delay:.4f} {mono:.4f} {poly:.4f} {poly - mono:.4f}")


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


def defect_windows(kind: str, sigma: float, samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> list[np.ndarray]:
    out = []
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        vals = []
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
        out.append(np.asarray(vals))
    return out


def corr_at_lag(x: np.ndarray, lag: int) -> float:
    if lag <= 0 or lag >= len(x) - 3:
        return 0.0
    a = x[:-lag]
    b = x[lag:]
    a = a - np.mean(a)
    b = b - np.mean(b)
    denom = math.sqrt(float(np.dot(a, a) * np.dot(b, b)))
    return float(np.dot(a, b) / denom) if denom else 0.0


def distributed_delay_bias(windows: list[np.ndarray], mean_lag: int, width: float) -> tuple[float, float, float]:
    lags = np.arange(1, 61)
    weights = np.exp(-0.5 * ((np.log(lags / mean_lag)) / max(width, 1e-6)) ** 2)
    weights /= np.sum(weights)
    mono_vals = []
    poly_vals = []
    for x in windows:
        mono_vals.append(corr_at_lag(x, mean_lag))
        poly_vals.append(float(sum(w * corr_at_lag(x, int(lag)) for w, lag in zip(weights, lags))))
    mono = float(np.mean(mono_vals))
    poly = float(np.mean(poly_vals))
    return mono, poly, poly - mono


def run_levenshtein() -> None:
    node_sig = "droplet size distribution evaporation time liquid fueled systems"
    candidates = [
        "phase delay distribution response in continuum defect signal",
        "zero shadow delay distribution response in bridge topology",
        "amplitude delay distribution response in bulk envelope",
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


def ht_delay_distribution(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    print("\nSTEP8/9 HT transfer: distributed delay response of phase-defect signal")
    print("kind sigma mean_lag width mono_corr poly_corr bias")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(1110000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            windows = defect_windows(kind, sigma, samples, primes, rng)
            for mean_lag in [8, 20, 40]:
                for width in [0.20, 0.55, 0.90]:
                    mono, poly, bias = distributed_delay_bias(windows, mean_lag, width)
                    print(f"{kind:6s} {sigma:.1f} {mean_lag:2d} {width:.2f} {mono: .4f} {poly: .4f} {bias: .4f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_delay_distribution(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
