#!/usr/bin/env python3
"""THE-MACHINE run: chaotic-saddle periodic skeletons."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def doubling_survives(x: float, steps: int, hole: tuple[float, float]) -> bool:
    for _ in range(steps):
        if hole[0] <= x <= hole[1]:
            return False
        x = (2.0 * x) % 1.0
    return True


def node_simulation() -> None:
    hole = (0.45, 0.55)
    print("NODE simulation: open doubling map saddle skeleton")
    print("period survivor_grid_fraction periodic_word_survivors topological_rate")
    for n in [4, 6, 8, 10, 12]:
        grid = np.linspace(0.0, 1.0, 2**14, endpoint=False)
        survivor_frac = float(np.mean([doubling_survives(float(x), n, hole) for x in grid]))
        words = 0
        for k in range(2**n):
            x = k / (2**n - 1) if n > 1 else 0.0
            if doubling_survives(x, n, hole):
                words += 1
        rate = math.log(max(words, 1)) / n
        print(f"{n:2d} {survivor_frac:.5f} {words:6d} {rate:.5f}")


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


def defect_sequence(kind: str, sigma: float, samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
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
        vals.append(float("nan"))
    return np.asarray(vals)


def recurrence_skeleton(vals: np.ndarray, threshold: float, max_lag: int) -> tuple[float, int, float, str]:
    valid = ~np.isnan(vals)
    hits = (vals > threshold) & valid
    density = float(np.mean(hits[valid]))
    best_lift = 0.0
    best_lag = 0
    scores = []
    for lag in range(1, max_lag + 1):
        a = hits[:-lag]
        b = hits[lag:]
        v = valid[:-lag] & valid[lag:]
        if np.sum(v) < 8:
            continue
        overlap = float(np.mean(a[v] & b[v]))
        lift = overlap / max(density * density, 1e-12)
        scores.append((lift, lag))
        if lift > best_lift:
            best_lift = lift
            best_lag = lag
    top = ",".join(f"{lag}:{lift:.2f}" for lift, lag in sorted(scores, reverse=True)[:5])
    return density, best_lag, best_lift, top


def run_levenshtein() -> None:
    node_sig = "chaotic saddle unstable periodic orbits govern transient dynamics"
    candidates = [
        "phase recurrence skeletons govern transient defect dynamics",
        "zero shadow periodic bridges govern transient topology dynamics",
        "amplitude envelope recurrences govern transient bulk dynamics",
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


def ht_recurrence(samples: int, prime_count: int, threshold: float, quantile: float, max_lag: int) -> None:
    primes = first_primes(prime_count)
    print("\nSTEP8/9 HT transfer: zero-shadow / phase-defect recurrence skeleton")
    print(f"threshold={threshold:.3f} quantile={quantile:.2f} samples_per_window={samples} prime_count={prime_count}")
    print("mode kind sigma cutoff density best_lag best_lift top_lags")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(1010000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            vals = defect_sequence(kind, sigma, samples, primes, rng)
            density, lag, lift, top = recurrence_skeleton(vals, threshold, max_lag)
            print(f"fixed    {kind:6s} {sigma:.1f} {threshold:.4f} {density:.4f} {lag:3d} {lift:.3f} {top}")
            cutoff = float(np.nanquantile(vals, quantile))
            density, lag, lift, top = recurrence_skeleton(vals, cutoff, max_lag)
            print(f"quantile {kind:6s} {sigma:.1f} {cutoff:.4f} {density:.4f} {lag:3d} {lift:.3f} {top}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=1.0)
    parser.add_argument("--quantile", type=float, default=0.90)
    parser.add_argument("--max-lag", type=int, default=90)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_recurrence(args.samples, args.prime_count, args.threshold, args.quantile, args.max_lag)


if __name__ == "__main__":
    main()
