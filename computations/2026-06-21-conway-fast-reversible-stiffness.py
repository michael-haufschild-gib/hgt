#!/usr/bin/env python3
"""THE-MACHINE run: fast reversible stochastic stiffness."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def ssa_fast_reversible(seed: int = 20260621, trajectories: int = 40) -> None:
    rng = np.random.default_rng(seed)
    print("NODE simulation: fast reversible reactions create exact-SSA stiffness")
    print("kfast mean_fast_events mean_slow_events mean_fast_per_slow mean_net_AB_change")
    for kfast in [1.0, 5.0, 25.0, 100.0]:
        fast_counts = []
        slow_counts = []
        net_changes = []
        for _ in range(trajectories):
            a, b, c, t = 60, 40, 0, 0.0
            fast = slow = 0
            while t < 3.0 and (a + b) > 0:
                props = [kfast * a, kfast * b, 0.08 * b]
                total = sum(props)
                if total <= 0:
                    break
                t += rng.exponential(1.0 / total)
                pick = rng.uniform(0.0, total)
                if pick < props[0]:
                    a -= 1
                    b += 1
                    fast += 1
                elif pick < props[0] + props[1]:
                    b -= 1
                    a += 1
                    fast += 1
                else:
                    b -= 1
                    c += 1
                    slow += 1
            fast_counts.append(fast)
            slow_counts.append(slow)
            net_changes.append(abs((a - b) - 20))
        mean_slow = float(np.mean(slow_counts))
        print(f"{kfast:5.1f} {np.mean(fast_counts):10.2f} {mean_slow:10.2f} {np.mean(fast_counts) / max(mean_slow, 1e-9):13.2f} {np.mean(net_changes):13.2f}")


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


def run_levenshtein() -> None:
    node_sig = "fast reversible reactions create stiffness exact stochastic simulation"
    candidates = [
        "fast reversible differential carrier flux creates stiffness in exact complex simulation",
        "fast reversible zero shadow topology creates stiffness in continuum bridge simulation",
        "fast reversible contour path jumps create stiffness in phase trajectory simulation",
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


def ht_stiffness(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    print("\nSTEP8/9 HT transfer: reversible carrier flux vs net differential motion")
    print("kind sigma mean_log_stiff p90_log_stiff p99_log_stiff tail_gt_1 tail_gt_2")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(881000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
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
                    vals.append(math.log((abs(g) + abs(p) + 1e-300) / (abs(g + p) + 1e-300)))
            arr = np.asarray(vals)
            print(f"{kind:6s} {sigma:.1f} {np.mean(arr): .4f} {np.quantile(arr, 0.90): .4f} {np.quantile(arr, 0.99): .4f} {np.mean(arr > 1.0):.4f} {np.mean(arr > 2.0):.4f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    ssa_fast_reversible()
    run_levenshtein()
    ht_stiffness(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
