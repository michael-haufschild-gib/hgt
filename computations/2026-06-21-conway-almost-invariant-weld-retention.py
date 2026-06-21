#!/usr/bin/env python3
"""THE-MACHINE run: probabilistic retention versus deterministic weld confinement."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_almost_invariant() -> None:
    print("NODE simulation: probabilistic retention is not deterministic confinement")
    print("leak horizon retention ever_exit deterministic_claim")
    rng = np.random.default_rng(204021)
    for leak in [0.002, 0.01, 0.04]:
        for horizon in [10, 50, 200, 1000]:
            trials = 3000
            retained = 0
            exited = 0
            for _ in range(trials):
                inside = True
                for _ in range(horizon):
                    if inside and rng.random() < leak:
                        inside = False
                        exited += 1
                        break
                retained += int(inside)
            retention = retained / trials
            deterministic = int(retention == 1.0)
            print(f"{leak:5.3f} {horizon:7d} {retention:9.4f} {exited/trials:9.4f} {deterministic:d}")


def run_levenshtein() -> str:
    node_sig = "interpreting probabilistic retention as deterministic confinement"
    candidates = [
        "interpreting probabilistic weld retention as deterministic confinement",
        "phase cancellation retention mistaken for invariant weld confinement",
        "almost invariant weld set leakage through phase boundary",
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
    return best[2]


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


def trace(kind: str, sigma: float, window, samples: int, primes, rng):
    vals = []
    for t in np.linspace(window[0], window[1], samples, endpoint=False):
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


def retention(mask: np.ndarray, lag: int) -> float:
    if lag <= 0 or lag >= len(mask):
        return 0.0
    starts = mask[:-lag]
    denom = int(np.sum(starts))
    if denom == 0:
        return 0.0
    return float(np.sum(starts & mask[lag:]) / denom)


def run_lengths(mask: np.ndarray):
    out = []
    cur = 0
    for x in mask:
        if x:
            cur += 1
        elif cur:
            out.append(cur)
            cur = 0
    if cur:
        out.append(cur)
    return np.asarray(out, dtype=float)


def ht_weld_retention(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    print("\nStanding-order consolidated target: The Weld")
    print("STEP8 transfer: interpreting probabilistic weld retention as deterministic confinement")
    print("STEP9 method 21: build a dependency chain")
    print("Dependency chain: confinement => retention_lag1 high + retention_lag20 high + no leakage; almost-invariance can satisfy only the first.")
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print("window kind sigma threshold occupancy ret1 ret5 ret20 median_run max_run leakage deterministic_like")
    for window in [(100.0, 170.0), (500.0, 570.0), (900.0, 970.0)]:
        window_name = f"{int(window[0])}-{int(window[1])}"
        for sigma in [0.3, 0.5, 0.7, 1.2]:
            for kind in ["true", "finite", "random"]:
                seed = 204700 + int(window[0]) + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind]
                vals = trace(kind, sigma, window, samples, primes, np.random.default_rng(seed))
                threshold = float(np.quantile(vals, 0.70))
                mask = vals >= threshold
                runs = run_lengths(mask)
                ret1 = retention(mask, 1)
                ret5 = retention(mask, 5)
                ret20 = retention(mask, 20)
                leakage = 1.0 - ret20
                deterministic_like = int(ret1 > 0.90 and ret20 > 0.85 and leakage < 0.15)
                med = float(np.median(runs)) if len(runs) else 0.0
                mx = float(np.max(runs)) if len(runs) else 0.0
                print(
                    f"{window_name:7s} {kind:6s} {sigma:.1f} {threshold:9.4f} {np.mean(mask):9.4f} "
                    f"{ret1:6.3f} {ret5:6.3f} {ret20:6.3f} {med:10.3f} {mx:7.1f} {leakage:7.3f} {deterministic_like:d}"
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_almost_invariant()
    run_levenshtein()
    print("\nSTEP7 formula check: transfer-operator retention/eigenvalue formulas apply unchanged only as generic Markov diagnostics; unchanged use is weld-blind.")
    ht_weld_retention(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
