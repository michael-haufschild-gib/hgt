#!/usr/bin/env python3
"""THE-MACHINE run: pooled drying zones and transverse HT coexistence."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def node_simulation() -> None:
    r = np.linspace(0.0, 1.0, 800)
    thickness = 0.15 + 1.25 * np.exp(-(r / 0.45) ** 2)
    dry_time = thickness**2
    gel_time = 0.58 * dry_time
    print("NODE simulation: thickness field creates simultaneous wet/gel/dry zones")
    print("time wet_frac gel_frac dry_frac coexist_zones")
    for time in [0.08, 0.16, 0.28, 0.42, 0.70, 1.10]:
        wet = time < gel_time
        gel = (time >= gel_time) & (time < dry_time)
        dry = time >= dry_time
        zones = int(np.any(wet)) + int(np.any(gel)) + int(np.any(dry))
        print(f"{time:.2f} {np.mean(wet):.4f} {np.mean(gel):.4f} {np.mean(dry):.4f} {zones}")


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


def defect_at(kind: str, sigma: float, t: float, primes: tuple[int, ...], rng: np.random.Generator) -> float:
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
    return phase_defect(g, p)


def run_levenshtein() -> None:
    node_sig = "pooling thickness mixed wet gelled dry zones"
    candidates = [
        "pooling thickness transverse sigma mixed wet gel dry phase zones",
        "pooling thickness zero shadow bridge mixed wet gel dry topology zones",
        "pooling thickness amplitude envelope mixed wet gel dry bulk zones",
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


def classify(vals: np.ndarray) -> tuple[bool, bool, bool]:
    dry = vals <= 0.20
    gel = (vals > 0.20) & (vals <= 1.00)
    wet = vals > 1.00
    return bool(np.any(wet)), bool(np.any(gel)), bool(np.any(dry))


def ht_zone_coexistence(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    sigmas = [0.3, 0.5, 0.8, 1.2]
    print("\nSTEP8/9 HT transfer: transverse wet/gel/dry phase-zone coexistence")
    print(f"samples_per_window={samples} prime_count={prime_count} sigmas={','.join(str(x) for x in sigmas)}")
    print("kind all_three wet_gel wet_dry gel_dry mean_zone_count mean_zone_entropy ordered_wet_to_dry")
    for kind in ["true", "finite", "random"]:
        rng = np.random.default_rng(1210000 + {"true": 1, "finite": 2, "random": 3}[kind])
        all_three = wet_gel = wet_dry = gel_dry = ordered = 0
        zone_counts = []
        entropies = []
        total = 0
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            for t in np.linspace(window[0], window[1], samples):
                vals = np.asarray([defect_at(kind, sigma, float(t), primes, rng) for sigma in sigmas])
                wet, gel, dry = classify(vals)
                all_three += int(wet and gel and dry)
                wet_gel += int(wet and gel)
                wet_dry += int(wet and dry)
                gel_dry += int(gel and dry)
                zone_counts.append(int(wet) + int(gel) + int(dry))
                state_counts = np.asarray([
                    np.sum(vals > 1.0),
                    np.sum((vals > 0.20) & (vals <= 1.0)),
                    np.sum(vals <= 0.20),
                ], dtype=float)
                probs = state_counts[state_counts > 0] / len(vals)
                entropies.append(float(-np.sum(probs * np.log(probs)) / math.log(3.0)))
                # Wet on the left and dry on the right is the pool-like layered analogue.
                ordered += int(vals[0] > 1.0 and vals[-1] <= 0.2)
                total += 1
        print(
            f"{kind:6s} {all_three / total:.4f} {wet_gel / total:.4f} {wet_dry / total:.4f} "
            f"{gel_dry / total:.4f} {np.mean(zone_counts):.3f} {np.mean(entropies):.4f} {ordered / total:.4f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_zone_coexistence(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
