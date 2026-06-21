#!/usr/bin/env python3
"""THE-MACHINE run: selective filtration loss of particle-bound analytes."""

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


def run_levenshtein() -> None:
    node_sig = "selective filtration loss of particle bound analytes"
    candidates = [
        "selective filtration loss of phase particle bound analytes",
        "pore size filtering loss of cancellation cluster signal",
        "sample filtration loss of zero neighborhood carrier mass",
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


def node_filtration() -> None:
    print("NODE simulation: particle-bound analyte lost by filtration")
    print("kd particle_load pore retained_particle_frac filtrate_recall fake_proof_gap")
    rng = np.random.default_rng(90400)
    particle_sizes = rng.lognormal(mean=0.0, sigma=0.85, size=5000)
    for kd in [0.05, 0.3, 1.0, 3.0]:
        for particle_load in [0.25, 1.0]:
            dissolved = 1.0 / (1.0 + kd * particle_load)
            bound = 1.0 - dissolved
            weights = rng.gamma(shape=2.0, scale=1.0, size=len(particle_sizes))
            weights /= float(np.sum(weights))
            for pore in [0.7, 1.4, 2.8]:
                retained_frac = float(np.sum(weights[particle_sizes > pore]))
                filtrate = dissolved + bound * (1.0 - retained_frac)
                gap = 1.0 - filtrate
                print(f"{kd:4.2f} {particle_load:5.2f} {pore:5.2f} {retained_frac:9.4f} {filtrate:9.4f} {gap:9.4f}")


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


def ht_signal(kind: str, sigma: float, samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for start, end in [(100.0, 220.0), (500.0, 620.0)]:
        for t in np.linspace(start, end, samples, endpoint=False):
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
            vals.append(max(phase_defect(g, p) - 1.0, 0.0))
    return np.asarray(vals)


def component_stats(signal: np.ndarray, pore_sizes: list[int]) -> tuple[int, float, float, dict[int, float]]:
    components: list[np.ndarray] = []
    current: list[float] = []
    for x in signal:
        if x > 0.0:
            current.append(float(x))
        elif current:
            components.append(np.asarray(current))
            current = []
    if current:
        components.append(np.asarray(current))
    total = float(np.sum(signal))
    if not components or total <= 1e-12:
        return 0, 0.0, 0.0, {p: 1.0 for p in pore_sizes}
    lengths = np.asarray([len(c) for c in components], dtype=float)
    masses = np.asarray([float(np.sum(c)) for c in components])
    recalls = {}
    for pore in pore_sizes:
        passed = float(np.sum([m for m, n in zip(masses, lengths) if n <= pore]))
        recalls[pore] = passed / total
    return len(components), float(np.mean(lengths)), float(np.max(masses) / total), recalls


def ht_experiment(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    pores = [1, 2, 3, 5, 8, 13]
    print("\nSTEP8/9 HT transfer: filtration of phase-particle-bound signal")
    print("Fake proof: pointwise phase-defect mass cannot be biased by component filtration.")
    print("Gap tested: mass can be carried by connected components that a pore threshold retains.")
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print("kind sigma total_signal components mean_len max_component_mass recall_p1 recall_p2 recall_p5 recall_p13 particle_bound")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            seed = 991000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind]
            rng = np.random.default_rng(seed)
            sig = ht_signal(kind, sigma, samples, primes, rng)
            n, mean_len, max_mass, recalls = component_stats(sig, pores)
            total = float(np.sum(sig))
            particle_bound = int(kind == "true" and sigma < 0.9 and recalls[2] < 0.40 and max_mass > 0.18)
            print(
                f"{kind:6s} {sigma:.1f} {total:11.5f} {n:4d} {mean_len:8.3f} {max_mass:8.4f} "
                f"{recalls[1]:8.4f} {recalls[2]:8.4f} {recalls[5]:8.4f} {recalls[13]:8.4f} {particle_bound:d}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=520)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_filtration()
    run_levenshtein()
    ht_experiment(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
