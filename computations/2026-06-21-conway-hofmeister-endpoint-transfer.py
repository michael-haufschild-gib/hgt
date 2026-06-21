#!/usr/bin/env python3
"""THE-MACHINE run: Hofmeister endpoint non-transfer."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def rankdata(values: np.ndarray) -> np.ndarray:
    order = np.argsort(values)
    ranks = np.empty_like(order, dtype=float)
    ranks[order] = np.arange(len(values), dtype=float)
    return ranks


def spearman(a: np.ndarray, b: np.ndarray) -> float:
    ra = rankdata(a)
    rb = rankdata(b)
    ra -= np.mean(ra)
    rb -= np.mean(rb)
    denom = math.sqrt(float(np.dot(ra, ra) * np.dot(rb, rb)))
    return float(np.dot(ra, rb) / denom) if denom else 0.0


def overlap_top(a: np.ndarray, b: np.ndarray, k: int = 4) -> int:
    return len(set(np.argsort(a)[-k:]).intersection(set(np.argsort(b)[-k:])))


def node_simulation(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)
    ions = [
        "F", "Cl", "Br", "I", "SO4", "SCN", "ClO4", "NO3", "Ac", "Gdn", "Li", "Cs",
    ]
    surface = np.asarray([-1.8, -0.9, -0.2, 0.4, -2.2, 1.8, 1.4, 0.7, -1.1, 2.1, -0.5, 0.9])
    protein = -0.15 * surface + rng.normal(0.0, 0.75, len(ions)) + np.asarray([0.1, -0.2, 0.2, -0.1, 1.0, -0.8, -0.5, 0.2, 0.4, -1.2, 0.1, -0.1])
    membrane = 0.30 * surface + rng.normal(0.0, 0.65, len(ions)) + np.asarray([-0.2, 0.1, 0.2, 0.9, -0.7, 0.1, 0.8, 0.4, -0.6, 0.2, -0.2, 0.7])
    polymer = rng.normal(0.0, 0.85, len(ions)) + np.asarray([0.7, -0.1, 0.0, -0.4, -0.5, 0.9, -0.3, 0.2, 0.5, -0.7, 0.1, -0.2])
    print("NODE simulation: Hofmeister rankings do not transfer across endpoints")
    print("endpoint spearman_with_surface top4_overlap values_by_ion")
    for name, vals in [("protein", protein), ("membrane", membrane), ("polymer", polymer)]:
        packed = ",".join(f"{ion}:{val:.2f}" for ion, val in zip(ions, vals))
        print(f"{name:8s} {spearman(surface, vals): .3f} {overlap_top(surface, vals):d} {packed}")


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


def traces(kind: str, sigma: float, samples: int, primes: tuple[int, ...], rng: np.random.Generator):
    gs: list[complex] = []
    ps: list[complex] = []
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
            gs.append(g)
            ps.append(p)
    return np.asarray(gs, dtype=np.complex128), np.asarray(ps, dtype=np.complex128)


def phase_defect(g: np.ndarray, p: np.ndarray) -> np.ndarray:
    return np.log(np.maximum(np.abs(g), np.abs(p)) + 1e-300) - np.log(np.abs(g + p) + 1e-300)


def mean_run(mask: np.ndarray) -> float:
    runs: list[int] = []
    cur = 0
    for item in mask:
        if item:
            cur += 1
        elif cur:
            runs.append(cur)
            cur = 0
    if cur:
        runs.append(cur)
    return float(np.mean(runs)) if runs else 0.0


def run_levenshtein() -> None:
    node_sig = "surface tension trends do not automatically transfer to protein membrane polymer endpoints"
    candidates = [
        "bulk amplitude ranking does not automatically transfer to phase run defect endpoints",
        "surface zero shadow bridge ranking does not automatically transfer to topology endpoints",
        "ion prime coefficient ranking does not automatically transfer to finite euler endpoints",
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


def ht_endpoint_transfer(samples: int, prime_count: int, threshold: float) -> None:
    primes = first_primes(prime_count)
    perturbations = [(lam, phi) for lam in [0.45, 0.70, 1.00, 1.35] for phi in [-1.30, -0.45, 0.45, 1.30]]
    print("\nSTEP8/9 HT transfer: endpoint ranking non-transfer")
    print(f"threshold={threshold:.3f} samples_per_window={samples} prime_count={prime_count}")
    print("kind sigma corr_surface_phase corr_surface_run corr_surface_variance top4_phase top4_run top4_variance transfer_lemma surface_range phase_range run_range")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(551000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            g, p = traces(kind, sigma, samples, primes, rng)
            surface_vals = []
            phase_vals = []
            run_vals = []
            var_vals = []
            for lam, phi in perturbations:
                z = lam * complex(math.cos(phi), math.sin(phi)) * p
                defect = phase_defect(g, z)
                surface_vals.append(float(np.mean(np.log(np.abs(g + z) + 1e-300))))
                phase_vals.append(float(np.mean(defect > threshold)))
                run_vals.append(mean_run(defect > threshold))
                var_vals.append(float(np.var(defect)))
            surface = np.asarray(surface_vals)
            phase = np.asarray(phase_vals)
            run = np.asarray(run_vals)
            var = np.asarray(var_vals)
            corr_phase = spearman(surface, phase)
            corr_run = spearman(surface, run)
            corr_var = spearman(surface, var)
            top_phase = overlap_top(surface, phase)
            top_run = overlap_top(surface, run)
            top_var = overlap_top(surface, var)
            lemma_ok = (
                corr_phase > 0.70
                and corr_run > 0.70
                and corr_var > 0.70
                and top_phase >= 3
                and top_run >= 3
                and top_var >= 3
            )
            print(
                f"{kind:6s} {sigma:.1f} "
                f"{corr_phase: .3f} {corr_run: .3f} {corr_var: .3f} "
                f"{top_phase} {top_run} {top_var} "
                f"{'holds' if lemma_ok else 'fails':5s} "
                f"{surface.min():.3f}:{surface.max():.3f} {phase.min():.4f}:{phase.max():.4f} {run.min():.2f}:{run.max():.2f}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=1.0)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_endpoint_transfer(args.samples, args.prime_count, args.threshold)


if __name__ == "__main__":
    main()
