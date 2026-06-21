#!/usr/bin/env python3
"""STEP 11: minimal contamination needed for false HT colocalization."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def corr(a: np.ndarray, b: np.ndarray) -> float:
    aa = a - float(np.mean(a))
    bb = b - float(np.mean(b))
    denom = math.sqrt(float(np.dot(aa, aa) * np.dot(bb, bb)))
    return 0.0 if denom <= 1e-18 else float(np.dot(aa, bb) / denom)


def contamination_matrix(n: int, leak: float) -> np.ndarray:
    mat = np.eye(n) * (1.0 - leak)
    for i in range(n):
        if i > 0:
            mat[i, i - 1] += 0.5 * leak
        else:
            mat[i, i] += 0.5 * leak
        if i + 1 < n:
            mat[i, i + 1] += 0.5 * leak
        else:
            mat[i, i] += 0.5 * leak
    return mat


def decontaminate(mix: np.ndarray, observed: np.ndarray, ridge: float = 1e-4) -> np.ndarray:
    return np.linalg.solve(mix.T @ mix + ridge * np.eye(mix.shape[1]), mix.T @ observed)


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


def profiles(
    kind: str,
    sigma: float,
    start: float,
    end: float,
    blocks: int,
    points_per_block: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray]:
    marker = []
    defect = []
    edges = np.linspace(start, end, blocks + 1)
    for lo, hi in zip(edges[:-1], edges[1:]):
        ms = []
        ds = []
        for t in np.linspace(lo, hi, points_per_block, endpoint=False):
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
            ms.append(math.log(abs(p) + 1e-300))
            ds.append(max(phase_defect(g, p) - 1.0, 0.0))
        marker.append(float(np.mean(ms)))
        defect.append(float(np.mean(ds)))
    return np.asarray(marker), np.asarray(defect)


def minimal_leak(marker: np.ndarray, defect: np.ndarray) -> tuple[float, float, float, float, float]:
    raw = corr(marker, defect)
    for leak in np.linspace(0.0, 0.72, 19):
        mix = contamination_matrix(len(marker), float(leak))
        obs_m = mix @ marker
        obs_d = mix @ defect
        mixed = corr(obs_m, obs_d)
        rec_m = decontaminate(mix, obs_m)
        rec_d = decontaminate(mix, obs_d)
        deconv = corr(rec_m, rec_d)
        if raw < 0.15 and mixed > 0.35 and deconv < 0.18:
            return float(leak), raw, mixed, deconv, float(np.linalg.cond(mix))
    return float("nan"), raw, raw, raw, 0.0


def run(points_per_block: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    windows = [(100.0, 220.0), (500.0, 620.0)]
    print("STEP11 metaphor: minimal strip contamination for false positive colocalization")
    print(f"points_per_block={points_per_block} prime_count={prime_count}")
    print("kind sigma window blocks min_leak raw_corr mixed_corr deconv_corr condition false_positive")
    count = 0
    for blocks in [10, 14, 20, 28, 36]:
        for sigma in [0.3, 0.5, 1.2]:
            for kind in ["true", "finite", "random"]:
                for wi, (start, end) in enumerate(windows, 1):
                    seed = 771000 + blocks * 17 + int(100 * sigma) + 1000 * wi + {"true": 1, "finite": 2, "random": 3}[kind]
                    rng = np.random.default_rng(seed)
                    marker, defect = profiles(kind, sigma, start, end, blocks, points_per_block, primes, rng)
                    leak, raw, mixed, deconv, cond = minimal_leak(marker, defect)
                    ok = int(not math.isnan(leak))
                    count += ok
                    leak_print = -1.0 if math.isnan(leak) else leak
                    print(
                        f"{kind:6s} {sigma:.1f} {wi:d} {blocks:2d} {leak_print:8.3f} "
                        f"{raw:8.4f} {mixed:8.4f} {deconv:8.4f} {cond:8.3f} {ok:d}"
                    )
    print(f"false_positive_cases={count}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--points-per-block", type=int, default=10)
    parser.add_argument("--prime-count", type=int, default=150)
    args = parser.parse_args()
    run(args.points_per_block, args.prime_count)


if __name__ == "__main__":
    main()
