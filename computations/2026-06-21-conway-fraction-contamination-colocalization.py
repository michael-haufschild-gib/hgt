#!/usr/bin/env python3
"""THE-MACHINE run: fraction contamination creating false colocalization."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def corr(a: np.ndarray, b: np.ndarray) -> float:
    aa = a - float(np.mean(a))
    bb = b - float(np.mean(b))
    denom = math.sqrt(float(np.dot(aa, aa) * np.dot(bb, bb)))
    if denom <= 1e-18:
        return 0.0
    return float(np.dot(aa, bb) / denom)


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
    lhs = mix.T @ mix + ridge * np.eye(mix.shape[1])
    rhs = mix.T @ observed
    return np.linalg.solve(lhs, rhs)


def node_fraction_profiles(leak: float, noise: float, rng: np.random.Generator) -> tuple[float, float, float]:
    fractions = np.linspace(-1.0, 1.0, 9)
    mito = np.exp(-((fractions + 0.55) / 0.22) ** 2)
    cyto = np.exp(-((fractions - 0.05) / 0.25) ** 2)
    er = np.exp(-((fractions - 0.55) / 0.24) ** 2)
    pure = np.vstack([mito, cyto, er]).T
    pure /= np.maximum(np.sum(pure, axis=0, keepdims=True), 1e-12)
    cross = np.asarray(
        [
            [1.0 - leak, 0.72 * leak, 0.08 * leak],
            [0.65 * leak, 1.0 - leak, 0.35 * leak],
            [0.10 * leak, 0.55 * leak, 1.0 - leak],
        ]
    )
    marker_profiles = pure @ cross
    enzyme_a_true = np.asarray([1.0, 0.0, 0.0])
    enzyme_b_true = np.asarray([0.0, 1.0, 0.0])
    obs_a = marker_profiles @ enzyme_a_true
    obs_b = marker_profiles @ enzyme_b_true
    obs_a = np.maximum(0.0, obs_a + rng.normal(0.0, noise, size=obs_a.shape))
    obs_b = np.maximum(0.0, obs_b + rng.normal(0.0, noise, size=obs_b.shape))
    naive = corr(obs_a, obs_b)
    a_hat = np.linalg.lstsq(marker_profiles, obs_a, rcond=None)[0]
    b_hat = np.linalg.lstsq(marker_profiles, obs_b, rcond=None)[0]
    deconv = corr(a_hat, b_hat)
    marker_cond = float(np.linalg.cond(marker_profiles.T @ marker_profiles))
    return naive, deconv, marker_cond


def node_experiment() -> None:
    print("NODE simulation: contamination matrix creates false colocalization")
    print("leak noise naive_fraction_corr deconv_compartment_corr marker_condition")
    for leak in [0.00, 0.10, 0.22, 0.36, 0.50]:
        rng = np.random.default_rng(19000 + int(100 * leak))
        naive, deconv, cond = node_fraction_profiles(leak, 0.002, rng)
        print(f"{leak:4.2f} 0.002 {naive:9.4f} {deconv:9.4f} {cond:9.3f}")


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def run_levenshtein() -> None:
    node_sig = "compartment contamination during fractionation creating false colocalization signals"
    candidates = [
        "strip contamination during window fractionation creating false colocalization signals",
        "phase component contamination during analytic fractionation creating false cancellation signals",
        "sigma lane leakage during continuum fractionation creating false localization signals",
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


def block_profiles(
    kind: str,
    sigma: float,
    start: float,
    end: float,
    blocks: int,
    points_per_block: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    marker = []
    defect = []
    balance = []
    edges = np.linspace(start, end, blocks + 1)
    for lo, hi in zip(edges[:-1], edges[1:]):
        ms = []
        ds = []
        bs = []
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
            ratio = math.log((abs(g) + 1e-300) / (abs(p) + 1e-300))
            ms.append(math.log(abs(p) + 1e-300))
            ds.append(max(phase_defect(g, p) - 1.0, 0.0))
            bs.append(math.exp(-abs(ratio)))
        marker.append(float(np.mean(ms)))
        defect.append(float(np.mean(ds)))
        balance.append(float(np.mean(bs)))
    return np.asarray(marker), np.asarray(defect), np.asarray(balance)


def ht_experiment(blocks: int, points_per_block: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    windows = [(100.0, 220.0), (500.0, 620.0)]
    print("\nSTEP8/9 HT transfer: matrix decontamination of false colocalization")
    print(f"blocks={blocks} points_per_block={points_per_block} prime_count={prime_count}")
    print(
        "kind sigma window leak raw_corr mixed_corr deconv_corr balance_corr "
        "drop mixed_minus_raw condition survives_decontam"
    )
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            for wi, (start, end) in enumerate(windows, 1):
                seed = 334000 + int(100 * sigma) + 1000 * wi + {"true": 1, "finite": 2, "random": 3}[kind]
                rng = np.random.default_rng(seed)
                marker, defect, balance = block_profiles(
                    kind, sigma, start, end, blocks, points_per_block, primes, rng
                )
                raw = corr(marker, defect)
                bal = corr(balance, defect)
                for leak in [0.0, 0.18, 0.36]:
                    mix = contamination_matrix(blocks, leak)
                    obs_marker = mix @ marker
                    obs_defect = mix @ defect
                    mixed = corr(obs_marker, obs_defect)
                    rec_marker = decontaminate(mix, obs_marker)
                    rec_defect = decontaminate(mix, obs_defect)
                    deconv = corr(rec_marker, rec_defect)
                    cond = float(np.linalg.cond(mix))
                    survives = int(kind == "true" and sigma < 0.9 and deconv > 0.38 and abs(deconv - raw) < 0.08 and bal > 0.35)
                    print(
                        f"{kind:6s} {sigma:.1f} {wi:d} {leak:4.2f} {raw:8.4f} {mixed:8.4f} "
                        f"{deconv:8.4f} {bal:8.4f} {mixed - raw:9.4f} {cond:8.3f} {survives:d}"
                    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--blocks", type=int, default=28)
    parser.add_argument("--points-per-block", type=int, default=12)
    parser.add_argument("--prime-count", type=int, default=150)
    args = parser.parse_args()
    node_experiment()
    run_levenshtein()
    ht_experiment(args.blocks, args.points_per_block, args.prime_count)


if __name__ == "__main__":
    main()
