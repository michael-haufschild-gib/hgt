#!/usr/bin/env python3
"""THE-MACHINE run: pre-clearing removes true interactors."""

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
    node_sig = "pre clearing can remove true interactors as well as sticky contaminants"
    candidates = [
        "pre clearing can remove true phase interactors as well as sticky amplitude contaminants",
        "background subtraction can erase true cancellation events as well as random artifacts",
        "control filtering can remove analytic interactions as well as finite truncation artifacts",
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


def node_simulation() -> None:
    print("NODE simulation: pre-clearing trades contaminant removal for true-interactor loss")
    print("case stringency true_recall contaminant_recall precision monotone_loss")
    rng = np.random.default_rng(61000)
    n_true = 120
    n_cont = 880
    abundance_true = rng.lognormal(0.0, 0.65, n_true)
    abundance_cont = rng.lognormal(0.2, 0.95, n_cont)
    sticky_base = rng.beta(1.4, 4.0, n_true)
    bait_true = 0.55 + 0.35 * sticky_base + rng.normal(0.0, 0.04, n_true)
    bait_true = np.clip(bait_true, 0.0, 1.0)
    sticky_cont = rng.beta(2.2, 2.4, n_cont)
    bait_cont = np.clip(0.12 + rng.normal(0.0, 0.04, n_cont), 0.0, 1.0)
    levels = np.linspace(0.0, 3.0, 9)
    prev_recall = 1.0
    for u in levels:
        remain_true = np.exp(-u * sticky_base)
        remain_cont = np.exp(-u * sticky_cont)
        cap_true = abundance_true * remain_true * bait_true
        cap_cont = abundance_cont * remain_cont * bait_cont
        true_recall = float(np.sum(cap_true) / np.sum(abundance_true * bait_true))
        cont_recall = float(np.sum(cap_cont) / np.sum(abundance_cont * bait_cont))
        precision = float(np.sum(cap_true) / max(np.sum(cap_true) + np.sum(cap_cont), 1e-12))
        monotone_loss = int(true_recall <= prev_recall + 1e-12)
        prev_recall = true_recall
        print(f"correlated {u:6.3f} {true_recall:9.4f} {cont_recall:9.4f} {precision:9.4f} {monotone_loss:d}")


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


def ht_trace(
    kind: str,
    sigma: float,
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray]:
    signals = []
    sticky = []
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
            defect = phase_defect(g, p)
            signals.append(max(defect - 1.0, 0.0))
            sticky.append(math.log(abs(p) + abs(g) + 1e-300))
    return np.asarray(signals), np.asarray(sticky)


def recall_curve(signal: np.ndarray, sticky: np.ndarray, levels: np.ndarray) -> tuple[np.ndarray, int, float]:
    total = float(np.sum(signal))
    if total <= 1e-12:
        return np.ones_like(levels), 0, 1.0
    recalls = []
    for q in levels:
        cutoff = float(np.quantile(sticky, 1.0 - q)) if q > 0 else float("inf")
        keep = sticky < cutoff
        recalls.append(float(np.sum(signal[keep]) / total))
    arr = np.asarray(recalls)
    violations = int(np.sum(np.diff(arr) > 1e-10))
    half_q = 1.0
    below = np.where(arr <= 0.5)[0]
    if len(below):
        half_q = float(levels[int(below[0])])
    return arr, violations, half_q


def ht_experiment(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    levels = np.asarray([0.0, 0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.50])
    print("\nSTEP8/9 HT transfer: pre-clearing high-amplitude sticky background")
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print("kind sigma total_signal q10 q20 q40 q50 half_q monotone_violations steep_loss")
    for sigma in [0.3, 0.5, 1.2]:
        rows = {}
        for kind in ["true", "finite", "random"]:
            seed = 701000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind]
            rng = np.random.default_rng(seed)
            signal, sticky = ht_trace(kind, sigma, samples, primes, rng)
            recalls, violations, half_q = recall_curve(signal, sticky, levels)
            total = float(np.sum(signal))
            rows[kind] = (recalls, violations, half_q, total)
            steep = int(kind == "true" and sigma < 0.9 and total > 1e-8 and half_q <= 0.20)
            print(
                f"{kind:6s} {sigma:.1f} {total:11.5f} {recalls[2]:6.3f} {recalls[4]:6.3f} "
                f"{recalls[6]:6.3f} {recalls[7]:6.3f} {half_q:6.3f} {violations:3d} {steep:d}"
            )
        if sigma < 0.9:
            t_half = rows["true"][2]
            control_half = min(rows["finite"][2], rows["random"][2])
            print(f"comparison sigma={sigma:.1f} true_half_q={t_half:.3f} best_control_half_q={control_half:.3f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    node_simulation()
    run_levenshtein()
    ht_experiment(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
