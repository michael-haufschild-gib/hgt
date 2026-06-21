#!/usr/bin/env python3
"""STEP 12 battery for depletion-like phase damping windows."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


HITS = [
    (0.3, 560.0, 14.0, 1.20),
    (0.3, 560.0, 14.0, 1.00),
    (0.3, 125.0, 14.0, 0.80),
    (0.3, 560.0, 14.0, 0.80),
    (0.3, 220.0, 14.0, 1.20),
    (0.3, 220.0, 14.0, 1.00),
    (0.5, 125.0, 14.0, 1.00),
    (0.3, 220.0, 22.0, 1.20),
    (0.5, 125.0, 78.0, 1.20),
]


def fit_exponential_inhibition(times: np.ndarray, product: np.ndarray) -> tuple[float, float, float]:
    y = product - product[0]
    y_range = float(np.max(y) - np.min(y))
    if y_range <= 1e-12:
        return 0.0, 0.0, 0.0
    best = (float("inf"), 0.0, 0.0)
    for k in np.concatenate(([0.0], np.geomspace(1e-4, 0.30, 190))):
        if k < 1e-12:
            basis = times - times[0]
        else:
            basis = (1.0 - np.exp(-k * (times - times[0]))) / k
        denom = float(np.dot(basis, basis))
        if denom <= 1e-18:
            continue
        a = max(0.0, float(np.dot(y, basis) / denom))
        err = float(np.sqrt(np.mean((a * basis - y) ** 2)) / y_range)
        if err < best[0]:
            best = (err, float(k), a)
    return best[1], best[2], best[0]


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


def trace(
    kind: str,
    sigma: float,
    start: float,
    length: float,
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    times = np.linspace(start, start + length, samples)
    defects = []
    amplitudes = []
    for t in times:
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
        defects.append(phase_defect(g, p))
        amplitudes.append(math.log(abs(g) + abs(p) + 1e-300))
    return times - times[0], np.asarray(defects), np.asarray(amplitudes)


def metrics(times: np.ndarray, raw: np.ndarray, threshold: float) -> tuple[float, float, float, float, float, float]:
    rates = np.maximum(raw - threshold, 0.0)
    if len(times) < 2:
        return 0.0, 0.0, 1.0, 0.0, 0.0, 0.0
    product = np.cumsum(rates) * float(np.mean(np.diff(times)))
    k, _, nrmse = fit_exponential_inhibition(times, product)
    n = len(rates)
    early = float(np.mean(rates[: max(4, n // 5)]))
    late = float(np.mean(rates[-max(4, n // 5) :]))
    ratio = early / max(late, 1e-12)
    active = float(np.mean(rates > 1e-12))
    mass = float(np.sum(rates))
    front = float(np.sum(rates[: n // 2]) / max(mass, 1e-12))
    score = max(0.0, k) * max(0.0, ratio - 1.0) * max(0.0, 0.20 - nrmse) * active
    return k, nrmse, ratio, active, front, score


def survives(
    true_m: tuple[float, float, float, float, float, float],
    false_max: float,
) -> bool:
    k, nrmse, ratio, active, front, score = true_m
    return (
        k > 0.018
        and nrmse < 0.12
        and ratio > 2.0
        and 0.04 <= active <= 0.55
        and front > 0.62
        and score > 2.5 * max(false_max, 1e-9)
    )


def battery(samples: int) -> None:
    prime_sets = {n: first_primes(n) for n in [80, 150, 260]}
    jitters = [-2.0, 0.0, 2.0]
    print("STEP12 battery: depletion-like phase damping windows")
    print(f"samples={samples} finite_prime_counts=80,150,260 random_seeds=16 shuffle_seeds=16 jitters=-2,0,2")
    print(
        "sigma start length threshold jitter true_k true_nrmse true_ratio true_active true_front "
        "true_score finite_max random_max shuffle_max amp_score survives"
    )
    total = 0
    survived = 0
    core_survived = 0
    for sigma, start, length, threshold in HITS:
        for jitter in jitters:
            total += 1
            s0 = start + jitter
            seed = 884000 + int(100 * sigma) + int(10 * s0) + int(100 * length) + int(100 * threshold)
            rng = np.random.default_rng(seed)
            times, true_d, true_a = trace("true", sigma, s0, length, samples, prime_sets[150], rng)
            true_m = metrics(times, true_d, threshold)
            finite_scores = []
            for n, primes in prime_sets.items():
                rng = np.random.default_rng(seed + n)
                _, finite_d, _ = trace("finite", sigma, s0, length, samples, primes, rng)
                finite_scores.append(metrics(times, finite_d, threshold)[5])
            random_scores = []
            for j in range(16):
                rng = np.random.default_rng(seed + 1000 + j)
                _, random_d, _ = trace("random", sigma, s0, length, samples, prime_sets[150], rng)
                random_scores.append(metrics(times, random_d, threshold)[5])
            shuffle_scores = []
            for j in range(16):
                shuf = true_d.copy()
                rng = np.random.default_rng(seed + 2000 + j)
                rng.shuffle(shuf)
                shuffle_scores.append(metrics(times, shuf, threshold)[5])
            amp_threshold = float(np.quantile(true_a, 0.70))
            amp_score = metrics(times, true_a, amp_threshold)[5]
            false_max = max(max(finite_scores), max(random_scores), max(shuffle_scores), amp_score)
            ok = survives(true_m, false_max)
            survived += int(ok)
            if jitter == 0.0:
                core_survived += int(ok)
            k, nrmse, ratio, active, front, score = true_m
            print(
                f"{sigma:.1f} {start:6.1f} {length:6.1f} {threshold:5.2f} {jitter:5.1f} "
                f"{k:8.5f} {nrmse:8.4f} {ratio:9.3f} {active:8.3f} {front:8.3f} "
                f"{score:10.6g} {max(finite_scores):10.6g} {max(random_scores):10.6g} "
                f"{max(shuffle_scores):10.6g} {amp_score:10.6g} {int(ok):d}"
            )
    print(f"survival_total={survived}/{total}")
    print(f"survival_core={core_survived}/{len(HITS)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    args = parser.parse_args()
    battery(args.samples)


if __name__ == "__main__":
    main()
