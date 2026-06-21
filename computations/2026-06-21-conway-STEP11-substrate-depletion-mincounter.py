#!/usr/bin/env python3
"""STEP 11: minimal-counterexample search for depletion-as-damping."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


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


def raw_trace(
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


def summarize(times: np.ndarray, raw: np.ndarray, threshold: float) -> tuple[float, float, float, float, float]:
    rates = np.maximum(raw - threshold, 0.0)
    if len(times) < 2:
        return 0.0, 0.0, 1.0, 0.0, 0.0
    product = np.cumsum(rates) * float(np.mean(np.diff(times)))
    k, _, nrmse = fit_exponential_inhibition(times, product)
    n = len(rates)
    early = float(np.mean(rates[: max(4, n // 5)]))
    late = float(np.mean(rates[-max(4, n // 5) :]))
    ratio = early / max(late, 1e-12)
    active = float(np.mean(rates > 1e-12))
    score = max(0.0, k) * max(0.0, ratio - 1.0) * max(0.0, 0.20 - nrmse) * active
    return k, nrmse, ratio, active, score


def scan(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    starts = [80.0, 100.0, 125.0, 160.0, 220.0, 300.0, 420.0, 500.0, 560.0]
    lengths = [14.0, 22.0, 34.0, 52.0, 78.0]
    thresholds = [0.8, 1.0, 1.2]
    sigmas = [0.3, 0.5, 1.2]
    print("STEP11 metaphor: minimal counterexample to 'depletion-like damping is absent'")
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print(
        "sigma start length threshold true_k true_nrmse true_ratio true_active "
        "finite_score random_score shuffle_score amp_score true_specific"
    )
    rows = []
    for sigma in sigmas:
        for start in starts:
            for length in lengths:
                for threshold in thresholds:
                    seed = 551000 + int(10 * start) + int(100 * length) + int(100 * threshold) + int(100 * sigma)
                    rng = np.random.default_rng(seed)
                    times, true_d, true_a = raw_trace("true", sigma, start, length, samples, primes, rng)
                    true_k, true_nrmse, true_ratio, true_active, true_score = summarize(times, true_d, threshold)
                    rng = np.random.default_rng(seed + 1)
                    _, finite_d, _ = raw_trace("finite", sigma, start, length, samples, primes, rng)
                    finite_score = summarize(times, finite_d, threshold)[4]
                    rng = np.random.default_rng(seed + 2)
                    _, random_d, _ = raw_trace("random", sigma, start, length, samples, primes, rng)
                    random_score = summarize(times, random_d, threshold)[4]
                    shuf = true_d.copy()
                    rng = np.random.default_rng(seed + 3)
                    rng.shuffle(shuf)
                    shuffle_score = summarize(times, shuf, threshold)[4]
                    amp_threshold = float(np.quantile(true_a, 0.70))
                    amp_score = summarize(times, true_a, amp_threshold)[4]
                    true_specific = int(
                        sigma < 0.9
                        and true_k > 0.018
                        and true_nrmse < 0.12
                        and true_ratio > 2.0
                        and 0.04 <= true_active <= 0.55
                        and true_score > 2.5 * max(finite_score, random_score, shuffle_score, amp_score, 1e-9)
                    )
                    rows.append(
                        (
                            true_specific,
                            length,
                            -true_score,
                            sigma,
                            start,
                            threshold,
                            true_k,
                            true_nrmse,
                            true_ratio,
                            true_active,
                            finite_score,
                            random_score,
                            shuffle_score,
                            amp_score,
                        )
                    )
    rows.sort()
    hits = [r for r in rows if r[0] == 1]
    top = hits[:12] if hits else sorted(rows, key=lambda r: r[2])[:12]
    for r in top:
        (
            true_specific,
            length,
            neg_score,
            sigma,
            start,
            threshold,
            true_k,
            true_nrmse,
            true_ratio,
            true_active,
            finite_score,
            random_score,
            shuffle_score,
            amp_score,
        ) = r
        print(
            f"{sigma:.1f} {start:6.1f} {length:6.1f} {threshold:5.2f} "
            f"{true_k:8.5f} {true_nrmse:8.4f} {true_ratio:9.3f} {true_active:8.3f} "
            f"{finite_score:11.6g} {random_score:11.6g} {shuffle_score:11.6g} "
            f"{amp_score:11.6g} {true_specific:d}"
        )
    print(f"true_specific_hits={len(hits)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    scan(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
