#!/usr/bin/env python3
"""STEP 11: boundary cases for HT pre-clearing false negatives."""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


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


def features(
    kind: str,
    sigma: float,
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    signal = []
    amp = []
    prime_amp = []
    balance = []
    opposition = []
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
            ratio = math.log((abs(g) + 1e-300) / (abs(p) + 1e-300))
            phase = math.atan2((g / (p + 1e-300)).imag, (g / (p + 1e-300)).real)
            signal.append(max(phase_defect(g, p) - 1.0, 0.0))
            amp.append(math.log(abs(g) + abs(p) + 1e-300))
            prime_amp.append(math.log(abs(p) + 1e-300))
            balance.append(-abs(ratio))
            opposition.append(-math.cos(phase))
    signal_a = np.asarray(signal)
    prime_a = np.asarray(prime_amp)
    grad = np.abs(np.gradient(prime_a))
    return {
        "signal": signal_a,
        "amplitude": np.asarray(amp),
        "prime_amp": prime_a,
        "balance": np.asarray(balance),
        "opposition": np.asarray(opposition),
        "prime_grad": grad,
        "random": rng.normal(0.0, 1.0, len(signal_a)),
    }


def recall(signal: np.ndarray, marker: np.ndarray, q: float) -> float:
    total = float(np.sum(signal))
    if total <= 1e-12:
        return 1.0
    cutoff = float(np.quantile(marker, 1.0 - q))
    keep = marker < cutoff
    return float(np.sum(signal[keep]) / total)


def run(samples: int, prime_count: int) -> None:
    primes = first_primes(prime_count)
    markers = ["amplitude", "prime_amp", "balance", "opposition", "prime_grad", "random"]
    print("STEP11 metaphor: pre-clear boundary cases")
    print(f"samples_per_window={samples} prime_count={prime_count}")
    print("kind sigma marker total_signal recall20 recall40 boundary_loss")
    for sigma in [0.3, 0.5, 1.2]:
        control_recalls: dict[str, list[float]] = {m: [] for m in markers}
        rows = []
        for kind in ["true", "finite", "random"]:
            seed = 812000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind]
            rng = np.random.default_rng(seed)
            feat = features(kind, sigma, samples, primes, rng)
            total = float(np.sum(feat["signal"]))
            for marker in markers:
                r20 = recall(feat["signal"], feat[marker], 0.20)
                r40 = recall(feat["signal"], feat[marker], 0.40)
                rows.append((kind, sigma, marker, total, r20, r40))
                if kind != "true":
                    control_recalls[marker].append(r20)
        for kind, sig, marker, total, r20, r40 in rows:
            best_control_loss = 1.0 - min(control_recalls[marker]) if control_recalls[marker] else 0.0
            boundary_loss = int(
                kind == "true"
                and sig < 0.9
                and marker in {"prime_grad", "amplitude", "prime_amp"}
                and total > 1e-8
                and r20 < 0.55
                and (1.0 - r20) > best_control_loss + 0.25
            )
            print(f"{kind:6s} {sig:.1f} {marker:10s} {total:11.5f} {r20:8.4f} {r40:8.4f} {boundary_loss:d}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    run(args.samples, args.prime_count)


if __name__ == "__main__":
    main()
