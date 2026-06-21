#!/usr/bin/env python3
"""THE-MACHINE Step 11 for excitable alternans.

NODE:
    Alternans or period-doubling before overt propagation failure.

Method #7:
    Strip it to essentials.  Remove fixed amplitudes and thresholds; keep only
    the ordering of high/low phase-defect states along a continuum line.

Metaphor:
    Before overt failure, an excitable system can expose a capacity constraint
    as an alternating high/low recovery pattern.  The HT analogue would be a
    true-specific high/low ordering in the phase-defect trace of zeta'/zeta
    that survives rank stripping and disappears under order shuffling.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def first_primes(n: int) -> tuple[int, ...]:
    primes: list[int] = []
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
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    vals: list[float] = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        true_p = dlog_zeta(s)
        finite_p = dlog_finite_euler(s, primes)
        if kind == "true":
            p = true_p
        elif kind == "finite":
            p = finite_p
        elif kind == "ampmatched-finite":
            p = finite_p * (abs(true_p) / (abs(finite_p) + 1e-300))
        elif kind == "random-phase":
            theta = float(rng.uniform(-math.pi, math.pi))
            p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        d = phase_defect(g, p)
        vals.append(d / (1.0 + d))
    return np.asarray(vals)


def longest_alternating_run(bits: np.ndarray) -> int:
    best = 1
    cur = 1
    for i in range(1, len(bits)):
        if bits[i] != bits[i - 1]:
            cur += 1
            best = max(best, cur)
        else:
            cur = 1
    return best


def stripped_metrics(x: np.ndarray, q: float, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    lo = float(np.quantile(x, q))
    hi = float(np.quantile(x, 1.0 - q))
    mask = (x <= lo) | (x >= hi)
    essential = x[mask]
    bits = (essential >= hi).astype(np.int8)
    if len(bits) < 12 or np.all(bits == bits[0]):
        return {
            "events": float(len(bits)),
            "alt_frac": 0.0,
            "shuffle_alt": 0.0,
            "alt_excess": 0.0,
            "long_run": 0.0,
            "shuffle_run": 0.0,
            "run_excess": 0.0,
            "collapse": 1.0,
            "survives": 0.0,
        }

    changes = bits[1:] != bits[:-1]
    alt_frac = float(np.mean(changes))
    run = float(longest_alternating_run(bits))
    shuffled_alt: list[float] = []
    shuffled_run: list[float] = []
    for _ in range(96):
        y = bits.copy()
        rng.shuffle(y)
        shuffled_alt.append(float(np.mean(y[1:] != y[:-1])))
        shuffled_run.append(float(longest_alternating_run(y)))
    shuffle_alt = float(np.mean(shuffled_alt))
    shuffle_run = float(np.mean(shuffled_run))

    third = max(4, len(bits) // 3)
    collapse = 1.0 - min(1.0, float(np.sum(bits[-third:])) / max(1.0, float(np.sum(bits[:third]))))
    alt_excess = alt_frac - shuffle_alt
    run_excess = run - shuffle_run
    survives = float(alt_excess > 0.08 and run_excess > 3.0 and collapse < 0.70)
    return {
        "events": float(len(bits)),
        "alt_frac": alt_frac,
        "shuffle_alt": shuffle_alt,
        "alt_excess": alt_excess,
        "long_run": run,
        "shuffle_run": shuffle_run,
        "run_excess": run_excess,
        "collapse": collapse,
        "survives": survives,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=300)
    parser.add_argument("--prime-count", type=int, default=120)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    qs = [0.20, 0.25, 0.30]

    print("STEP11 method #7: strip alternans to high/low ordering essentials")
    print("kind sigma window q events alt_frac shuffle_alt alt_excess long_run shuffle_run run_excess collapse survives")
    for c_i, (sigma, window) in enumerate(cases):
        for k_i, kind in enumerate(kinds):
            x = trace(kind, sigma, window, args.samples, primes, seed=20260621 + 977 * c_i + k_i)
            for q_i, q in enumerate(qs):
                out = stripped_metrics(x, q, seed=404000 + c_i * 100 + k_i * 10 + q_i)
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {q:.2f} "
                    f"{out['events']:.0f} {out['alt_frac']:.6f} {out['shuffle_alt']:.6f} "
                    f"{out['alt_excess']:.6f} {out['long_run']:.0f} {out['shuffle_run']:.6f} "
                    f"{out['run_excess']:.6f} {out['collapse']:.6f} {out['survives']:.0f}"
                )
    print(
        "\nInterpretation key: a non-reducing metaphor survivor would be true-specific "
        "rank-stripped alternation above shuffled order, before high-state collapse, "
        "without finite or random-phase leakage."
    )


if __name__ == "__main__":
    main()
