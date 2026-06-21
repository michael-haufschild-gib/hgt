#!/usr/bin/env python3
"""THE-MACHINE Step 11: attack phase-catalog depth drift as false.

Metaphor:
    A shallow survey is a peephole into a city. If the apparent street pattern
    disappears when the peephole widens, it was not the city's constraint.

Scientific method #2:
    Attack it as false. Vary thresholds and origins, then ask whether the
    supposed phase-catalog depth drift survives finite/random controls.
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


def dlog_finite(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def bundle(
    sigma: float,
    t0: float,
    span: float,
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    out = {"true": [], "finite": [], "random": []}
    for t in np.linspace(t0, t0 + span, samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        zp = dlog_zeta(s)
        fp = dlog_finite(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
        out["true"].append(phase_defect(g, zp))
        out["finite"].append(phase_defect(g, fp))
        out["random"].append(phase_defect(g, rp))
    return {k: np.asarray(v, dtype=float) for k, v in out.items()}


def exponent(vals: np.ndarray, threshold: float, depth: int) -> float:
    events = vals[:depth] > threshold
    subdepths = np.unique(np.geomspace(max(12, depth // 16), depth, 16).astype(int))
    counts = np.asarray([np.count_nonzero(events[:d]) for d in subdepths], dtype=float)
    mask = counts >= 3
    if np.count_nonzero(mask) < 4:
        return float("nan")
    return float(np.polyfit(np.log(subdepths[mask]), np.log(counts[mask]), 1)[0])


def drift(vals: np.ndarray, threshold: float, shallow: int, deep: int) -> float:
    a = exponent(vals, threshold, shallow)
    b = exponent(vals, threshold, deep)
    if not np.isfinite(a) or not np.isfinite(b):
        return float("nan")
    return abs(b - a)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=768)
    parser.add_argument("--span", type=float, default=260.0)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(2606210202)
    primes = first_primes(args.prime_count)
    shallow = 128
    deep = args.samples

    print("STEP11 attack phase-catalog depth-drift as false")
    print(f"samples={args.samples} span={args.span} prime_count={args.prime_count} shallow={shallow} deep={deep}")
    print("sigma t0 q threshold true_drift finite_drift random_drift max_control verdict")
    wins = 0
    trials = 0
    for sigma in [0.3, 0.5, 1.2]:
        for t0 in [100.0, 260.0, 500.0]:
            data = bundle(sigma, t0, args.span, args.samples, primes, rng)
            for q in [0.70, 0.80, 0.90]:
                threshold = float(np.quantile(data["true"], q))
                vals = {kind: drift(data[kind], threshold, shallow, deep) for kind in ["true", "finite", "random"]}
                controls_valid = np.isfinite(vals["finite"]) and np.isfinite(vals["random"])
                finite_v = vals["finite"] if np.isfinite(vals["finite"]) else float("nan")
                random_v = vals["random"] if np.isfinite(vals["random"]) else float("nan")
                max_control = max(finite_v, random_v) if controls_valid else float("nan")
                if np.isfinite(vals["true"]):
                    trials += 1
                survives = controls_valid and np.isfinite(vals["true"]) and vals["true"] > 0.22 and vals["true"] > max_control + 0.12
                wins += int(survives)
                if survives:
                    verdict = "survives"
                elif not controls_valid:
                    verdict = "sparse_control_not_evidence"
                else:
                    verdict = "control_or_small"
                print(
                    f"{sigma:.1f} {t0:5.0f} {q:.2f} {threshold:.6g} "
                    f"{vals['true']:.4f} {vals['finite']:.4f} {vals['random']:.4f} "
                    f"{max_control:.4f} {verdict}"
                )
    print(f"\nSURVIVAL_COUNT true_specific={wins} finite_trials={trials}")
    print("reduction gate: zero or control-matched survival means the shallow-catalog metaphor does not produce new HT content.")


if __name__ == "__main__":
    main()
