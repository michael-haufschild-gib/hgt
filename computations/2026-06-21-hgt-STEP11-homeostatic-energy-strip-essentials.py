#!/usr/bin/env python3
"""Step 11 metaphor test: strip homeostatic energy capacity to essentials.

Metaphor:
    A constrained homeostatic response is like a phase relation that survives
    only when a local "metabolic" budget can pay for the adjustment.

Method #7 from scientific-method.md:
    Strip it to essentials.

The experiment asks whether the HT capacity-threshold effect depends on the
roughness/cost coupling, or whether it is just the old phase-defect drive
distribution in new language.
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


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    defects = []
    mags = []
    phases = []
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
        defects.append(phase_defect(g, p))
        mags.append(math.log1p(abs(p)))
        phases.append(math.atan2(p.imag, p.real) if abs(p) else 0.0)
    d = np.asarray(defects)
    m = np.asarray(mags)
    p = np.unwrap(np.asarray(phases))
    rough = np.r_[0.0, np.abs(np.diff(d))] + 0.35 * np.r_[0.0, np.abs(np.diff(m))] + 0.08 * np.r_[0.0, np.abs(np.diff(p))]
    return d / (1.0 + d), rough, d


def success_fraction(drive: np.ndarray, cost: np.ndarray, capacity: float) -> float:
    target = 0.30
    gain = 1.0
    success = 0
    for x, c in zip(drive, cost):
        raw = gain * x
        demand = 0.12 + 0.22 * c * gain * gain + 0.60 * raw * raw
        if demand > capacity:
            actual = raw * capacity / demand
            stress = demand / capacity - 1.0
        else:
            actual = raw
            stress = 0.0
        gain += 0.040 * (target - actual) - 0.0015 * max(0.0, gain - 1.0) - 0.003 * stress
        gain = float(np.clip(gain, 0.1, 10.0))
        success += int(actual >= target)
    return success / len(drive)


def first_capacity(drive: np.ndarray, cost: np.ndarray, capacities: list[float], threshold: float) -> float:
    for cap in capacities:
        if success_fraction(drive, cost, cap) >= threshold:
            return cap
    return math.inf


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=190)
    parser.add_argument("--prime-count", type=int, default=120)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    capacities = [0.35, 0.50, 0.70, 1.00, 1.45, 2.10, 3.00]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    print("STEP11 method #7: strip the metabolic-capacity transfer to essentials")
    print("kind sigma window defect_med defect_pos full_C30 constcost_C30 shuffled_C30 roughonly_success_at_1.0")
    for case_index, (sigma, window) in enumerate(cases):
        raw = {
            kind: trace(kind, sigma, window, args.samples, primes, seed=20260621 + 211 * case_index + j)
            for j, kind in enumerate(kinds)
        }
        rough_scale = float(np.median(raw["true"][1]) + 1e-6)
        rng = np.random.default_rng(303000 + case_index)
        for kind in kinds:
            drive, rough, defect = raw[kind]
            cost_full = 1.0 + rough / (rough_scale + 1e-12)
            cost_const = np.ones_like(cost_full)
            cost_shuf = cost_full.copy()
            rng.shuffle(cost_shuf)
            flat_drive = np.ones_like(drive) * float(np.median(drive))
            full_c = first_capacity(drive, cost_full, capacities, 0.30)
            const_c = first_capacity(drive, cost_const, capacities, 0.30)
            shuf_c = first_capacity(drive, cost_shuf, capacities, 0.30)
            rough_only = success_fraction(flat_drive, cost_full, 1.00)
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{np.median(defect):.6f} {np.mean(defect > 0.0):.6f} "
                f"{full_c} {const_c} {shuf_c} {rough_only:.6f}"
            )
    print(
        "\nInterpretation key: if full_C30 tracks constcost_C30 and shuffled_C30, "
        "the energy metaphor has stripped down to phase-defect drive rather than "
        "an independent capacity/cost coupling."
    )


if __name__ == "__main__":
    main()
