#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for homeostatic energy capacity.

NODE:
    Homeostatic responses are constrained by energy metabolism and
    mitochondrial capacity.

Step 8:
    Create three HT transfer attempts and continue with the lowest
    Levenshtein distance to the NODE phrase.

Step 9 method #13:
    Find a monotone quantity. Here the monotone variable is available
    metabolic capacity; the measured quantity is phase-homeostasis success.
"""

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
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = cur
    return prev[-1]


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


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    defects: list[float] = []
    magnitudes: list[float] = []
    phases: list[float] = []
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
        elif kind == "gamma-only":
            p = 0.0 + 0.0j
        else:
            raise ValueError(kind)
        defects.append(phase_defect(g, p))
        magnitudes.append(math.log1p(abs(p)))
        phases.append(math.atan2(p.imag, p.real) if abs(p) > 0 else 0.0)
    d = np.asarray(defects)
    mag = np.asarray(magnitudes)
    ph = np.unwrap(np.asarray(phases))
    rough = np.r_[0.0, np.abs(np.diff(d))] + 0.35 * np.r_[0.0, np.abs(np.diff(mag))] + 0.08 * np.r_[0.0, np.abs(np.diff(ph))]
    drive = d / (1.0 + d)
    return {"drive": drive, "rough": rough, "defect": d}


def homeostatic_capacity_response(drive: np.ndarray, rough: np.ndarray, capacity: float, rough_scale: float) -> dict[str, float]:
    target = 0.30
    gain = 1.0
    actuals = []
    stresses = []
    gains = []
    costs = 1.0 + rough / (rough_scale + 1e-12)
    for x, cost in zip(drive, costs):
        raw = gain * x
        demand = 0.12 + 0.22 * cost * gain * gain + 0.60 * raw * raw
        if demand > capacity:
            actual = raw * capacity / demand
            stress = demand / capacity - 1.0
        else:
            actual = raw
            stress = 0.0
        gain += 0.040 * (target - actual) - 0.0015 * max(0.0, gain - 1.0) - 0.003 * stress
        gain = float(np.clip(gain, 0.1, 10.0))
        actuals.append(actual)
        stresses.append(stress)
        gains.append(gain)
    a = np.asarray(actuals)
    st = np.asarray(stresses)
    return {
        "success_frac": float(np.mean(a >= target)),
        "median_actual": float(np.median(a)),
        "mean_deficit": float(np.mean(np.maximum(0.0, target - a))),
        "stress_frac": float(np.mean(st > 0.0)),
        "mean_stress": float(np.mean(st)),
        "final_gain": float(gains[-1]),
    }


def monotone_violations(values: list[float]) -> int:
    return sum(1 for a, b in zip(values, values[1:]) if b + 1e-9 < a)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=190)
    parser.add_argument("--prime-count", type=int, default=120)
    args = parser.parse_args()

    node = "homeostatic responses constrained by energy metabolism and mitochondrial capacity"
    attempts = {
        "metabolic-capacity-phase-homeostasis": "homeostatic responses constrained by phase energy metabolism and mitochondrial capacity",
        "mitochondrial-constraint-derivative-budget": "mitochondrial capacity constrains derivative energy response on the complex strip",
        "atp-limited-zero-shadow-upscaling": "ATP limited zero shadow upscaling under archimedean prime cancellation",
    }
    distances = {name: levenshtein(node, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:42s} distance={dist} normalized={dist / len(node):.4f}")
    print(f"selected={selected}")
    if selected != "metabolic-capacity-phase-homeostasis":
        raise SystemExit("Selected transfer is not implemented in this script.")

    print("\nSTEP9 method #13: find a monotone quantity")
    print("quantity: capacity -> phase-homeostasis success fraction under energy-limited gain")
    primes = first_primes(args.prime_count)
    capacities = [0.35, 0.50, 0.70, 1.00, 1.45, 2.10, 3.00]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (0.7, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    print("kind sigma window capacity success_frac median_actual mean_deficit stress_frac mean_stress final_gain")
    summaries = []
    for case_index, (sigma, window) in enumerate(cases):
        traces = {
            kind: trace(kind, sigma, window, args.samples, primes, seed=20260621 + 97 * case_index + j)
            for j, kind in enumerate(kinds)
        }
        rough_scale = float(np.median(traces["true"]["rough"]) + 1e-6)
        for kind in kinds:
            successes = []
            for cap in capacities:
                out = homeostatic_capacity_response(traces[kind]["drive"], traces[kind]["rough"], cap, rough_scale)
                successes.append(out["success_frac"])
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {cap:.2f} "
                    f"{out['success_frac']:.6f} {out['median_actual']:.6f} {out['mean_deficit']:.6f} "
                    f"{out['stress_frac']:.6f} {out['mean_stress']:.6f} {out['final_gain']:.6f}"
                )
            summaries.append((kind, sigma, window, successes, monotone_violations(successes)))

    print("\ncapacity monotonicity summary")
    for kind, sigma, window, successes, violations in summaries:
        print(
            f"{kind:17s} sigma={sigma:.1f} window=[{window[0]:.0f},{window[1]:.0f}] "
            f"successes={','.join(f'{x:.3f}' for x in successes)} violations={violations}"
        )
    print(
        "\nInterpretation key: a non-reducing result would require a true-only "
        "capacity threshold or monotone success curve that survives finite, "
        "amplitude-matched, random-phase, gamma-only, and right-strip controls."
    )


if __name__ == "__main__":
    main()
