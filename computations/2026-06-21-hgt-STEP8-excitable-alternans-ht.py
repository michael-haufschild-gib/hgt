#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for excitable alternans.

NODE:
    Alternans or period-doubling before overt propagation failure.

Step 8:
    Compare three transfer attempts by Levenshtein distance.

Step 9 method #16:
    Minimal counterexample: shuffle parity / reverse parity / controls. A real
    alternans precursor should not survive arbitrary parity assignment.
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


def trace(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    vals = []
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


def alternans_metrics(x: np.ndarray, threshold: float, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    active = x >= threshold
    even = x[::2]
    odd = x[1::2]
    raw = abs(float(np.mean(even) - np.mean(odd)))
    failure = 1.0 - float(np.mean(active))
    shuffled = []
    for _ in range(48):
        y = x.copy()
        rng.shuffle(y)
        shuffled.append(abs(float(np.mean(y[::2]) - np.mean(y[1::2]))))
    return {
        "raw_alt": raw,
        "shuffle_alt": float(np.mean(shuffled)),
        "excess_alt": raw - float(np.mean(shuffled)),
        "failure_frac": failure,
        "active_frac": float(np.mean(active)),
        "period2_precursor": float(raw > float(np.mean(shuffled)) + 0.025 and failure < 0.70),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=120)
    args = parser.parse_args()

    node = "alternans or period doubling before overt propagation failure"
    attempts = {
        "phase-alternans-before-propagation-failure": "phase alternans or period doubling before overt propagation failure",
        "zero-shadow-period-doubling": "zero shadow period doubling before wave block",
        "prime-cutoff-restitution-alternans": "prime cutoff restitution alternans before Euler failure",
    }
    distances = {name: levenshtein(node, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:44s} distance={dist} normalized={dist / len(node):.4f}")
    print(f"selected={selected}")
    if selected != "phase-alternans-before-propagation-failure":
        raise SystemExit("Selected transfer is not implemented in this script.")

    print("\nSTEP9 method #16: minimal counterexample")
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    print("kind sigma window threshold raw_alt shuffle_alt excess_alt active_frac failure_frac period2_precursor")
    for c_i, (sigma, window) in enumerate(cases):
        for k_i, kind in enumerate(kinds):
            x = trace(kind, sigma, window, args.samples, primes, seed=20260621 + 211 * c_i + k_i)
            for threshold in [0.12, 0.20, 0.32]:
                out = alternans_metrics(x, threshold, seed=303000 + c_i * 100 + k_i * 10 + int(threshold * 100))
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {threshold:.2f} "
                    f"{out['raw_alt']:.6f} {out['shuffle_alt']:.6f} {out['excess_alt']:.6f} "
                    f"{out['active_frac']:.6f} {out['failure_frac']:.6f} {out['period2_precursor']:.0f}"
                )
    print(
        "\nInterpretation key: a survivor needs excess even/odd alternans above "
        "shuffle null, before failure, and without leakage to finite/random/right-side controls."
    )


if __name__ == "__main__":
    main()
