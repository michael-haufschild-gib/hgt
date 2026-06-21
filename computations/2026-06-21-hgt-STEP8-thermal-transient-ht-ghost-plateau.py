#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for transient false steady branches.

NODE constraint:
    Transient regimes can be mistaken for steady branches.

Step 8:
    Create three wildly different HT transfer attempts and select the
    lowest-Levenshtein one.

Step 9 method #18:
    Look for the right theorem. The right theorem is not "a short strip window
    looks steady"; it is "the apparent branch persists under window extension
    and controls." This script tests that theorem.
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


def carrier_profile(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray]:
    ts = np.linspace(window[0], window[1], samples)
    vals = []
    for t in ts:
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
        vals.append(phase_defect(g, p))
    return ts, np.asarray(vals)


def steady_segment(ts: np.ndarray, vals: np.ndarray, threshold: float) -> int:
    if len(vals) < 4:
        return 0
    med = float(np.median(vals))
    span = float(np.quantile(vals, 0.85) - np.quantile(vals, 0.15))
    slope = float(np.polyfit(ts - ts[0], vals, 1)[0])
    return int(med >= threshold and span <= 0.18 and abs(slope) <= 0.012)


def classify_false_branches(ts: np.ndarray, vals: np.ndarray, short_n: int, long_n: int) -> dict[str, float]:
    threshold = max(0.04, float(np.quantile(vals, 0.62)))
    short_total = 0
    false_total = 0
    persistent_total = 0
    for start in range(0, len(vals) - long_n, max(1, short_n // 2)):
        short = slice(start, start + short_n)
        long = slice(start, start + long_n)
        short_ok = steady_segment(ts[short], vals[short], threshold)
        long_ok = steady_segment(ts[long], vals[long], threshold)
        short_total += short_ok
        false_total += int(short_ok and not long_ok)
        persistent_total += int(short_ok and long_ok)
    return {
        "threshold": threshold,
        "short_steady": float(short_total),
        "false_short": float(false_total),
        "persistent": float(persistent_total),
        "false_fraction": float(false_total / short_total) if short_total else 0.0,
        "median": float(np.median(vals)),
        "q90": float(np.quantile(vals, 0.90)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=100)
    args = parser.parse_args()

    kernel = "transient regimes mistaken for steady branches"
    attempts = {
        "strip-transient-branch": "transient regimes mistaken for steady branches in continuum strip windows",
        "zero-ghost-plateau": "zero ghost plateaus mistaken for steady branches near zeros",
        "finite-prime-thermal-branch": "finite prime thermal branches mistaken for steady Euler states",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:29s} distance={dist} normalized={dist / max(1, len(kernel)):.4f}")
    print(f"selected={selected}")
    if selected != "zero-ghost-plateau":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #18: look for the right theorem")
    print("right theorem: apparent zero-shadow/phase plateau must persist under window extension")
    print("kind sigma window median q90 threshold short_steady false_short persistent false_fraction")
    primes = first_primes(args.prime_count)
    kinds = ["true", "finite", "ampmatched-finite", "random-phase", "gamma-only"]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    for case_index, (sigma, window) in enumerate(cases):
        for kind_index, kind in enumerate(kinds):
            rng = np.random.default_rng(20260621 + 101 * case_index + kind_index)
            ts, vals = carrier_profile(kind, sigma, window, args.samples, primes, rng)
            out = classify_false_branches(ts, vals, short_n=18, long_n=72)
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{out['median']:.6f} {out['q90']:.6f} {out['threshold']:.6f} "
                f"{out['short_steady']:.0f} {out['false_short']:.0f} "
                f"{out['persistent']:.0f} {out['false_fraction']:.6f}"
            )
    print(
        "\nInterpretation key: if short steady plateaus fail extension only because "
        "the carrier is the known left-strip phase-defect field, or if finite/random "
        "controls also generate false branches, the result reduces to finite-window "
        "plateau hunting."
    )


if __name__ == "__main__":
    main()
