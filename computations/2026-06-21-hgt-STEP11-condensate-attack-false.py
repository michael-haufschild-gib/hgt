#!/usr/bin/env python3
"""THE-MACHINE Step 11 for condensate crowding/accessibility.

Method #2: attack it as false.

Attack:
    If "crowding reduces active-site accessibility" has independent HT content,
    the true-zeta access advantage should not be a fragile choice of the
    nonspecific penalty function. Sweep penalty strength and include random
    phase controls with identical true magnitudes.
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


def measure(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator, penalty_strength: float) -> tuple[float, float, float]:
    amps = []
    access = []
    penalized = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p_true = dlog_zeta(s)
        if kind == "true":
            p = p_true
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "ampmatched-finite":
            p0 = dlog_finite_euler(s, primes)
            p = p0 * (abs(p_true) / (abs(p0) + 1e-300))
        elif kind == "random-phase":
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(p_true) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        amp = math.log1p(abs(p))
        acc = phase_defect(g, p)
        amps.append(amp)
        access.append(acc)
        penalized.append(acc / (1.0 + penalty_strength * amp**2))
    return float(np.median(amps)), float(np.median(access)), float(np.median(penalized))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    rng = np.random.default_rng(20260622)
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.7, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    strengths = [0.0, 0.25, 1.0, 4.0, 16.0]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]

    print("STEP11 method #2: attack crowding/accessibility as false")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("sigma window penalty kind amp access penalized")
    for sigma, window in cases:
        for strength in strengths:
            for kind in kinds:
                amp, access, penalized = measure(kind, sigma, window, args.samples, primes, rng, strength)
                print(
                    f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {strength:.2f} "
                    f"{kind:17s} {amp:.6f} {access:.6f} {penalized:.6f}"
                )

    print(
        "\nInterpretation: if changing penalty strength merely rescales the existing "
        "true phase-defect advantage, and amplitude-matched/random controls only fail "
        "because phase is destroyed, this is the known amplitude-vs-phase observable."
    )


if __name__ == "__main__":
    main()
