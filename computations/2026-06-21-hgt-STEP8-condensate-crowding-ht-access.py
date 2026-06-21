#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for condensate crowding/accessibility.

NODE constraint:
    Crowding can increase effective molarity while reducing active-site
    accessibility through nonspecific interactions.

Step 8:
    Rank three HT transfers by Levenshtein and run the selected one.

Step 9 method #13:
    Find a monotone quantity. We test whether finite-prime crowding/enrichment
    rises monotonically while phase-accessibility does not, and whether this is
    anything beyond the existing amplitude-vs-phase split.
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
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
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


def scores(kind: str, sigma: float, window: tuple[float, float], samples: int, prime_count: int, rng: np.random.Generator) -> tuple[float, float, float]:
    primes = first_primes(prime_count)
    amp = []
    access = []
    crowd_penalized = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            pt = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(pt) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        amp_i = math.log1p(abs(p))
        access_i = phase_defect(g, p)
        nonspecific_penalty = 1.0 / (1.0 + amp_i**2)
        amp.append(amp_i)
        access.append(access_i)
        crowd_penalized.append(access_i * nonspecific_penalty)
    return float(np.median(amp)), float(np.median(access)), float(np.median(crowd_penalized))


def monotone(values: list[float], direction: str) -> int:
    if direction == "up":
        return int(all(b + 1e-12 >= a for a, b in zip(values, values[1:])))
    if direction == "down":
        return int(all(b <= a + 1e-12 for a, b in zip(values, values[1:])))
    raise ValueError(direction)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    args = parser.parse_args()

    kernel = "crowding increases effective molarity while nonspecific interactions reduce active site accessibility"
    attempts = {
        "amplitude-crowding-phase-access": "crowding amplitude increases while phase access decreases under nonspecific interactions",
        "condensate-diffusion-smoothing": "condensate viscosity slows diffusion by smoothing continuum differential signal",
        "partition-coefficient-strip": "partition coefficient moves enzyme and substrate between sigma lanes",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:32s} distance={dist}")
    print(f"selected={selected}")
    if selected != "amplitude-crowding-phase-access":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #13: find a monotone quantity")
    print("amplitude=enrichment/crowding proxy; access=phase-carrier accessibility; penalized=access/(1+amplitude^2)")
    print("sigma window kind prime_count amp access penalized")
    rng = np.random.default_rng(20260621)
    prime_counts = [20, 40, 80, 160, 320]
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.7, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    summaries = []
    for sigma, window in cases:
        for kind in ["true", "finite", "random-phase"]:
            amps = []
            accesses = []
            penalties = []
            counts = [160] if kind != "finite" else prime_counts
            for pc in counts:
                amp, access, penalized = scores(kind, sigma, window, args.samples, pc, rng)
                amps.append(amp)
                accesses.append(access)
                penalties.append(penalized)
                print(f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {kind:12s} {pc:3d} {amp:.6f} {access:.6f} {penalized:.6f}")
            if kind == "finite":
                summaries.append((sigma, window, monotone(amps, "up"), monotone(accesses, "up"), monotone(penalties, "up"), amps, accesses, penalties))

    print("\nFinite-prime monotone summary")
    print("sigma window amp_monotone_up access_monotone_up penalized_monotone_up amp_values access_values penalized_values")
    for sigma, window, amp_m, access_m, pen_m, amps, accesses, penalties in summaries:
        print(
            f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {amp_m:d} {access_m:d} {pen_m:d} "
            f"{','.join(f'{x:.4f}' for x in amps)} "
            f"{','.join(f'{x:.4f}' for x in accesses)} "
            f"{','.join(f'{x:.4f}' for x in penalties)}"
        )

    print(
        "\nInterpretation key: if this only says finite Euler amplitude rises while "
        "phase access stays low, it reduces to the existing specificity/promiscuity "
        "and amplitude-vs-phase results."
    )


if __name__ == "__main__":
    main()
