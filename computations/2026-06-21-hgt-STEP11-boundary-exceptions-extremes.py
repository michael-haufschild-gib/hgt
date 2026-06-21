#!/usr/bin/env python3
"""THE-MACHINE Step 11 for repeated small boundary exceptions.

Method #10: test extreme cases.

The metaphor says a boundary can be technically maintained by dramatic-event
reset while small exceptions accumulate hidden debt. Extremes should decide
whether the HT transfer has content beyond phase-defect distribution:

- permissive boundary: high dramatic trigger, almost no reset;
- strict boundary: every positive defect is enforced/reset;
- low/high debt thresholds;
- right-strip case where true and finite should collapse if this is not new.
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
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def make_panel(sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> dict[str, np.ndarray]:
    rows = {"true": [], "finite": [], "random-phase": []}
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p_true = dlog_zeta(s)
        p_finite = dlog_finite_euler(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        p_random = abs(p_true) * complex(math.cos(theta), math.sin(theta))
        rows["true"].append(max(0.0, phase_defect(g, p_true)))
        rows["finite"].append(max(0.0, phase_defect(g, p_finite)))
        rows["random-phase"].append(max(0.0, phase_defect(g, p_random)))
    out = {k: np.asarray(v, dtype=float) for k, v in rows.items()}
    shuffled = out["true"].copy()
    rng.shuffle(shuffled)
    out["true-shuffled"] = shuffled
    out["true-clipped-sorted"] = np.sort(np.minimum(out["true"], 0.59))
    return out


def debt_stats(values: np.ndarray, *, small_floor: float, dramatic_trigger: float, debt_trigger: float, decay: float, reset: float) -> tuple[float, float, float]:
    debt = 0.0
    max_debt = 0.0
    crises = 0
    for value in values:
        if value >= dramatic_trigger:
            debt *= reset
        elif value > small_floor:
            debt = decay * debt + float(value)
        else:
            debt *= decay
        max_debt = max(max_debt, debt)
        if debt > debt_trigger:
            crises += 1
            debt *= 0.35
    return max_debt, float(crises), float(np.sum((values > small_floor) & (values < dramatic_trigger)))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(20260622)
    cases = [(0.3, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    regimes = {
        "baseline": dict(small_floor=0.02, dramatic_trigger=0.60, debt_trigger=3.8, decay=0.94, reset=0.18),
        "permissive_no_reset": dict(small_floor=0.02, dramatic_trigger=9.99, debt_trigger=3.8, decay=0.98, reset=1.0),
        "strict_every_positive_reset": dict(small_floor=0.02, dramatic_trigger=0.021, debt_trigger=3.8, decay=0.94, reset=0.05),
        "low_debt_trigger": dict(small_floor=0.02, dramatic_trigger=0.60, debt_trigger=1.5, decay=0.94, reset=0.18),
        "high_debt_trigger": dict(small_floor=0.02, dramatic_trigger=0.60, debt_trigger=8.0, decay=0.94, reset=0.18),
    }

    print("STEP11 method #10: extreme cases for boundary-exception debt")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("regime kind sigma window max_debt crises subdramatic_count")
    for sigma, window in cases:
        panel = make_panel(sigma, window, args.samples, primes, rng)
        for regime, params in regimes.items():
            for kind, values in panel.items():
                max_debt, crises, small_count = debt_stats(values, **params)
                print(
                    f"{regime:27s} {kind:19s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{max_debt:.3f} {crises:.0f} {small_count:.0f}"
                )

    print(
        "\nInterpretation: permissive/no-reset and clipped/sorted cases turn the statistic "
        "into total positive phase-defect mass. Strict reset kills all cases. Right-strip "
        "true/finite collapse means the metaphor has no independent HT-native boundary law."
    )


if __name__ == "__main__":
    main()
