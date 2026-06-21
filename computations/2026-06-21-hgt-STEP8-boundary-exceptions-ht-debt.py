#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for repeated small boundary exceptions.

NODE constraint:
    Repeated below-trigger boundary exceptions can accumulate precedent debt
    more than one dramatic violation.

Step 8:
    Create three wildly different HT transfers, rank by Levenshtein, and run
    the lowest-distance one.

Step 9 method #20:
    Name the missing lemma. Here the missing lemma is that subthreshold
    cumulative debt is not merely phase-defect mass, positive occupancy, or run
    persistence in disguise.
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
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def run_lengths(mask: np.ndarray) -> list[int]:
    runs: list[int] = []
    cur = 0
    for val in mask:
        if bool(val):
            cur += 1
        elif cur:
            runs.append(cur)
            cur = 0
    if cur:
        runs.append(cur)
    return runs


def boundary_debt(
    values: np.ndarray,
    *,
    small_floor: float,
    dramatic_trigger: float,
    debt_trigger: float,
    decay: float,
) -> dict[str, float]:
    debt = 0.0
    max_debt = 0.0
    crises = 0
    dramatic = 0
    first_crisis = -1
    small_count = 0
    positive_runs = run_lengths(values > small_floor)
    for idx, val in enumerate(values):
        if val >= dramatic_trigger:
            dramatic += 1
            debt *= 0.18
        elif val > small_floor:
            small_count += 1
            debt = decay * debt + float(val)
        else:
            debt = decay * debt
        max_debt = max(max_debt, debt)
        if debt > debt_trigger:
            crises += 1
            if first_crisis < 0:
                first_crisis = idx
            debt *= 0.35
    return {
        "small_count": float(small_count),
        "dramatic_count": float(dramatic),
        "positive_occupancy": float(np.mean(values > small_floor)),
        "median_positive_run": float(np.median(positive_runs)) if positive_runs else 0.0,
        "max_positive_run": float(max(positive_runs)) if positive_runs else 0.0,
        "total_small_mass": float(np.sum(np.where((values > small_floor) & (values < dramatic_trigger), values, 0.0))),
        "max_debt": float(max_debt),
        "crises": float(crises),
        "first_crisis": float(first_crisis),
    }


def defect_panel(
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> dict[str, np.ndarray]:
    rows: dict[str, list[float]] = {
        "true": [],
        "finite": [],
        "ampmatched-finite": [],
        "random-phase": [],
    }
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p_true = dlog_zeta(s)
        p_finite = dlog_finite_euler(s, primes)
        theta = rng.uniform(-math.pi, math.pi)
        p_random = abs(p_true) * complex(math.cos(theta), math.sin(theta))
        p_amp = p_finite * (abs(p_true) / (abs(p_finite) + 1e-300))
        rows["true"].append(max(0.0, phase_defect(g, p_true)))
        rows["finite"].append(max(0.0, phase_defect(g, p_finite)))
        rows["ampmatched-finite"].append(max(0.0, phase_defect(g, p_amp)))
        rows["random-phase"].append(max(0.0, phase_defect(g, p_random)))
    out = {k: np.asarray(v, dtype=float) for k, v in rows.items()}
    shuffled = out["true"].copy()
    rng.shuffle(shuffled)
    out["true-shuffled"] = shuffled
    clipped_sorted = np.sort(np.minimum(out["true"], 0.59))
    out["true-sorted-clipped"] = clipped_sorted
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    kernel = "repeated small exceptions cumulative precedent debt boundary collapse dramatic violation consequence"
    attempts = {
        "small-exception-accumulator": "repeated small exceptions cumulative precedent debt boundary collapse dramatic violation consequence",
        "role-ambiguity-access-map": "ambiguous roles access expectation emotional availability resource dispute boundary",
        "single-spike-repair-test": "dramatic violation consequence repair apology restore access single spike",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:30s} distance={dist}")
    print(f"selected={selected}")
    if selected != "small-exception-accumulator":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #20: name the missing lemma")
    print(
        "Missing lemma: subthreshold cumulative boundary debt for true zeta is not "
        "determined by one-point phase-defect mass, positive occupancy, or run persistence."
    )
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print(
        "kind sigma window small_count dramatic_count pos_occ med_run max_run "
        "total_small_mass max_debt crises first_crisis"
    )

    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(20260621)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    for sigma, window in cases:
        panel = defect_panel(sigma, window, args.samples, primes, rng)
        for kind, values in panel.items():
            row = boundary_debt(
                values,
                small_floor=0.02,
                dramatic_trigger=0.60,
                debt_trigger=3.8,
                decay=0.94,
            )
            print(
                f"{kind:20s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{row['small_count']:.0f} {row['dramatic_count']:.0f} {row['positive_occupancy']:.3f} "
                f"{row['median_positive_run']:.1f} {row['max_positive_run']:.0f} "
                f"{row['total_small_mass']:.3f} {row['max_debt']:.3f} "
                f"{row['crises']:.0f} {row['first_crisis']:.0f}"
            )

    print(
        "\nInterpretation key: if true and true-shuffled/true-sorted-clipped behave "
        "similarly, the missing lemma fails. The observable is then distribution/run "
        "persistence of the phase-carrier defect, not a new boundary-exception mechanism."
    )


if __name__ == "__main__":
    main()
