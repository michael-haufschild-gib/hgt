#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: sampling usually misses rare intermediate lineages that fail before
producing successful descendants.

Selected minimal HT edit: replace stochastic lineages by connected excursions
of a continuum differential observable on s = sigma + i t. A fine t-grid is
the hidden ground truth; coarser sampling grids are the experimental readout.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "lineages are sampled on a grid; status is failed or success; missed failed "
    "lineages and success enrichment are measured"
)

ATTEMPTS = {
    "excursion-sampling": (
        "connected excursions of an HT continuum differential phase-defect are "
        "sampled on a grid; status is failed or success; missed failed "
        "excursions and success enrichment are measured"
    ),
    "jet-packet-survival": (
        "Taylor-jet packets around random complex centers are propagated by "
        "finite-difference stability tests; packet death or survival replaces "
        "lineage extinction or success"
    ),
    "antiphase-run-censoring": (
        "runs of negative relative phase between archimedean and prime "
        "components are treated as censored sign intervals; sampling counts "
        "missed sign-runs rather than missed lineages"
    ),
}


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def first_primes(n):
    primes = []
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


def gamma_part(s):
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g, p):
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def component(kind, s, primes, rng):
    if kind == "true-zeta":
        return dlog_zeta(s)
    if kind == "finite-euler":
        return dlog_finite_euler(s, primes)
    if kind == "random-phase":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        return abs(base) * complex(math.cos(theta), math.sin(theta))
    raise ValueError(kind)


def defect_series(kind, sigma, window, samples, primes, rng):
    t0, t1 = window
    values = []
    for t in np.linspace(t0, t1, samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        p = component(kind, s, primes, rng)
        values.append(max(0.0, phase_defect(g, p)))
    return np.array(values, dtype=float)


def excursion_components(values, low, high):
    components = []
    start = None
    for i, value in enumerate(values):
        if value >= low and start is None:
            start = i
        if start is not None and (value < low or i == len(values) - 1):
            end = i if value >= low and i == len(values) - 1 else i - 1
            block = values[start : end + 1]
            peak = float(np.max(block))
            components.append((start, end, "success" if peak >= high else "failed", peak))
            start = None
    return components


def sampling_summary(values, components, stride, low):
    if not components:
        return None
    totals = []
    failed_seen = []
    success_seen = []
    enrichments = []
    status = np.array([c[2] for c in components])
    true_success = float(np.mean(status == "success"))
    for offset in range(stride):
        sampled = set(range(offset, len(values), stride))
        seen = []
        for start, end, _, _ in components:
            hit = any(i in sampled and values[i] >= low for i in range(start, end + 1))
            seen.append(hit)
        seen = np.array(seen, dtype=bool)
        totals.append(float(np.mean(seen)))
        failed = status == "failed"
        success = status == "success"
        failed_seen.append(float(np.mean(seen[failed])) if np.any(failed) else math.nan)
        success_seen.append(float(np.mean(seen[success])) if np.any(success) else math.nan)
        observed_success = float(np.mean(success[seen])) if np.any(seen) else 0.0
        enrichments.append(observed_success / true_success if true_success > 0.0 else math.nan)
    return {
        "observed_frac": float(np.nanmean(totals)),
        "failed_seen": float(np.nanmean(failed_seen)),
        "failed_missed": float(1.0 - np.nanmean(failed_seen)),
        "success_seen": float(np.nanmean(success_seen)),
        "success_enrichment": float(np.nanmean(enrichments)),
    }


def print_step8_attempts():
    scored = []
    for name, text in ATTEMPTS.items():
        distance = levenshtein(BASE_TRANSFER, text)
        scored.append((distance, distance / max(len(BASE_TRANSFER), len(text)), name))
    scored.sort()
    print("STEP8 three HT-transfer attempts by Levenshtein from NODE test")
    for distance, normalized, name in scored:
        marker = "SELECTED" if name == scored[0][2] else "rejected"
        print(f"attempt={name:22s} levenshtein={distance:3d} normalized={normalized:.4f} {marker}")
    print()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=520)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--low", type=float, default=0.18)
    parser.add_argument("--high", type=float, default=0.95)
    args = parser.parse_args()

    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    cases = [
        (0.3, (100.0, 170.0)),
        (0.5, (100.0, 170.0)),
        (0.7, (100.0, 170.0)),
        (0.3, (500.0, 570.0)),
    ]
    kinds = ["true-zeta", "finite-euler", "random-phase"]
    print_step8_attempts()
    print("STEP8/9 continuum excursion sampling")
    print(
        "method=19 write-the-fake-proof; wished proof: coarse sampling hides failed "
        "HT phase-defect excursions and enriches observed successful ones; gap tested "
        "below by threshold sensitivity"
    )
    print(f"samples={args.samples} low={args.low} high={args.high} finite_prime_count={args.prime_count}")
    print(
        "kind sigma window events failed success stride observed_frac "
        "failed_missed_frac success_seen_frac success_enrichment median peak_q90"
    )
    for sigma, window in cases:
        for kind in kinds:
            values = defect_series(kind, sigma, window, args.samples, primes, rng)
            components = excursion_components(values, args.low, args.high)
            failed = sum(1 for c in components if c[2] == "failed")
            success = sum(1 for c in components if c[2] == "success")
            med = float(np.median(values))
            q90 = float(np.quantile(values, 0.90))
            for stride in [2, 5, 10, 20, 40]:
                row = sampling_summary(values, components, stride, args.low)
                if row is None:
                    print(
                        f"{kind:12s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                        f"0 0 0 {stride:2d} nan nan nan nan {med:.6g} {q90:.6g}"
                    )
                    continue
                print(
                    f"{kind:12s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{len(components):3d} {failed:3d} {success:3d} {stride:2d} "
                    f"{row['observed_frac']:.6f} {row['failed_missed']:.6f} "
                    f"{row['success_seen']:.6f} {row['success_enrichment']:.6f} "
                    f"{med:.6g} {q90:.6g}"
                )
            print(
                f"METHOD19_GAP_SWEEP kind={kind} sigma={sigma:.1f} "
                f"window=[{window[0]:.0f},{window[1]:.0f}] stride=20"
            )
            print("  low high events failed success failed_missed success_seen enrichment")
            for low, high in [(0.12, 0.70), (0.18, 0.95), (0.24, 1.20), (0.32, 1.50)]:
                sweep_components = excursion_components(values, low, high)
                row = sampling_summary(values, sweep_components, 20, low)
                sweep_failed = sum(1 for c in sweep_components if c[2] == "failed")
                sweep_success = sum(1 for c in sweep_components if c[2] == "success")
                if row is None:
                    print(f"  {low:.2f} {high:.2f} 0 0 0 nan nan nan")
                else:
                    print(
                        f"  {low:.2f} {high:.2f} {len(sweep_components)} "
                        f"{sweep_failed} {sweep_success} {row['failed_missed']:.6f} "
                        f"{row['success_seen']:.6f} {row['success_enrichment']:.6f}"
                    )


if __name__ == "__main__":
    main()
