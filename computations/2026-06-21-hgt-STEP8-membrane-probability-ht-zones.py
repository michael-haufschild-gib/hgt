#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: membrane compartments are dynamic probability zones, not fixed boxes.

Selected minimal HT edit: replace particle membership by soft membership in a
continuum differential strip zone. The zone is defined by local phase-defect
probability, while a fixed sigma box is the hard-box control.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "particles have soft membership in a moving probability zone; fixed boxes "
    "misread fuzzy compartment occupancy"
)

ATTEMPTS = {
    "soft-strip-membership": (
        "continuum samples have soft membership in a moving phase-defect zone; "
        "fixed sigma boxes misread fuzzy HT occupancy"
    ),
    "raft-lifetime-excursions": (
        "transient membrane rafts become short-lived analytic excursions; "
        "lifetimes of high-stress patches replace particle membership"
    ),
    "curvature-sorting-map": (
        "membrane curvature sorting becomes sorting of log-derivative vectors "
        "by local strip curvature and phase angle"
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


def defect(kind, sigma, t, primes, rng):
    s = complex(float(sigma), float(t))
    g = gamma_part(s)
    if kind == "true-zeta":
        p = dlog_zeta(s)
    elif kind == "finite-euler":
        p = dlog_finite_euler(s, primes)
    elif kind == "random-phase":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        p = abs(base) * complex(math.cos(theta), math.sin(theta))
    elif kind == "gamma-only":
        return 0.0
    else:
        raise ValueError(kind)
    return max(0.0, phase_defect(g, p))


def zone_metrics(kind, window, primes, rng, sigma_samples=7, t_samples=180):
    sigmas = np.linspace(0.2, 0.8, sigma_samples)
    ts = np.linspace(window[0], window[1], t_samples)
    grid = np.array([[defect(kind, sigma, t, primes, rng) for sigma in sigmas] for t in ts])
    rolling = []
    hard = []
    fuzzy = []
    centers = []
    for row in grid:
        q = float(np.quantile(row, 0.65))
        p = 1.0 / (1.0 + np.exp(-(row - q) / 0.12))
        rolling.append(float(np.mean(p)))
        hard.append(float(np.mean((sigmas < 0.5) & (row > 0.18))))
        fuzzy.append(float(np.mean((p > 0.25) & (p < 0.75))))
        centers.append(float(sigmas[int(np.argmax(p))]))
    rolling = np.array(rolling)
    hard = np.array(hard)
    fuzzy = np.array(fuzzy)
    centers = np.array(centers)
    return {
        "soft_occ_mean": float(rolling.mean()),
        "soft_occ_std": float(rolling.std()),
        "hard_occ_mean": float(hard.mean()),
        "hard_occ_std": float(hard.std()),
        "fuzzy_mean": float(fuzzy.mean()),
        "center_std": float(centers.std()),
        "left_center_frac": float(np.mean(centers < 0.5)),
    }


def attempt_report():
    rows = []
    for name, text in ATTEMPTS.items():
        d = levenshtein(BASE_TRANSFER, text)
        rows.append((d, d / max(len(BASE_TRANSFER), len(text)), name))
    rows.sort()
    print("STEP8 three HT-transfer attempts by Levenshtein from NODE test")
    for d, norm, name in rows:
        marker = "SELECTED" if name == rows[0][2] else "rejected"
        print(f"attempt={name:24s} levenshtein={d:3d} normalized={norm:.4f} {marker}")
    print()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    attempt_report()
    print("STEP8/9 membrane probability-zone HT transfer")
    print("method=2 attack-as-false; gamma-only and random-phase controls must not reproduce the claimed soft-zone structure")
    print(f"finite_prime_count={args.prime_count}")
    print("kind window soft_occ_mean soft_occ_std hard_occ_mean hard_occ_std fuzzy_mean center_std left_center_frac")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["gamma-only", "true-zeta", "finite-euler", "random-phase"]:
            row = zone_metrics(kind, window, primes, rng)
            print(
                f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] "
                f"{row['soft_occ_mean']:.6f} {row['soft_occ_std']:.6f} "
                f"{row['hard_occ_mean']:.6f} {row['hard_occ_std']:.6f} "
                f"{row['fuzzy_mean']:.6f} {row['center_std']:.6f} {row['left_center_frac']:.6f}"
            )


if __name__ == "__main__":
    main()
