#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: oxygen depletion inside a corrosion pit creates a differential aeration
cell between mouth and bottom.

Selected minimal HT edit: compare a strip "mouth" observable with a hidden
"pit-bottom" observable and measure the log-potential between them.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "mouth oxygen is compared with bottom oxygen; hidden depletion creates a "
    "differential aeration potential"
)

ATTEMPTS = {
    "strip-mouth-bottom": (
        "strip mouth content is compared with pit-bottom content; hidden "
        "depletion creates a differential HT potential"
    ),
    "zero-cavity-cover": (
        "visible zero-neighborhood mouth size is compared with hidden cavity "
        "depth; hidden defects create a failure potential"
    ),
    "prime-oxygen-depletion": (
        "finite prime oxygen supply is compared with analytic-continuation "
        "demand; hidden depletion creates phase potential"
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
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def obs(kind, sigma, t, primes, rng):
    s = complex(float(sigma), float(t))
    g = gamma_part(s)
    if kind == "gamma-only":
        return math.log1p(abs(g))
    if kind == "true-zeta":
        return phase_defect(g, dlog_zeta(s))
    if kind == "finite-euler":
        return phase_defect(g, dlog_finite_euler(s, primes))
    if kind == "random-phase":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        p = abs(base) * complex(math.cos(theta), math.sin(theta))
        return phase_defect(g, p)
    raise ValueError(kind)


def summarize(kind, window, primes, rng, mouth=0.8, bottom=0.2):
    potentials = []
    bottom_depleted = []
    for t in np.linspace(window[0], window[1], 180):
        m = obs(kind, mouth, t, primes, rng)
        b = obs(kind, bottom, t, primes, rng)
        potentials.append(math.log((b + 1e-9) / (m + 1e-9)))
        bottom_depleted.append(float(b < 0.25 * (m + 1e-9)))
    arr = np.array(potentials)
    return {
        "potential_med": float(np.median(arr)),
        "potential_q10": float(np.quantile(arr, 0.10)),
        "potential_q90": float(np.quantile(arr, 0.90)),
        "bottom_depleted_frac": float(np.mean(bottom_depleted)),
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
    print("STEP8/9 pitting differential-aeration HT potential")
    print("method=21 build-dependency-chain; potential => left-bottom phase-defect lower bound + right-mouth depletion")
    print(f"finite_prime_count={args.prime_count}")
    print("kind window potential_q10 potential_med potential_q90 bottom_depleted_frac")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["gamma-only", "true-zeta", "finite-euler", "random-phase"]:
            row = summarize(kind, window, primes, rng)
            print(
                f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] "
                f"{row['potential_q10']:.6f} {row['potential_med']:.6f} {row['potential_q90']:.6f} "
                f"{row['bottom_depleted_frac']:.6f}"
            )


if __name__ == "__main__":
    main()
