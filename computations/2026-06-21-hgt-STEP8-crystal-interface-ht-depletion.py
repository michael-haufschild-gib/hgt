#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: interface supersaturation can differ from measured bulk because of
diffusion/depletion layers.

Selected minimal HT edit: compare bulk strip averages with interface-sigma
values for a continuum differential observable.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "bulk concentration is compared with interface concentration; depletion "
    "makes local growth differ from measured bulk"
)

ATTEMPTS = {
    "bulk-interface-strip": (
        "bulk strip average is compared with interface-sigma differential "
        "content; depletion makes local HT signal differ from measured bulk"
    ),
    "zero-boundary-layer": (
        "bulk zero-density estimates are compared with local zero-neighborhood "
        "layers; depletion is replaced by missing local zero supply"
    ),
    "prime-diffusion-depletion": (
        "finite prime sums diffuse from the convergent half-plane into the "
        "left strip; depletion measures loss of local prime supply"
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


def observable(kind, sigma, t, primes, rng):
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


def summarize(kind, window, primes, rng):
    sigmas = np.linspace(0.2, 0.8, 9)
    ts = np.linspace(window[0], window[1], 180)
    bulk = []
    left = []
    center = []
    right = []
    for t in ts:
        row = np.array([observable(kind, sigma, t, primes, rng) for sigma in sigmas])
        bulk.append(float(row.mean()))
        left.append(float(row[0]))
        center.append(float(row[len(row) // 2]))
        right.append(float(row[-1]))
    bulk = np.array(bulk) + 1e-12
    out = {}
    for label, arr in [("left", left), ("center", center), ("right", right)]:
        arr = np.array(arr)
        ratio = arr / bulk
        out[f"{label}_ratio_med"] = float(np.median(ratio))
        out[f"{label}_depletion_frac"] = float(np.mean(ratio < 0.65))
        out[f"{label}_enrichment_frac"] = float(np.mean(ratio > 1.35))
    return out


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
    print("STEP8/9 crystal interface-depletion HT transfer")
    print("method=15 strengthen-the-conjecture; require side-specific interface/bulk asymmetry, not a raw ratio")
    print(f"finite_prime_count={args.prime_count}")
    print("kind window left_ratio left_depleted left_enriched center_ratio right_ratio right_depleted")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["gamma-only", "true-zeta", "finite-euler", "random-phase"]:
            row = summarize(kind, window, primes, rng)
            print(
                f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] "
                f"{row['left_ratio_med']:.6f} {row['left_depletion_frac']:.6f} {row['left_enrichment_frac']:.6f} "
                f"{row['center_ratio_med']:.6f} {row['right_ratio_med']:.6f} {row['right_depletion_frac']:.6f}"
            )


if __name__ == "__main__":
    main()
