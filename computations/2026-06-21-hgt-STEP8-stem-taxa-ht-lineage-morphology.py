#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: stem taxa do not necessarily resemble the last common ancestor.

Selected minimal HT edit: separate "constraint-lineage position" from local
continuum differential morphology. The taxon vectors become windows of
log(1+|d/ds log f(s)|), and distance-to-LCA becomes distance-to-a baseline
constraint profile on the same strip.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "phylogenetic position is tested separately from morphology; stem taxa are "
    "side branches with distance to LCA measured; specialization rate varies"
)

ATTEMPTS = {
    "constraint-lineage-distance": (
        "constraint-lineage position is tested separately from continuum "
        "differential morphology; HT branches have distance to a baseline "
        "constraint profile measured; deformation rate varies"
    ),
    "character-mosaic-matrix": (
        "mosaic character vectors are replaced by mixed samples of gamma, zeta, "
        "and finite Euler features; clustering errors test whether local "
        "characters imply analytic lineage"
    ),
    "ghost-branch-interpolation": (
        "unobserved ghost lineages are replaced by interpolating analytic paths "
        "between completed and uncompleted functions; vanished intermediate "
        "profiles are reconstructed from sparse samples"
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


def profile(kind, sigma, window, samples, primes, rng):
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "ancestor-gamma":
            z = g
            delta = 0.0
        elif kind == "true-lambda":
            p = dlog_zeta(s)
            z = g + p
            delta = max(0.0, phase_defect(g, p))
        elif kind == "uncompleted-zeta":
            p = dlog_zeta(s)
            z = p
            delta = max(0.0, phase_defect(g, p))
        elif kind == "finite-euler":
            p = dlog_finite_euler(s, primes)
            z = p
            delta = max(0.0, phase_defect(g, p))
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
            z = p
            delta = max(0.0, phase_defect(g, p))
        else:
            raise ValueError(kind)
        vals.append([math.log1p(abs(z)), delta, math.atan2(z.imag, z.real)])
    arr = np.array(vals, dtype=float)
    arr[:, 2] = np.unwrap(arr[:, 2])
    # normalize each character within a profile so distance is morphology, not scale only
    mean = arr.mean(axis=0)
    std = arr.std(axis=0) + 1e-12
    return (arr - mean) / std


def distance(a, b):
    return float(np.linalg.norm(a - b) / math.sqrt(a.size))


def attempt_report():
    rows = []
    for name, text in ATTEMPTS.items():
        d = levenshtein(BASE_TRANSFER, text)
        rows.append((d, d / max(len(BASE_TRANSFER), len(text)), name))
    rows.sort()
    print("STEP8 three HT-transfer attempts by Levenshtein from NODE test")
    for d, norm, name in rows:
        marker = "SELECTED" if name == rows[0][2] else "rejected"
        print(f"attempt={name:28s} levenshtein={d:3d} normalized={norm:.4f} {marker}")
    print()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.5, (100.0, 170.0)), (0.7, (100.0, 170.0)), (0.3, (500.0, 570.0))]
    kinds = ["true-lambda", "uncompleted-zeta", "finite-euler", "random-phase"]
    attempt_report()
    print("STEP8/9 stem-taxa lineage-vs-morphology transfer")
    print("method=5 make-it-visual; distance bars show local continuum morphology, not lineage position")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("sigma window kind dist_to_gamma dist_to_true dist_to_finite nearest_to_gamma nearest_to_true")
    for sigma, window in cases:
        ancestor = profile("ancestor-gamma", sigma, window, args.samples, primes, rng)
        true = profile("true-lambda", sigma, window, args.samples, primes, rng)
        finite = profile("finite-euler", sigma, window, args.samples, primes, rng)
        rows = {}
        for kind in kinds:
            prof = profile(kind, sigma, window, args.samples, primes, rng)
            rows[kind] = {
                "gamma": distance(prof, ancestor),
                "true": distance(prof, true),
                "finite": distance(prof, finite),
            }
        gamma_nearest = min(rows, key=lambda k: rows[k]["gamma"])
        true_nearest = min([k for k in rows if k != "true-lambda"], key=lambda k: rows[k]["true"])
        for kind in kinds:
            r = rows[kind]
            print(
                f"{sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {kind:16s} "
                f"{r['gamma']:.6f} {r['true']:.6f} {r['finite']:.6f} "
                f"{gamma_nearest:16s} {true_nearest:16s}"
            )
        print("VISUAL distance-to-gamma bars")
        max_d = max(rows[k]["gamma"] for k in rows) + 1e-12
        for kind in kinds:
            width = int(round(30 * rows[kind]["gamma"] / max_d))
            print(f"  {kind:16s} |{'#' * width:<30s}| {rows[kind]['gamma']:.4f}")


if __name__ == "__main__":
    main()
