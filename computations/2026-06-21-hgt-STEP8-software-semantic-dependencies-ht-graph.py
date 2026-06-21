#!/usr/bin/env python3
"""THE-MACHINE Step 8 HT transfer.

NODE: semantic dependencies dominate package imports.

Selected minimal HT edit: build a graph on continuum differential samples.
Visible dependency edges are local/formula-syntactic; semantic edges are hidden
constraint edges induced by mirror consistency and phase-carrier class.
"""

import argparse
import math

import mpmath as mp
import numpy as np


BASE_TRANSFER = (
    "package-import closure is compared with semantic-contract closure; mutated "
    "modules reveal silent semantic coupling"
)

ATTEMPTS = {
    "continuum-constraint-graph": (
        "local formula closure is compared with continuum-constraint closure; "
        "mutated strip samples reveal silent semantic coupling"
    ),
    "proof-obligation-graph": (
        "software modules become formal proof obligations; imports are lemma "
        "uses and semantics are hidden assumptions that break under mutation"
    ),
    "api-contract-sheaf": (
        "interfaces become sheaf restrictions on overlapping complex patches; "
        "semantic dependencies are gluing failures invisible from local syntax"
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


def value(kind, s, primes, rng):
    g = gamma_part(s)
    if kind == "gamma-only":
        return g, 0.0
    if kind == "true-lambda":
        p = dlog_zeta(s)
        return g + p, max(0.0, phase_defect(g, p))
    if kind == "zeta-prime":
        p = dlog_zeta(s)
        return p, max(0.0, phase_defect(g, p))
    if kind == "finite-euler":
        p = dlog_finite_euler(s, primes)
        return p, max(0.0, phase_defect(g, p))
    if kind == "random-phase":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        p = abs(base) * complex(math.cos(theta), math.sin(theta))
        return p, max(0.0, phase_defect(g, p))
    raise ValueError(kind)


def closure(edges, seeds):
    seen = set(seeds)
    frontier = list(seeds)
    while frontier:
        i = frontier.pop()
        for j in np.flatnonzero(edges[i]):
            j = int(j)
            if j not in seen:
                seen.add(j)
                frontier.append(j)
    return len(seen)


def build_graph(kind, t0, t1, samples, primes, rng):
    sigmas = [0.3, 0.7]
    nodes = []
    vals = []
    defects = []
    for lane, sigma in enumerate(sigmas):
        for k, t in enumerate(np.linspace(t0, t1, samples)):
            nodes.append((lane, k, sigma, float(t)))
            z, d = value(kind, complex(sigma, float(t)), primes, rng)
            vals.append(z)
            defects.append(d)
    n = len(nodes)
    visible = np.zeros((n, n), dtype=bool)
    semantic = np.zeros((n, n), dtype=bool)
    vals = np.array(vals, dtype=complex)
    defects = np.array(defects, dtype=float)
    high = defects >= np.quantile(defects, 0.75)
    low = defects <= np.quantile(defects, 0.25)
    # Visible formula edges are intentionally tiny: a local finite-difference
    # sample depends only on immediate local neighbors.
    for i, (lane_i, k_i, _, _) in enumerate(nodes):
        for j, (lane_j, k_j, _, _) in enumerate(nodes):
            if lane_i == lane_j and 0 < abs(k_i - k_j) <= 1 and (k_i % 17 == 0):
                visible[i, j] = True
    # Semantic edges: mirror FE-like consistency, plus phase-carrier class.
    for i, (lane_i, k_i, _, _) in enumerate(nodes):
        mirror_j = (1 - lane_i) * samples + k_i
        mirror_resid = abs(vals[i] + np.conjugate(vals[mirror_j])) / (abs(vals[i]) + abs(vals[mirror_j]) + 1e-12)
        if mirror_resid < 0.35:
            semantic[i, mirror_j] = True
        for step in [3, 7, 13]:
            for k_j in [k_i - step, k_i + step]:
                if 0 <= k_j < samples:
                    j = lane_i * samples + k_j
                    if (high[i] and high[j]) or (low[i] and low[j]):
                        semantic[i, j] = True
    return visible, visible | semantic


def attempt_report():
    rows = []
    for name, text in ATTEMPTS.items():
        d = levenshtein(BASE_TRANSFER, text)
        rows.append((d, d / max(len(BASE_TRANSFER), len(text)), name))
    rows.sort()
    print("STEP8 three HT-transfer attempts by Levenshtein from NODE test")
    for d, norm, name in rows:
        marker = "SELECTED" if name == rows[0][2] else "rejected"
        print(f"attempt={name:26s} levenshtein={d:3d} normalized={norm:.4f} {marker}")
    print()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=130)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()
    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    attempt_report()
    print("STEP8/9 software semantic-dependency HT graph")
    print("method=10 test-extreme-cases; gamma-only and random-phase controls probe graph artifacts")
    print(f"samples_per_lane={args.samples} finite_prime_count={args.prime_count}")
    print("kind window seeds visible_q50 visible_q90 semantic_q50 semantic_q90 silent_ratio_q50")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["gamma-only", "true-lambda", "zeta-prime", "finite-euler", "random-phase"]:
            visible, combined = build_graph(kind, window[0], window[1], args.samples, primes, rng)
            n = visible.shape[0]
            for seed_count in [1, 2, 4]:
                vis = []
                sem = []
                ratios = []
                for _ in range(160):
                    seeds = rng.choice(n, size=seed_count, replace=False).tolist()
                    a = closure(visible, seeds)
                    b = closure(combined, seeds)
                    vis.append(a)
                    sem.append(b)
                    ratios.append((b - a) / max(1, a))
                print(
                    f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] {seed_count:5d} "
                    f"{np.quantile(vis,0.5):11.6f} {np.quantile(vis,0.9):11.6f} "
                    f"{np.quantile(sem,0.5):12.6f} {np.quantile(sem,0.9):12.6f} "
                    f"{np.quantile(ratios,0.5):17.6f}"
                )


if __name__ == "__main__":
    main()
