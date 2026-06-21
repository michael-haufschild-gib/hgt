#!/usr/bin/env python3
import math

import mpmath as mp
import numpy as np


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
    if kind == "finite-euler":
        p = dlog_finite_euler(s, primes)
        return p, max(0.0, phase_defect(g, p))
    if kind == "random-phase":
        base = dlog_zeta(s)
        theta = rng.uniform(-math.pi, math.pi)
        p = abs(base) * complex(math.cos(theta), math.sin(theta))
        return p, max(0.0, phase_defect(g, p))
    raise ValueError(kind)


def graph(kind, window, samples, primes, rng):
    vals = []
    defects = []
    for sigma in [0.3, 0.7]:
        for t in np.linspace(window[0], window[1], samples):
            z, d = value(kind, complex(sigma, float(t)), primes, rng)
            vals.append(z)
            defects.append(d)
    vals = np.array(vals, dtype=complex)
    defects = np.array(defects)
    n = len(vals)
    adj = np.zeros((n, n), dtype=float)
    high = defects >= np.quantile(defects, 0.75)
    low = defects <= np.quantile(defects, 0.25)
    for i in range(n):
        lane = 0 if i < samples else 1
        k = i % samples
        mirror = (1 - lane) * samples + k
        resid = abs(vals[i] + np.conjugate(vals[mirror])) / (abs(vals[i]) + abs(vals[mirror]) + 1e-12)
        if resid < 0.35:
            adj[i, mirror] = adj[mirror, i] = 1.0
        for step in [3, 7, 13]:
            for kk in [k - step, k + step]:
                if 0 <= kk < samples:
                    j = lane * samples + kk
                    if (high[i] and high[j]) or (low[i] and low[j]):
                        adj[i, j] = adj[j, i] = 1.0
    return adj


def components(adj):
    n = adj.shape[0]
    seen = np.zeros(n, dtype=bool)
    sizes = []
    for i in range(n):
        if seen[i]:
            continue
        stack = [i]
        seen[i] = True
        size = 0
        while stack:
            u = stack.pop()
            size += 1
            for v in np.flatnonzero(adj[u]):
                if not seen[v]:
                    seen[v] = True
                    stack.append(int(v))
        sizes.append(size)
    return sorted(sizes, reverse=True)


def spectral(adj):
    degree = adj.sum(axis=1)
    lap = np.diag(degree) - adj
    evals = np.linalg.eigvalsh(lap)
    comps = components(adj)
    return {
        "edges": float(adj.sum() / 2.0),
        "components": len(comps),
        "largest_component": comps[0] if comps else 0,
        "lambda2": float(evals[1]) if len(evals) > 1 else 0.0,
        "lambda90": float(np.quantile(evals, 0.9)),
    }


def main():
    rng = np.random.default_rng(20260621)
    primes = first_primes(160)
    print("STEP11 software semantic-dependency spectrum")
    print("method=17 change-representation; closure graph -> Laplacian spectrum")
    print("kind window edges components largest_component lambda2 lambda90")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for kind in ["gamma-only", "true-lambda", "finite-euler", "random-phase"]:
            row = spectral(graph(kind, window, 100, primes, rng))
            print(
                f"{kind:12s} [{window[0]:.0f},{window[1]:.0f}] {row['edges']:.0f} "
                f"{row['components']:10d} {row['largest_component']:17d} "
                f"{row['lambda2']:.6f} {row['lambda90']:.6f}"
            )


if __name__ == "__main__":
    main()
