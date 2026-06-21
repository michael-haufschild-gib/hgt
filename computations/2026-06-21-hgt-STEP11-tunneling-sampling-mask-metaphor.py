#!/usr/bin/env python3
"""THE-MACHINE Step 11 wild metaphor experiment.

Metaphor: failed intermediates are invisible if the shutter samples the wrong
moments. Strip to essentials: binary excursion intervals plus a sampling mask.
"""

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


def values(kind, sigma, window, samples, primes, rng):
    out = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(sigma, float(t))
        g = gamma_part(s)
        if kind == "true-zeta":
            p = dlog_zeta(s)
        elif kind == "finite-euler":
            p = dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        out.append(max(0.0, phase_defect(g, p)))
    return np.array(out)


def components(vals, low=0.18, high=0.95):
    out = []
    start = None
    for i, v in enumerate(vals):
        if v >= low and start is None:
            start = i
        if start is not None and (v < low or i == len(vals) - 1):
            end = i if v >= low and i == len(vals) - 1 else i - 1
            peak = float(np.max(vals[start : end + 1]))
            out.append((start, end, peak >= high))
            start = None
    return out


def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def mask_indices(name, n, rng):
    if name == "periodic":
        return set(range(0, n, 20))
    if name == "prime-index":
        return {i for i in range(n) if is_prime(i) and i % 4 == 1}
    if name == "golden":
        count = max(1, n // 20)
        phi = (math.sqrt(5.0) - 1.0) / 2.0
        return {int(n * ((k * phi) % 1.0)) for k in range(count)}
    if name == "clustered":
        out = set()
        for start in range(0, n, 100):
            out.update(range(start, min(n, start + 5)))
        return out
    if name == "random":
        return set(np.flatnonzero(rng.random(n) < 0.05).tolist())
    raise ValueError(name)


def observe(comps, mask):
    if not comps:
        return float("nan"), float("nan"), float("nan")
    status = np.array([success for _, _, success in comps])
    seen = []
    for start, end, _ in comps:
        seen.append(any(i in mask for i in range(start, end + 1)))
    seen = np.array(seen, dtype=bool)
    failed = ~status
    success = status
    failed_missed = 1.0 - float(np.mean(seen[failed])) if np.any(failed) else float("nan")
    success_seen = float(np.mean(seen[success])) if np.any(success) else float("nan")
    observed_success = float(np.mean(success[seen])) if np.any(seen) else 0.0
    return failed_missed, success_seen, observed_success


def main():
    rng = np.random.default_rng(20260621)
    primes = first_primes(160)
    masks = ["periodic", "prime-index", "golden", "clustered", "random"]
    cases = [(0.3, (100.0, 170.0)), (0.5, (100.0, 170.0)), (0.3, (500.0, 570.0))]
    print("STEP11 stripped sampling-mask metaphor")
    print("method=7 strip-to-essentials; binary excursion intervals + sampling mask only")
    print("kind sigma window mask density events failed success failed_missed success_seen observed_success")
    for sigma, window in cases:
        for kind in ["true-zeta", "finite-euler", "random-phase"]:
            vals = values(kind, sigma, window, 520, primes, rng)
            comps = components(vals)
            failed = sum(1 for c in comps if not c[2])
            success = sum(1 for c in comps if c[2])
            for mask_name in masks:
                rows = []
                repeats = 12 if mask_name == "random" else 1
                densities = []
                for _ in range(repeats):
                    mask = mask_indices(mask_name, len(vals), rng)
                    densities.append(len(mask) / len(vals))
                    rows.append(observe(comps, mask))
                arr = np.array(rows, dtype=float)
                print(
                    f"{kind:12s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                    f"{mask_name:11s} {np.mean(densities):.4f} {len(comps):3d} {failed:3d} {success:3d} "
                    f"{np.nanmean(arr[:,0]):.6f} {np.nanmean(arr[:,1]):.6f} {np.nanmean(arr[:,2]):.6f}"
                )


if __name__ == "__main__":
    main()
