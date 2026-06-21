#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase reverse-support gap.

NODE:
    Absolute irreversibility matters when reverse trajectories have zero
    forward probability.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_reverse_support_gap:   12 / 92 = 0.1304
    - B_zero_shadow_support_gap:     17 / 97 = 0.1753
    - C_mirror_protocol_support_gap: 23 / 103 = 0.2233

    Replace trajectory support by support of high phase-carrier events in the
    continuum differential weld. The reverse protocol is the mirror sigma
    lane, read in the reverse height direction.

STEP 9 method #12:
    Find an invariant. Test whether the reverse-support singular mass lambda
    is stable across thresholds/windows and specific to true analytic zeta.
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


def dlog_finite(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def values(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals: list[float] = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite(s, primes)
        elif kind == "random":
            base = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(base) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(phase_defect(g, p))
    return np.asarray(vals, dtype=float)


def support_lambda(forward_vals: np.ndarray, reverse_vals: np.ndarray, q: float) -> dict[str, float]:
    threshold = float(np.quantile(np.r_[forward_vals, reverse_vals], q))
    f = forward_vals > threshold
    reverse_weight = np.maximum(0.0, reverse_vals - threshold)
    if float(reverse_weight.sum()) <= 1e-12:
        return {"lambda": 0.0, "overlap": 0.0, "forward_occ": float(np.mean(f)), "reverse_occ": 0.0}
    lam = float(reverse_weight[~f].sum() / reverse_weight.sum())
    overlap = float(reverse_weight[f].sum() / reverse_weight.sum())
    return {
        "lambda": lam,
        "overlap": overlap,
        "forward_occ": float(np.mean(f)),
        "reverse_occ": float(np.mean(reverse_vals > threshold)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=180)
    args = parser.parse_args()
    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(2606211012)
    print("STEP8/9 phase reverse-support absolute-irreversibility transfer")
    print(f"samples={args.samples} prime_count={args.prime_count}")
    print("kind sigma mirror window q lambda overlap forward_occ reverse_occ finite_identity")
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for sigma in [0.2, 0.3, 0.4]:
            mirror = 1.0 - sigma
            for kind in ["true", "finite", "random"]:
                fwd = values(kind, sigma, window, args.samples, primes, rng)
                rev = values(kind, mirror, window, args.samples, primes, rng)[::-1]
                for q in [0.50, 0.70, 0.85]:
                    row = support_lambda(fwd, rev, q)
                    print(
                        f"{kind:6s} {sigma:.1f} {mirror:.1f} [{window[0]:.0f},{window[1]:.0f}] {q:.2f} "
                        f"{row['lambda']:.4f} {row['overlap']:.4f} "
                        f"{row['forward_occ']:.3f} {row['reverse_occ']:.3f} {1.0-row['lambda']:.4f}"
                    )


if __name__ == "__main__":
    main()
