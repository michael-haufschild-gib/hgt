#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase-state metastability.

NODE:
    Epigenetic states can be metastable rather than permanently locked.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_state_metastability: 8 / 63 = 0.1270
    - B_zero_shadow_well_escape:  15 / 63 = 0.2381
    - C_memory_barrier_decay:    28 / 63 = 0.4444

    Replace epigenetic state by high/low state of the continuum phase-carrier
    defect Delta(s) along vertical traces in C.

STEP 9 method #16:
    Use a minimal counterexample. Test the false claim "a high phase state is
    permanently locked" by finding finite exits from high-state runs under
    threshold and window sweeps.
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


def series(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
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


def run_lengths(mask: np.ndarray) -> list[int]:
    out: list[int] = []
    cur = 0
    for x in mask:
        if bool(x):
            cur += 1
        elif cur:
            out.append(cur)
            cur = 0
    if cur:
        out.append(cur)
    return out


def metastability(vals: np.ndarray, q: float) -> dict[str, float]:
    threshold = float(np.quantile(vals, q))
    runs = run_lengths(vals > threshold)
    if not runs:
        return {"occupancy": 0.0, "runs": 0.0, "median": 0.0, "max": 0.0, "s8": 0.0, "s32": 0.0, "s64": 0.0, "escape_h": 0.0}
    arr = np.asarray(runs, dtype=float)
    surv = {h: float(np.mean(arr >= h)) for h in [4, 8, 16, 32, 64]}
    escape_h = 0.0
    if surv[4] >= 0.5:
        for h in [8, 16, 32, 64]:
            if surv[h] < 0.5:
                escape_h = float(h)
                break
    return {
        "occupancy": float(np.mean(vals > threshold)),
        "runs": float(len(runs)),
        "median": float(np.median(arr)),
        "max": float(np.max(arr)),
        "s8": surv[8],
        "s32": surv[32],
        "s64": surv[64],
        "escape_h": escape_h,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--prime-count", type=int, default=180)
    args = parser.parse_args()
    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(260621181)
    print("STEP8/9 phase-state metastability")
    print(f"samples={args.samples} prime_count={args.prime_count}")
    print("kind sigma window q occupancy runs median_run max_run survive8 survive32 survive64 escape_h")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for window in [(14.0, 84.0), (100.0, 170.0), (500.0, 570.0)]:
            for kind in ["true", "finite", "random"]:
                vals = series(kind, sigma, window, args.samples, primes, rng)
                for q in [0.50, 0.70, 0.85]:
                    row = metastability(vals, q)
                    print(
                        f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {q:.2f} "
                        f"{row['occupancy']:.3f} {row['runs']:.0f} {row['median']:.1f} {row['max']:.0f} "
                        f"{row['s8']:.3f} {row['s32']:.3f} {row['s64']:.3f} {row['escape_h']:.0f}"
                    )


if __name__ == "__main__":
    main()
