#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: continuous phase flux maintains assembly.

NODE:
    Energy flux must be continuous to maintain the assembled state.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_continuous_phase_flux_assembly: 6 / 52 = 0.1154
    - C_weld_turnover_maintenance:     23 / 66 = 0.3485
    - B_prime_feed_cutoff_decay:       38 / 72 = 0.5278

    Replace energy flux by the continuum phase-carrier flux
        Delta(s)=max(log|Gamma_infty|,log|P|)-log|Gamma_infty+P|
    along vertical traces in C. An assembled state is a leaky maintained
    variable fed by positive Delta.

STEP 9 method #7:
    Strip it to essentials: one input flux, one decay, one maintained state.
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


def flux_series(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
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


def maintained_state(flux: np.ndarray, threshold: float, decay: float, cutoff_frac: float | None = None) -> np.ndarray:
    state = 0.0
    out = []
    cutoff = len(flux) + 1 if cutoff_frac is None else int(cutoff_frac * len(flux))
    for i, value in enumerate(flux):
        feed = max(0.0, value - threshold) if i < cutoff else 0.0
        state = (1.0 - decay) * state + feed
        out.append(state)
    return np.asarray(out, dtype=float)


def summarize(kind: str, sigma: float, window: tuple[float, float], flux: np.ndarray) -> None:
    threshold = float(np.quantile(flux, 0.50))
    continuous = maintained_state(flux, threshold, decay=0.045, cutoff_frac=None)
    cutoff = maintained_state(flux, threshold, decay=0.045, cutoff_frac=0.55)
    shuffled = maintained_state(np.random.default_rng(8801).permutation(flux), threshold, decay=0.045, cutoff_frac=None)
    cont_plateau = float(np.mean(continuous[-60:]))
    cutoff_plateau = float(np.mean(cutoff[-60:]))
    shuffled_plateau = float(np.mean(shuffled[-60:]))
    print(
        f"{kind:6s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
        f"flux_med={float(np.median(flux)):.4f} flux_q90={float(np.quantile(flux,0.90)):.4f} "
        f"continuous={cont_plateau:.4f} cutoff_tail={cutoff_plateau:.4f} "
        f"cutoff_ratio={cutoff_plateau / max(cont_plateau,1e-12):.4f} "
        f"shuffled={shuffled_plateau:.4f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--prime-count", type=int, default=180)
    args = parser.parse_args()
    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(260621011)
    print("STEP8/9 continuous phase-flux assembly")
    print(f"samples={args.samples} prime_count={args.prime_count}")
    print("kind sigma window flux_med flux_q90 continuous cutoff_tail cutoff_ratio shuffled")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            for kind in ["true", "finite", "random"]:
                summarize(kind, sigma, window, flux_series(kind, sigma, window, args.samples, primes, rng))


if __name__ == "__main__":
    main()
