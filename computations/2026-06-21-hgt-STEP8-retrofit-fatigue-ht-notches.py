#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for retrofit fatigue details.

NODE constraint:
    Later retrofits introduce local stress concentrators; fatigue damage is the
    nonlinear, local, history-weighted result of those concentrations.

Step 8:
    Rank three wildly different HT transfers by Levenshtein and run the lowest.

Step 9 method #6:
    Ask what action is happening. The action is: concentrate sparse local stress
    and exponentiate it into fatigue damage. The reduction check is whether this
    is merely a zero/proximity spike or p-norm roughness detector.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = cur
    return prev[-1]


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


def dlog_finite_euler(s: complex, primes: tuple[int, ...]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def series(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> np.ndarray:
    vals = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "gamma-only":
            z = g
        elif kind == "true-zeta":
            z = g + dlog_zeta(s)
        elif kind == "finite-euler":
            z = g + dlog_finite_euler(s, primes)
        elif kind == "random-phase":
            p = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            z = g + abs(p) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        vals.append(math.log1p(abs(z)))
    return np.asarray(vals, dtype=float)


def notch_mask(values: np.ndarray, *, kind: str, rng: np.random.Generator, fraction: float) -> np.ndarray:
    n = len(values)
    count = max(1, int(round(fraction * n)))
    mask = np.zeros(n, dtype=bool)
    if kind == "periodic":
        idx = np.linspace(0, n - 1, count, dtype=int)
    elif kind == "random":
        idx = rng.choice(n, size=count, replace=False)
    elif kind == "bad-retrofit":
        grad = np.abs(np.gradient(values))
        idx = np.argsort(grad)[-count:]
    else:
        raise ValueError(kind)
    mask[idx] = True
    return mask


def damage(values: np.ndarray, mask: np.ndarray, *, kt: float, endurance_quantile: float, exponent: float) -> dict[str, float]:
    endurance = float(np.quantile(values, endurance_quantile))
    base_active = np.maximum(values - endurance, 0.0)
    retrofit_values = values.copy()
    retrofit_values[mask] *= kt
    retrofit_active = np.maximum(retrofit_values - endurance, 0.0)
    base_damage = float(np.sum(base_active**exponent))
    retrofit_damage = float(np.sum(retrofit_active**exponent))
    notch_share = float(np.sum(retrofit_active[mask] ** exponent) / max(retrofit_damage, 1e-300))
    return {
        "endurance": endurance,
        "base_damage": base_damage,
        "retrofit_damage": retrofit_damage,
        "amplification": retrofit_damage / max(base_damage, 1e-300),
        "notch_share": notch_share,
        "notch_mean": float(np.mean(values[mask])),
        "bulk_mean": float(np.mean(values)),
        "notch_q90": float(np.quantile(values[mask], 0.90)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=240)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    kernel = "retrofit drilled holes service penetrations equipment mounts local stress concentration fatigue damage"
    attempts = {
        "strip-notch-amplifier": "retrofit notches local stress concentration on continuum strip fatigue damage",
        "prime-mount-cutoff": "finite prime equipment mounts add cutoff loads and fatigue damage",
        "zero-penetration-cavity": "service penetration holes around zero neighborhoods amplify cavity damage",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:24s} distance={dist}")
    print(f"selected={selected}")
    if selected != "strip-notch-amplifier":
        raise SystemExit("Selected attempt is not implemented here.")

    print("\nSTEP9 method #6: ask what action is happening")
    print("action=local sparse stress concentration, then nonlinear fatigue exponentiation")
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print("kind sigma window notch_pattern base_damage retrofit_damage amplification notch_share notch_mean bulk_mean notch_q90 endurance")

    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0)), (0.3, (500.0, 570.0))]
    for sigma, window in cases:
        for kind in ["gamma-only", "true-zeta", "finite-euler", "random-phase"]:
            vals = series(kind, sigma, window, args.samples, primes, rng)
            for pattern in ["periodic", "random", "bad-retrofit"]:
                mask = notch_mask(vals, kind=pattern, rng=rng, fraction=0.08)
                row = damage(vals, mask, kt=2.4, endurance_quantile=0.70, exponent=5.0)
                print(
                    f"{kind:12s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {pattern:12s} "
                    f"{row['base_damage']:.6e} {row['retrofit_damage']:.6e} {row['amplification']:.3e} "
                    f"{row['notch_share']:.3f} {row['notch_mean']:.5f} {row['bulk_mean']:.5f} "
                    f"{row['notch_q90']:.5f} {row['endurance']:.5f}"
                )

    print(
        "\nInterpretation key: a non-reducing result would need notch amplification not "
        "explained by local roughness/zero proximity or by choosing high-gradient/high-value "
        "notch sites. If bad-retrofit dominates for every rough control, this is a p-norm "
        "stress-concentration artifact."
    )


if __name__ == "__main__":
    main()
