#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for mass-transfer catalytic hot spots.

NODE constraint:
    Apparent catalytic hot spots can be transport/supply hot spots, not intrinsic
    active-site hot spots.

Step 8:
    Rank three wildly different HT transfers by Levenshtein and run the lowest.

Step 9 method #20:
    Name the missing lemma. Here: after correcting for a continuum supply field,
    the apparent hot spots of true zeta must remain phase-intrinsic rather than
    denominator/smoothing artifacts.
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


def phase_defect(g: complex, p: complex) -> float:
    return max(0.0, math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300))


def moving_mean(x: np.ndarray, width: int) -> np.ndarray:
    width = max(3, int(width))
    kernel = np.ones(width, dtype=float) / width
    return np.convolve(x, kernel, mode="same")


def panel(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    defect = []
    supply_raw = []
    total_field = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        if kind == "true":
            p = dlog_zeta(s)
        elif kind == "finite":
            p = dlog_finite_euler(s, primes)
        elif kind == "ampmatched-finite":
            p0 = dlog_finite_euler(s, primes)
            pt = dlog_zeta(s)
            p = p0 * (abs(pt) / (abs(p0) + 1e-300))
        elif kind == "random-phase":
            pt = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            p = abs(pt) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        defect.append(phase_defect(g, p))
        supply_raw.append(math.log1p(abs(g) + abs(p)))
        total_field.append(math.log1p(abs(g + p)))
    defect_arr = np.asarray(defect, dtype=float)
    supply = moving_mean(np.asarray(supply_raw, dtype=float), width=max(9, samples // 18)) + 1e-9
    total = np.asarray(total_field, dtype=float)
    return defect_arr, supply, total


def summarize(defect: np.ndarray, supply: np.ndarray, total: np.ndarray) -> dict[str, float]:
    apparent = defect / supply
    intrinsic = defect / np.maximum(np.median(supply), 1e-9)
    top_app = apparent >= np.quantile(apparent, 0.90)
    top_def = defect >= np.quantile(defect, 0.90)
    overlap = float(np.mean(top_app & top_def) / max(np.mean(top_app), 1e-300))
    return {
        "defect_median": float(np.median(defect)),
        "apparent_median": float(np.median(apparent)),
        "apparent_q90": float(np.quantile(apparent, 0.90)),
        "intrinsic_q90": float(np.quantile(intrinsic, 0.90)),
        "supply_top_app": float(np.median(supply[top_app])),
        "supply_bulk": float(np.median(supply)),
        "top_overlap": overlap,
        "corr_app_supply": float(np.corrcoef(apparent, supply)[0, 1]),
        "corr_def_supply": float(np.corrcoef(defect, supply)[0, 1]),
        "total_top_app": float(np.median(total[top_app])),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--prime-count", type=int, default=160)
    args = parser.parse_args()

    kernel = "mass transfer limitation transport supply apparent catalytic hot spot intrinsic activity"
    attempts = {
        "transport-normalized-phase-hotspots": "mass transfer supply normalized apparent phase hot spots intrinsic continuum activity",
        "component-diffusion-film": "diffusion film acts on gamma and prime components before observed rate",
        "finite-prime-supply-layer": "finite prime cutoff creates supply layer and apparent catalytic hot spot",
    }
    distances = {name: levenshtein(kernel, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:34s} distance={dist}")
    print(f"selected={selected}")
    if selected != "transport-normalized-phase-hotspots":
        raise SystemExit("Selected attempt not implemented in this script.")

    print("\nSTEP9 method #20: name the missing lemma")
    print(
        "Missing lemma: true-zeta apparent hot spots remain after transport/supply "
        "normalization and are not denominator artifacts or the old phase-defect observable."
    )
    print(f"samples={args.samples} finite_prime_count={args.prime_count}")
    print(
        "kind sigma window defect_med apparent_med apparent_q90 intrinsic_q90 "
        "supply_top supply_bulk top_overlap corr_app_supply corr_def_supply total_top"
    )

    rng = np.random.default_rng(20260621)
    primes = first_primes(args.prime_count)
    for sigma, window in [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]:
        for kind in ["true", "finite", "ampmatched-finite", "random-phase"]:
            defect, supply, total = panel(kind, sigma, window, args.samples, primes, rng)
            row = summarize(defect, supply, total)
            print(
                f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] "
                f"{row['defect_median']:.6f} {row['apparent_median']:.6f} "
                f"{row['apparent_q90']:.6f} {row['intrinsic_q90']:.6f} "
                f"{row['supply_top_app']:.6f} {row['supply_bulk']:.6f} "
                f"{row['top_overlap']:.3f} {row['corr_app_supply']:.3f} "
                f"{row['corr_def_supply']:.3f} {row['total_top_app']:.6f}"
            )

    print(
        "\nInterpretation key: if apparent hot spots overlap raw defect hot spots and "
        "collapse/right-strip controls match finite behavior, the missing lemma fails."
    )


if __name__ == "__main__":
    main()
