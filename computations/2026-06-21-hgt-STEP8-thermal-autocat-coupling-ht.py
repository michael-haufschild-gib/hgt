#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer for thermal-autocatalytic coupling.

NODE:
    Heat release and concentration growth are coupled, so thermal runaway and
    chemical autocatalysis can amplify each other.

Step 8:
    Compare three transfer attempts by Levenshtein distance.

Step 9 method #16:
    Use a minimal counterexample: break or shuffle the coupling between phase
    reserve and amplitude heat, then see whether runaway survives.
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
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
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


def normalized(x: np.ndarray) -> np.ndarray:
    lo = float(np.quantile(x, 0.05))
    hi = float(np.quantile(x, 0.95))
    if hi <= lo + 1e-12:
        return np.zeros_like(x)
    return np.clip((x - lo) / (hi - lo), 0.0, 1.0)


def traces(kind: str, sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], seed: int) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    phase = []
    amp = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        g = gamma_part(s)
        true_p = dlog_zeta(s)
        finite_p = dlog_finite_euler(s, primes)
        if kind == "true":
            p = true_p
        elif kind == "finite":
            p = finite_p
        elif kind == "ampmatched-finite":
            p = finite_p * (abs(true_p) / (abs(finite_p) + 1e-300))
        elif kind == "random-phase":
            theta = float(rng.uniform(-math.pi, math.pi))
            p = abs(true_p) * complex(math.cos(theta), math.sin(theta))
        else:
            raise ValueError(kind)
        d = phase_defect(g, p)
        phase.append(d / (1.0 + d))
        amp.append(math.log1p(abs(p)))
    return np.asarray(phase), normalized(np.asarray(amp))


def coupled_runaway(phase: np.ndarray, heat_src: np.ndarray, mode: str, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    if mode == "shuffled-heat":
        heat_src = heat_src.copy()
        rng.shuffle(heat_src)
    elif mode == "phase-only":
        heat_src = np.zeros_like(heat_src)
    elif mode == "heat-only":
        phase = np.zeros_like(phase)
    elif mode != "coupled":
        raise ValueError(mode)
    c = 0.03
    heat = 0.0
    runaway_t = -1
    max_product = 0.0
    for i, (p, hsrc) in enumerate(zip(phase, heat_src)):
        rate = c * (0.12 + p) * (1.0 + 1.9 * heat)
        c = min(1.0, c + 0.11 * rate)
        heat = max(0.0, 0.82 * heat + 0.28 * hsrc * rate + 0.05 * c - 0.035)
        max_product = max(max_product, c * heat)
        if runaway_t < 0 and c > 0.20 and heat > 0.18:
            runaway_t = i
    return {
        "runaway": float(runaway_t >= 0),
        "runaway_t": float(runaway_t),
        "final_c": float(c),
        "final_heat": float(heat),
        "max_product": float(max_product),
        "phase_mean": float(np.mean(phase)),
        "heat_mean": float(np.mean(heat_src)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=190)
    parser.add_argument("--prime-count", type=int, default=120)
    args = parser.parse_args()

    node = "heat release and concentration growth are coupled so thermal runaway and chemical autocatalysis amplify each other"
    attempts = {
        "phase-release-and-amplitude-growth-are-coupled": "phase release and amplitude growth are coupled so phase runaway and amplitude autocatalysis amplify each other",
        "zero-shadow-thermal-runaway": "zero shadow thermal runaway with autocatalytic phase concentration",
        "prime-heat-autocatalytic-cutoff": "prime heat autocatalytic cutoff growth in the strip",
    }
    distances = {name: levenshtein(node, text) for name, text in attempts.items()}
    selected = min(distances, key=distances.get)
    print("STEP8 transfer attempts by Levenshtein distance")
    for name, dist in sorted(distances.items(), key=lambda item: item[1]):
        print(f"{name:48s} distance={dist} normalized={dist / len(node):.4f}")
    print(f"selected={selected}")
    if selected != "phase-release-and-amplitude-growth-are-coupled":
        raise SystemExit("Selected transfer is not implemented in this script.")

    print("\nSTEP9 method #16: minimal counterexample")
    primes = first_primes(args.prime_count)
    cases = [(0.3, (100.0, 170.0)), (0.3, (500.0, 570.0)), (0.5, (100.0, 170.0)), (1.2, (100.0, 170.0))]
    kinds = ["true", "finite", "ampmatched-finite", "random-phase"]
    modes = ["coupled", "shuffled-heat", "phase-only", "heat-only"]
    print("kind sigma window mode runaway runaway_t final_c final_heat max_product phase_mean heat_mean")
    for c_i, (sigma, window) in enumerate(cases):
        for k_i, kind in enumerate(kinds):
            phase, heat = traces(kind, sigma, window, args.samples, primes, seed=20260621 + 211 * c_i + k_i)
            for mode in modes:
                out = coupled_runaway(phase, heat, mode, seed=303000 + 100 * c_i + 10 * k_i + len(mode))
                print(
                    f"{kind:17s} {sigma:.1f} [{window[0]:.0f},{window[1]:.0f}] {mode:13s} "
                    f"{out['runaway']:.0f} {out['runaway_t']:.0f} {out['final_c']:.6f} {out['final_heat']:.6f} "
                    f"{out['max_product']:.6f} {out['phase_mean']:.6f} {out['heat_mean']:.6f}"
                )
    print(
        "\nInterpretation key: if shuffled-heat or single-component ablations "
        "reproduce coupled runaway, the NODE transfer is not an independent "
        "phase/amplitude feedback finding."
    )


if __name__ == "__main__":
    main()
