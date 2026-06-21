#!/usr/bin/env python3
"""THE-MACHINE run: context-dependent catch/slip bond behavior."""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np


@dataclass(frozen=True)
class Context:
    name: str
    catch_scale: float
    slip_scale: float
    catch_length: float
    slip_length: float


@dataclass(frozen=True)
class HTContext:
    name: str
    lambda0: float
    alpha: float
    phase: float


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[j - 1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def classify_curve(values: np.ndarray, forces: np.ndarray) -> tuple[str, float, float]:
    start = float(values[0])
    peak_i = int(np.argmax(values))
    peak = float(values[peak_i])
    end = float(values[-1])
    if start < 1e-9:
        if peak_i not in (0, len(values) - 1) and peak > 1e-3 and peak > end + 1e-3:
            return "emerg", peak, float(forces[peak_i])
        if peak <= 1e-3:
            return "null", 0.0, float(forces[peak_i])
        return "mixed", peak, float(forces[peak_i])
    if peak_i not in (0, len(values) - 1) and peak > 1.15 * max(start, 1e-12) and peak > 1.15 * max(end, 1e-12):
        return "catch", peak / max(start, 1e-12), float(forces[peak_i])
    if np.all(np.diff(values) <= 1e-12):
        return "slip", end / max(start, 1e-12), float(forces[peak_i])
    return "mixed", peak / max(start, 1e-12), float(forces[peak_i])


def node_lifetime(force: np.ndarray, ctx: Context) -> np.ndarray:
    catch_path = ctx.catch_scale * np.exp(-force / ctx.catch_length)
    slip_path = ctx.slip_scale * np.exp(force / ctx.slip_length)
    return 1.0 / (0.015 + catch_path + slip_path)


def run_node() -> None:
    forces = np.asarray([0.0, 1.0, 2.0, 4.0, 6.0, 8.0, 10.0, 13.0, 16.0])
    contexts = [
        Context("cofactor_on", 1.60, 0.030, 3.0, 4.5),
        Context("ion_low", 0.04, 0.360, 2.2, 4.0),
        Context("pH_shift", 1.15, 0.050, 4.8, 3.2),
        Context("glyco_mask", 0.02, 0.560, 2.4, 3.6),
        Context("membrane_anchor", 2.10, 0.020, 4.0, 6.0),
    ]
    print("NODE simulation: context changes catch/slip classification")
    print("context class peak_force peak_ratio lifetimes")
    for ctx in contexts:
        curve = node_lifetime(forces, ctx)
        cls, ratio, peak_force = classify_curve(curve, forces)
        packed = ",".join(f"{x:.3f}" for x in curve)
        print(f"{ctx.name:15s} {cls:5s} {peak_force:5.1f} {ratio:8.3f} {packed}")


def first_primes(n: int) -> tuple[int, ...]:
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


def traces(
    kind: str,
    sigma: float,
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray]:
    gs: list[complex] = []
    ps: list[complex] = []
    for window in [(100.0, 170.0), (500.0, 570.0)]:
        for t in np.linspace(window[0], window[1], samples):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            if kind == "true":
                p = dlog_zeta(s)
            elif kind == "finite":
                p = dlog_finite_euler(s, primes)
            else:
                base = dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p = abs(base) * complex(math.cos(theta), math.sin(theta))
            gs.append(g)
            ps.append(p)
    return np.asarray(gs, dtype=np.complex128), np.asarray(ps, dtype=np.complex128)


def phase_defect(g: np.ndarray, p: np.ndarray) -> np.ndarray:
    return np.log(np.maximum(np.abs(g), np.abs(p)) + 1e-300) - np.log(np.abs(g + p) + 1e-300)


def mean_run(mask: np.ndarray) -> float:
    runs: list[int] = []
    current = 0
    for item in mask:
        if item:
            current += 1
        elif current:
            runs.append(current)
            current = 0
    if current:
        runs.append(current)
    return float(np.mean(runs)) if runs else 0.0


def ht_curve(
    g: np.ndarray,
    p: np.ndarray,
    ctx: HTContext,
    forces: np.ndarray,
    threshold: float,
) -> tuple[np.ndarray, np.ndarray]:
    fractions = []
    runs = []
    phase = complex(math.cos(ctx.phase), math.sin(ctx.phase))
    for force in forces:
        lam = ctx.lambda0 * math.exp(ctx.alpha * float(force))
        defect = phase_defect(g, lam * phase * p)
        mask = defect > threshold
        fractions.append(float(np.mean(mask)))
        runs.append(mean_run(mask))
    return np.asarray(fractions), np.asarray(runs)


def run_levenshtein_selection() -> None:
    node_sig = "context dependent catch bond lifetime under force with cofactors ions pH glycosylation membrane anchoring"
    candidates = [
        "context dependent phase cancellation lifetime under force with sigma phase weight membrane anchoring",
        "context dependent zero shadow bridge topology under force with sigma phase weight membrane anchoring",
        "context dependent prime rebinding markov lifetime under force with sigma phase weight membrane anchoring",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best = None
    for index, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{index} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, index, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")


def run_ht(samples: int, prime_count: int, threshold: float) -> None:
    forces = np.asarray([0.0, 0.75, 1.5, 2.25, 3.0, 3.75, 4.5, 5.25, 6.0])
    contexts = [
        HTContext("cofactor_on", 0.11, 0.43, 0.00),
        HTContext("ion_low", 0.34, 0.06, 0.20),
        HTContext("pH_shift", 0.11, 0.43, 0.85),
        HTContext("glyco_mask", 0.22, 0.25, 1.65),
        HTContext("membrane_anchor", 0.055, 0.58, -0.25),
    ]
    primes = first_primes(prime_count)
    print("\nSTEP8/9 HT transfer: context-modulated phase-cancellation lifetime")
    print(f"threshold={threshold:.3f} samples_per_window={samples} prime_count={prime_count}")
    print("kind sigma context frac_class frac_peak_force frac_peak_metric run_class run_peak_force run_peak_metric fractions runs")
    for sigma in [0.3, 0.5, 1.2]:
        for kind in ["true", "finite", "random"]:
            rng = np.random.default_rng(431000 + int(100 * sigma) + {"true": 1, "finite": 2, "random": 3}[kind])
            g, p = traces(kind, sigma, samples, primes, rng)
            response_word = []
            max_frac = 0.0
            max_run = 0.0
            for ctx in contexts:
                frac, runs = ht_curve(g, p, ctx, forces, threshold)
                frac_cls, frac_ratio, frac_peak = classify_curve(frac, forces)
                run_cls, run_ratio, run_peak = classify_curve(runs, forces)
                response_word.append(f"{ctx.name}:{frac_cls}/{run_cls}")
                max_frac = max(max_frac, float(np.max(frac)))
                max_run = max(max_run, float(np.max(runs)))
                packed_frac = ",".join(f"{x:.4f}" for x in frac)
                packed_runs = ",".join(f"{x:.2f}" for x in runs)
                print(
                    f"{kind:6s} {sigma:.1f} {ctx.name:15s} "
                    f"{frac_cls:5s} {frac_peak:4.2f} {frac_ratio:7.3f} "
                    f"{run_cls:5s} {run_peak:4.2f} {run_ratio:7.3f} "
                    f"{packed_frac} {packed_runs}"
                )
            print(
                f"SUMMARY {kind:6s} {sigma:.1f} "
                f"max_frac={max_frac:.4f} max_run={max_run:.2f} "
                f"response_word={'|'.join(response_word)}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--threshold", type=float, default=1.0)
    args = parser.parse_args()
    run_node()
    run_levenshtein_selection()
    run_ht(args.samples, args.prime_count, args.threshold)


if __name__ == "__main__":
    main()
