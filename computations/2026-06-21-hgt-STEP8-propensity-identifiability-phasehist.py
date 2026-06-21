#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: phase-histogram identifiability.

NODE:
    Different uncertain propensity models can fit the same observed count data.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_phase_histogram_hidden_transitions:      36 / 102 = 0.3529
    - C_amplitude_distribution_hidden_phase:     38 / 104 = 0.3654
    - B_zero_shadow_occupancy_hidden_topology:   53 / 108 = 0.4907

    Replace observed count histogram by observed phase-defect histogram for
    the continuum differential weld
        Delta(s)=max(log|Gamma_infty|,log|P|)-log|Gamma_infty+P|.
    Compare true zeta, finite Euler, random-phase, and histogram-matched
    controls whose marginal Delta distribution is exactly the same as true.

STEP 9 method #21:
    Build a dependency chain:
    same histogram -> need transition structure -> need run/edge structure ->
    check boundary and controls.
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


def phase_series(
    kind: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: tuple[int, ...],
    rng: np.random.Generator,
) -> np.ndarray:
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


def quantile_map(source: np.ndarray, target: np.ndarray) -> np.ndarray:
    order = np.argsort(source, kind="mergesort")
    target_sorted = np.sort(target)
    out = np.zeros_like(source, dtype=float)
    out[order] = target_sorted
    return out


def js_hist(a: np.ndarray, b: np.ndarray, bins: int) -> float:
    lo = min(float(np.min(a)), float(np.min(b)))
    hi = max(float(np.max(a)), float(np.max(b)))
    if hi <= lo:
        return 0.0
    pa, edges = np.histogram(a, bins=bins, range=(lo, hi), density=False)
    pb, _ = np.histogram(b, bins=edges, density=False)
    p = pa.astype(float) + 1e-12
    q = pb.astype(float) + 1e-12
    p /= p.sum()
    q /= q.sum()
    m = 0.5 * (p + q)
    return math.sqrt(0.5 * float(np.sum(p * np.log(p / m))) + 0.5 * float(np.sum(q * np.log(q / m))))


def run_lengths(mask: np.ndarray) -> list[int]:
    out: list[int] = []
    cur = 0
    for value in mask:
        if bool(value):
            cur += 1
        elif cur:
            out.append(cur)
            cur = 0
    if cur:
        out.append(cur)
    return out


def edge_softness(vals: np.ndarray, threshold: float, band: float) -> tuple[int, float, float]:
    events = []
    for i in range(1, len(vals)):
        if (vals[i - 1] - threshold) * (vals[i] - threshold) <= 0 and vals[i - 1] != vals[i]:
            left = i
            while left > 0 and abs(vals[left] - threshold) <= band:
                left -= 1
            right = i
            while right < len(vals) - 1 and abs(vals[right] - threshold) <= band:
                right += 1
            width = max(1, right - left)
            slope = abs(vals[right] - vals[left]) / width
            events.append(width / max(slope, 1e-9))
    if not events:
        return 0, 0.0, 0.0
    return len(events), float(np.median(events)), float(np.mean(events))


def transition_entropy(states: np.ndarray) -> float:
    counts = np.ones((4, 4), dtype=float)
    for a, b in zip(states[:-1], states[1:]):
        counts[int(a), int(b)] += 1.0
    probs = counts / counts.sum(axis=1, keepdims=True)
    ent = -np.sum(probs * np.log(probs), axis=1)
    weights = counts.sum(axis=1) / counts.sum()
    return float(np.dot(weights, ent))


def metrics(vals: np.ndarray, true_vals: np.ndarray) -> dict[str, float]:
    threshold = float(np.median(true_vals))
    band = max(0.04, 0.25 * float(np.std(true_vals)))
    mask = vals > threshold
    runs = run_lengths(mask)
    if float(np.std(vals)) < 1e-12:
        ac1 = 0.0
        ac8 = 0.0
    else:
        ac1 = float(np.corrcoef(vals[:-1], vals[1:])[0, 1])
        ac8 = float(np.corrcoef(vals[:-8], vals[8:])[0, 1]) if len(vals) > 16 else 0.0
    qs = np.quantile(true_vals, [0.25, 0.50, 0.75])
    states = np.digitize(vals, qs)
    events, soft_med, soft_mean = edge_softness(vals, threshold, band)
    return {
        "hist_js": js_hist(vals, true_vals, 24),
        "occupancy": float(np.mean(mask)),
        "run_med": float(np.median(runs)) if runs else 0.0,
        "run_q90": float(np.quantile(runs, 0.90)) if runs else 0.0,
        "acf1": ac1,
        "acf8": ac8,
        "trans_entropy": transition_entropy(states),
        "edge_events": float(events),
        "edge_soft_med": soft_med,
        "edge_soft_mean": soft_mean,
    }


def case_report(sigma: float, window: tuple[float, float], samples: int, primes: tuple[int, ...], rng: np.random.Generator) -> None:
    true_vals = phase_series("true", sigma, window, samples, primes, rng)
    finite_vals = phase_series("finite", sigma, window, samples, primes, rng)
    random_vals = phase_series("random", sigma, window, samples, primes, rng)
    controls = {
        "true": true_vals,
        "finite_raw": finite_vals,
        "random_raw": random_vals,
        "finite_histmatched": quantile_map(finite_vals, true_vals),
        "random_histmatched": quantile_map(random_vals, true_vals),
        "true_shuffled": rng.permutation(true_vals),
    }
    print(f"\nCASE sigma={sigma:.1f} window=[{window[0]:.0f},{window[1]:.0f}]")
    print(
        "series hist_js occupancy run_med run_q90 acf1 acf8 trans_entropy "
        "edge_events edge_soft_med edge_soft_mean"
    )
    base = metrics(true_vals, true_vals)
    for name, vals in controls.items():
        row = metrics(vals, true_vals)
        print(
            f"{name:20s} {row['hist_js']:.4f} {row['occupancy']:.3f} "
            f"{row['run_med']:.1f} {row['run_q90']:.1f} {row['acf1']:+.3f} {row['acf8']:+.3f} "
            f"{row['trans_entropy']:.3f} {row['edge_events']:.0f} "
            f"{row['edge_soft_med']:.2f} {row['edge_soft_mean']:.2f}"
        )
    print(
        "dependency_chain "
        f"hist_ok_finite={metrics(controls['finite_histmatched'], true_vals)['hist_js']:.4f} "
        f"hist_ok_random={metrics(controls['random_histmatched'], true_vals)['hist_js']:.4f} "
        f"true_run_q90={base['run_q90']:.1f}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--prime-count", type=int, default=180)
    args = parser.parse_args()
    primes = first_primes(args.prime_count)
    rng = np.random.default_rng(260621091)
    print("STEP8/9 phase-histogram identifiability transfer")
    print(f"samples={args.samples} prime_count={args.prime_count}")
    print("Same marginal phase histogram is forced by quantile mapping; hidden transition statistics are then tested.")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        for window in [(100.0, 170.0), (500.0, 570.0)]:
            case_report(sigma, window, args.samples, primes, rng)


if __name__ == "__main__":
    main()
