#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 transfer: uncertain prime-coefficient pruning.

NODE:
    Error propagation from uncertain rate coefficients into pruning decisions.

STEP 8:
    Levenshtein-minimal HT transfer:
    - A_uncertain_prime_coefficients_pruning: 3 / 67 = 0.0448
    - B_uncertain_phase_jacobian_pruning:    14 / 66 = 0.2121
    - C_uncertain_boundary_transport_pruning: 19 / 68 = 0.2794

    Replace uncertain reaction rates by uncertain finite-prime group
    coefficients in the prime/log-derivative part of
        d/ds log Lambda = Gamma_infty + P.
    Prune groups by their effect on a continuum phase observable over vertical
    windows in C, not by discrete zeta(n) values.

STEP 9 method #2:
    Attack it as false. Controls:
    - random-phase prime-group contributions with matched magnitudes;
    - right-strip sigma=1.2 where finite Euler should collapse toward true;
    - ask whether robust pruning improves the analytic true-zeta carrier, or
      merely keeps more finite groups.
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


def group_contributions(s: complex, groups: list[tuple[int, ...]]) -> np.ndarray:
    vals: list[complex] = []
    for group in groups:
        out = 0.0 + 0.0j
        for p in group:
            q = mp.fp.power(p, -s)
            out -= math.log(p) * q / (1.0 - q)
        vals.append(complex(out))
    return np.asarray(vals, dtype=complex)


def phase_defect_vec(g: np.ndarray, p: np.ndarray) -> np.ndarray:
    return np.log(np.maximum(np.abs(g), np.abs(p)) + 1e-300) - np.log(np.abs(g + p) + 1e-300)


def build_arrays(
    sigma: float,
    window: tuple[float, float],
    samples: int,
    groups: list[tuple[int, ...]],
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    gamma_vals: list[complex] = []
    true_vals: list[complex] = []
    contribs: list[np.ndarray] = []
    for t in np.linspace(window[0], window[1], samples):
        s = complex(float(sigma), float(t))
        gamma_vals.append(gamma_part(s))
        true_vals.append(dlog_zeta(s))
        contribs.append(group_contributions(s, groups))
    return (
        np.asarray(gamma_vals, dtype=complex),
        np.asarray(true_vals, dtype=complex),
        np.vstack(contribs).T,
    )


def random_phase_groups(contrib: np.ndarray, rng: np.random.Generator) -> np.ndarray:
    theta = rng.uniform(-math.pi, math.pi, size=contrib.shape)
    return np.abs(contrib) * (np.cos(theta) + 1j * np.sin(theta))


def group_importance(
    gamma_vals: np.ndarray,
    contrib: np.ndarray,
    threshold: float,
    coeff_sigma: float,
    trials: int,
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    group_count, samples = contrib.shape
    weights_one = np.ones(group_count)
    full_p = weights_one @ contrib
    full_delta = phase_defect_vec(gamma_vals, full_p)
    nominal = np.zeros(group_count)
    for j in range(group_count):
        w = np.ones(group_count)
        w[j] = 0.0
        pruned_delta = phase_defect_vec(gamma_vals, w @ contrib)
        nominal[j] = float(np.median(np.abs(full_delta - pruned_delta)))

    dist = np.zeros((trials, group_count), dtype=float)
    for r in range(trials):
        weights = np.exp(rng.normal(0.0, coeff_sigma, size=group_count))
        p_weighted = weights @ contrib
        delta_weighted = phase_defect_vec(gamma_vals, p_weighted)
        for j in range(group_count):
            w = np.array(weights, copy=True)
            w[j] = 0.0
            delta_without = phase_defect_vec(gamma_vals, w @ contrib)
            dist[r, j] = float(np.median(np.abs(delta_weighted - delta_without)))
    q95 = np.quantile(dist, 0.95, axis=0)
    fail_prob = np.mean(dist > threshold, axis=0)
    return nominal, q95, fail_prob, full_delta


def summarize_case(
    label: str,
    sigma: float,
    window: tuple[float, float],
    samples: int,
    groups: list[tuple[int, ...]],
    threshold: float,
    coeff_sigma: float,
    trials: int,
    rng: np.random.Generator,
) -> None:
    gamma_vals, true_p, finite_contrib = build_arrays(sigma, window, samples, groups)
    true_delta = phase_defect_vec(gamma_vals, true_p)
    for kind, contrib in [
        ("finite", finite_contrib),
        ("random-phase", random_phase_groups(finite_contrib, rng)),
    ]:
        nominal, q95, fail_prob, full_delta = group_importance(
            gamma_vals, contrib, threshold, coeff_sigma, trials, rng
        )
        nominal_keep = nominal >= threshold
        robust_keep = q95 >= threshold
        full_p = np.ones(contrib.shape[0]) @ contrib
        nominal_p = nominal_keep.astype(float) @ contrib
        robust_p = robust_keep.astype(float) @ contrib
        full_err = float(np.median(np.abs(phase_defect_vec(gamma_vals, full_p) - true_delta)))
        nominal_err = float(np.median(np.abs(phase_defect_vec(gamma_vals, nominal_p) - true_delta)))
        robust_err = float(np.median(np.abs(phase_defect_vec(gamma_vals, robust_p) - true_delta)))
        field_rel = float(np.median(np.abs(full_p - true_p) / (np.abs(true_p) + 1e-12)))
        print(
            f"\nCASE {label} kind={kind} sigma={sigma} window=[{window[0]:.0f},{window[1]:.0f}] "
            f"threshold={threshold} coeff_sigma={coeff_sigma}"
        )
        print(
            f"summary kept_nominal={int(np.sum(nominal_keep))}/{len(nominal)} "
            f"kept_robust={int(np.sum(robust_keep))}/{len(nominal)} "
            f"delta_err_full={full_err:.4f} delta_err_nominal={nominal_err:.4f} "
            f"delta_err_robust={robust_err:.4f} field_rel_full={field_rel:.3f}"
        )
        print("group first_prime last_prime nominal q95 fail_prob prune_nominal prune_robust")
        for j, group in enumerate(groups):
            print(
                f"{j:02d} {group[0]:4d} {group[-1]:4d} {nominal[j]:.4f} {q95[j]:.4f} "
                f"{fail_prob[j]:.3f} {int(not nominal_keep[j])} {int(not robust_keep[j])}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=220)
    parser.add_argument("--prime-count", type=int, default=180)
    parser.add_argument("--groups", type=int, default=12)
    parser.add_argument("--threshold", type=float, default=0.035)
    parser.add_argument("--coeff-sigma", type=float, default=0.85)
    parser.add_argument("--trials", type=int, default=220)
    args = parser.parse_args()
    primes = first_primes(args.prime_count)
    group_size = len(primes) // args.groups
    groups = [tuple(primes[i * group_size : (i + 1) * group_size]) for i in range(args.groups)]
    rng = np.random.default_rng(260621152)
    print("STEP8/9 uncertain prime-coefficient pruning")
    print(
        f"samples={args.samples} prime_count={args.prime_count} groups={args.groups} "
        f"group_size={group_size} threshold={args.threshold}"
    )
    for label, sigma, window in [
        ("left_low", 0.3, (100.0, 170.0)),
        ("left_mid", 0.5, (100.0, 170.0)),
        ("right_collapse", 1.2, (100.0, 170.0)),
    ]:
        summarize_case(
            label,
            sigma,
            window,
            args.samples,
            groups,
            args.threshold,
            args.coeff_sigma,
            args.trials,
            rng,
        )


if __name__ == "__main__":
    main()
