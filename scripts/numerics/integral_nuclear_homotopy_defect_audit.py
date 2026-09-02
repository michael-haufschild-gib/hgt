#!/usr/bin/env python3
"""Finite falsification audit for ULF-INHD-001.

This script evaluates only source-side objects whose formulas are already proved in
the Lean corpus.  It does not sample Xi zeros or treat numerical evidence as a proof.
"""

import argparse
import itertools
import json
import math
from pathlib import Path

import numpy as np
import mpmath as mp
import sympy as sp
from scipy.optimize import minimize_scalar


COLLISION_SCALE = 115.0 / 864.0


def primes_up_to(limit):
    sieve = np.ones(limit + 1, dtype=np.bool_)
    sieve[:2] = False
    stop = int(math.isqrt(limit))
    for p in range(2, stop + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = False
    return np.flatnonzero(sieve)


def depth_factor(primes, depth_max):
    p = primes.astype(np.float64)
    total = np.zeros_like(p)
    inverse_p_power = np.ones_like(p)
    for depth in range(depth_max + 1):
        total += inverse_p_power / float((depth + 1) ** 3)
        inverse_p_power /= p
    return total


def collision_budget(limit, depth_max, checkpoints):
    primes = primes_up_to(limit)
    p = primes.astype(np.float64)
    logs = np.log(p)
    terms = COLLISION_SCALE * depth_factor(primes, depth_max) / (p * logs * logs)
    prefix = np.cumsum(terms)
    depth_zero_source = COLLISION_SCALE / (p * logs * logs)
    centered_rate = 0.25
    formation_anomaly = COLLISION_SCALE * logs * logs / (centered_rate**4 * p)
    completion_companion = formation_anomaly - depth_zero_source
    source_prefix = np.cumsum(depth_zero_source)
    anomaly_prefix = np.cumsum(formation_anomaly)
    companion_prefix = np.cumsum(completion_companion)
    partials = {}
    anomaly_partials = {}
    for checkpoint in checkpoints:
        index = np.searchsorted(primes, checkpoint, side="right") - 1
        partials[str(checkpoint)] = float(prefix[index]) if index >= 0 else 0.0
        anomaly_partials[str(checkpoint)] = {
            "formation_anomaly": float(anomaly_prefix[index]) if index >= 0 else 0.0,
            "completion_companion": float(companion_prefix[index]) if index >= 0 else 0.0,
            "relative_source_remainder": float(source_prefix[index]) if index >= 0 else 0.0,
            "subtraction_residual": float(
                anomaly_prefix[index] - companion_prefix[index] - source_prefix[index]
            )
            if index >= 0
            else 0.0,
        }

    # For p > X, sum_e p^-e/(e+1)^3 <= X/(X-1).  Monotonicity gives
    # sum_{n>X} 1/(n log(n)^2) <= integral_X^infinity = 1/log X.
    prime_tail_bound = (
        COLLISION_SCALE * (limit / (limit - 1.0)) / math.log(float(limit))
    )
    # Tail in depth for the primes already enumerated.
    inverse_p = 1.0 / p
    depth_tail_bound = COLLISION_SCALE * float(
        np.sum(
            (inverse_p ** (depth_max + 1))
            / float((depth_max + 2) ** 3)
            / (1.0 - inverse_p)
            / (p * logs * logs)
        )
    )
    lower = float(prefix[-1])
    upper = lower + prime_tail_bound + depth_tail_bound
    return {
        "prime_limit": limit,
        "prime_count": int(primes.size),
        "depth_max": depth_max,
        "partials": partials,
        "formation_relative_anomaly_centered_rate": centered_rate,
        "formation_relative_anomaly_partials": anomaly_partials,
        "lower": lower,
        "rigorous_upper": upper,
        "prime_tail_bound": prime_tail_bound,
        "depth_tail_bound": depth_tail_bound,
        "half_base_lower": (108.0 / 115.0) * lower,
        "half_base_rigorous_upper": (108.0 / 115.0) * upper,
    }


def cell_parameters(cells):
    frequencies = []
    amplitudes = []
    for prime, depth in cells:
        logp = math.log(float(prime))
        frequencies.append((depth + 1) * logp)
        amplitudes.append(math.sqrt(logp / float(prime ** (depth + 1))))
    return np.asarray(frequencies), np.asarray(amplitudes)


def base_gram(cells, kappas):
    frequencies, amplitudes = cell_parameters(cells)
    n = len(cells)
    matrix = np.empty((n, n), dtype=np.complex128)
    for i in range(n):
        for j in range(n):
            frequency = frequencies[i] + frequencies[j] + 1j * (kappas[j] - kappas[i])
            matrix[i, j] = amplitudes[i] * amplitudes[j] * 2.0 / frequency**3
    return matrix


def collision_gram(cells, kappas):
    frequencies, amplitudes = cell_parameters(cells)
    n = len(cells)
    matrix = np.empty((n, n), dtype=np.complex128)
    for i in range(n):
        for j in range(n):
            a = frequencies[i]
            b = frequencies[j]
            delta = 1j * (kappas[j] - kappas[i])
            kernel = (
                2.0 / (a + b + delta) ** 3
                - 2.0 / (a + 2.0 * b + delta) ** 3
                - 2.0 / (2.0 * a + b + delta) ** 3
                + 2.0 / (2.0 * a + 2.0 * b + delta) ** 3
            )
            matrix[i, j] = amplitudes[i] * amplitudes[j] * kernel
    return matrix


def aperture_channel_grams(cells, kappas, aperture):
    frequencies, amplitudes = cell_parameters(cells)
    n = len(cells)
    transported = np.empty((n, n), dtype=np.complex128)
    boundary = np.empty((n, n), dtype=np.complex128)
    tail = np.empty((n, n), dtype=np.complex128)
    for i in range(n):
        for j in range(n):
            w = frequencies[i] + frequencies[j] + 1j * (kappas[j] - kappas[i])
            amplitude = amplitudes[i] * amplitudes[j]
            exponential = np.exp(-aperture * w)
            source = amplitude * 2.0 / w**3
            transported[i, j] = exponential * source
            boundary[i, j] = amplitude * (
                2.0 / w**3
                - exponential
                * (aperture**2 / w + 2.0 * aperture / w**2 + 2.0 / w**3)
            )
            tail[i, j] = amplitude * exponential * (
                aperture**2 / w + 2.0 * aperture / w**2
            )
    return transported, boundary, tail


def hermitian_diagnostics(matrix):
    hermitian = (matrix + matrix.conj().T) / 2.0
    eigenvalues = np.linalg.eigvalsh(hermitian)
    singular_values = np.linalg.svd(matrix, compute_uv=False)
    return {
        "hermitian_residual": float(np.linalg.norm(matrix - matrix.conj().T, ord="fro")),
        "min_eigenvalue": float(eigenvalues[0]),
        "max_eigenvalue": float(eigenvalues[-1]),
        "trace_real": float(np.trace(matrix).real),
        "trace_imag": float(np.trace(matrix).imag),
        "trace_norm": float(np.sum(singular_values)),
        "frobenius_norm": float(np.linalg.norm(matrix, ord="fro")),
    }


def packet_audit(cells, kappas):
    base = base_gram(cells, kappas)
    collision = collision_gram(cells, kappas)
    half_base = 0.5 * base
    off_diagonal_ratios = []
    for i in range(len(cells)):
        for j in range(len(cells)):
            if i != j and abs(collision[i, j]) > 1e-30:
                off_diagonal_ratios.append(base[i, j] / collision[i, j])
    diagonal_ratios = np.diag(base) / np.diag(collision)
    idempotence = np.linalg.norm(half_base @ half_base - half_base, ord="fro")
    return {
        "base": hermitian_diagnostics(base),
        "collision": hermitian_diagnostics(collision),
        "half_base": hermitian_diagnostics(half_base),
        "half_base_idempotence_residual": float(idempotence),
        "diagonal_base_collision_ratio_min": float(np.min(diagonal_ratios.real)),
        "diagonal_base_collision_ratio_max": float(np.max(diagonal_ratios.real)),
        "off_diagonal_base_collision_ratio_real_range": [
            float(min(z.real for z in off_diagonal_ratios)),
            float(max(z.real for z in off_diagonal_ratios)),
        ],
        "off_diagonal_base_collision_ratio_imag_range": [
            float(min(z.imag for z in off_diagonal_ratios)),
            float(max(z.imag for z in off_diagonal_ratios)),
        ],
        "best_scalar_collision_to_base_relative_residual": float(
            np.linalg.norm(
                base
                - (
                    np.vdot(collision, base) / np.vdot(collision, collision)
                )
                * collision,
                ord="fro",
            )
            / np.linalg.norm(base, ord="fro")
        ),
    }


def channel_grading_audit(cells, kappas, apertures):
    source = base_gram(cells, kappas)
    source_norm = np.linalg.norm(source, ord="fro")
    rows = []
    for aperture in apertures:
        channels = aperture_channel_grams(cells, kappas, aperture)
        conservation = np.linalg.norm(sum(channels) - source, ord="fro") / source_norm
        candidates = []
        for signs in itertools.product((-1.0, 1.0), repeat=3):
            signed = sum(sign * channel for sign, channel in zip(signs, channels))
            candidates.append(
                (
                    np.linalg.norm(signed, ord="fro") / source_norm,
                    signs,
                    float(np.trace(signed).real),
                )
            )
        best = min(candidates, key=lambda row: row[0])
        rows.append(
            {
                "aperture": aperture,
                "colligation_relative_residual": float(conservation),
                "best_natural_grading_signs": [int(value) for value in best[1]],
                "best_zero_relative_residual": float(best[0]),
                "best_signed_trace": best[2],
            }
        )
    return rows


def optimized_channel_grading_audit(cells, kappas, aperture_max=64.0):
    source = base_gram(cells, kappas)
    source_norm = np.linalg.norm(source, ord="fro")
    candidates = []
    for signs in itertools.product((-1.0, 1.0), repeat=3):
        def objective(aperture):
            channels = aperture_channel_grams(cells, kappas, aperture)
            signed = sum(sign * channel for sign, channel in zip(signs, channels))
            return float(np.linalg.norm(signed, ord="fro") / source_norm)

        grid = np.unique(
            np.concatenate(
                (
                    np.linspace(0.0, 8.0, 4097),
                    np.geomspace(8.0, aperture_max, 513),
                )
            )
        )
        values = np.asarray([objective(float(value)) for value in grid])
        index = int(np.argmin(values))
        lower = float(grid[max(0, index - 1)])
        upper = float(grid[min(len(grid) - 1, index + 1)])
        optimum = minimize_scalar(
            objective,
            bounds=(lower, upper),
            method="bounded",
            options={"xatol": 1e-13, "maxiter": 500},
        )
        aperture = float(optimum.x)
        channels = aperture_channel_grams(cells, kappas, aperture)
        signed = sum(sign * channel for sign, channel in zip(signs, channels))
        candidates.append(
            {
                "signs": [int(value) for value in signs],
                "aperture": aperture,
                "relative_zero_residual": float(objective(aperture)),
                "signed_trace": float(np.trace(signed).real),
                "optimizer_success": bool(optimum.success),
                "global_scan_max_aperture": aperture_max,
            }
        )
    return min(candidates, key=lambda row: row["relative_zero_residual"])


def high_precision_grading_validation(cells, kappas, aperture, signs, digits=80):
    with mp.workdps(digits):
        frequencies = [mp.mpf(depth + 1) * mp.log(prime) for prime, depth in cells]
        amplitudes = [
            mp.sqrt(mp.log(prime) / mp.mpf(prime) ** (depth + 1))
            for prime, depth in cells
        ]
        source_sq = mp.mpf("0")
        signed_sq = mp.mpf("0")
        signed_trace = mp.mpf("0")
        for i in range(len(cells)):
            for j in range(len(cells)):
                w = frequencies[i] + frequencies[j] + mp.j * (kappas[j] - kappas[i])
                amplitude = amplitudes[i] * amplitudes[j]
                exponential = mp.exp(-mp.mpf(aperture) * w)
                source = amplitude * 2 / w**3
                transported = exponential * source
                boundary = amplitude * (
                    2 / w**3
                    - exponential
                    * (
                        mp.mpf(aperture) ** 2 / w
                        + 2 * mp.mpf(aperture) / w**2
                        + 2 / w**3
                    )
                )
                tail = amplitude * exponential * (
                    mp.mpf(aperture) ** 2 / w + 2 * mp.mpf(aperture) / w**2
                )
                signed = signs[0] * transported + signs[1] * boundary + signs[2] * tail
                source_sq += abs(source) ** 2
                signed_sq += abs(signed) ** 2
                if i == j:
                    signed_trace += mp.re(signed)
        return {
            "digits": digits,
            "relative_zero_residual": mp.nstr(mp.sqrt(signed_sq / source_sq), digits),
            "signed_trace": mp.nstr(signed_trace, digits),
        }


def exact_one_cell_audit():
    g = sp.Matrix(
        [
            [sp.Rational(1, 4), sp.Rational(2, 27)],
            [sp.Rational(2, 27), sp.Rational(1, 32)],
        ]
    )
    difference = sp.Matrix([[1, -1]])
    collision = (difference * g * difference.T)[0]
    swap = sp.Matrix([[0, 1], [1, 0]])
    coupling = sp.symbols("coupling", real=True)
    environment = sp.Matrix([[coupling**2, coupling], [coupling, 1]])
    return {
        "doubled_cubic_gram": [[str(value) for value in row] for row in g.tolist()],
        "doubled_cubic_gram_determinant": str(g.det()),
        "collision_diagonal": str(collision),
        "base_over_collision": str(sp.simplify(g[0, 0] / collision)),
        "half_base_over_collision": str(sp.simplify(g[0, 0] / (2 * collision))),
        "aperture_swap_commutator": [
            [str(value) for value in row] for row in (swap * g - g * swap).tolist()
        ],
        "rank_one_environment_block": [
            [str(value) for value in row] for row in environment.tolist()
        ],
        "rank_one_environment_determinant": str(environment.det()),
        "rank_one_environment_schur_short": str(
            sp.simplify(environment[0, 0] - environment[0, 1] * environment[1, 0])
        ),
        "reflection_signed_index_at_multiplicity_one": "0",
        "reflection_unsigned_energy_at_multiplicity_one": "2",
    }


def aperture_eigencharacter_gap_audit(cells, kappas):
    aperture = 0.2
    target_rate = 0.25 + 0.7j
    frequencies, _ = cell_parameters(cells)
    gaps = []
    for frequency, kappa in zip(frequencies, kappas):
        source_rate = frequency + 1j * kappa
        gaps.append(abs(np.exp(-aperture * source_rate) - np.exp(-aperture * target_rate)))
    return {
        "aperture": aperture,
        "synthetic_strict_right_centered_rate": [target_rate.real, target_rate.imag],
        "minimum_eigencharacter_gap": float(min(gaps)),
        "maximum_eigencharacter_gap": float(max(gaps)),
        "gaps": [float(value) for value in gaps],
    }


def random_projection_audit(seed, trials):
    rng = np.random.default_rng(seed)
    dimension = 12
    rank_p = 6
    rank_q = 5

    raw = rng.normal(size=(dimension, dimension)) + 1j * rng.normal(
        size=(dimension, dimension)
    )
    unitary, _ = np.linalg.qr(raw)
    p_nested = unitary[:, :rank_p] @ unitary[:, :rank_p].conj().T
    q_nested = unitary[:, :rank_q] @ unitary[:, :rank_q].conj().T
    nested = hermitian_diagnostics(p_nested - q_nested)

    minimum = math.inf
    maximum_trace_error = 0.0
    for _ in range(trials):
        raw_p = rng.normal(size=(dimension, rank_p)) + 1j * rng.normal(
            size=(dimension, rank_p)
        )
        raw_q = rng.normal(size=(dimension, rank_q)) + 1j * rng.normal(
            size=(dimension, rank_q)
        )
        basis_p, _ = np.linalg.qr(raw_p)
        basis_q, _ = np.linalg.qr(raw_q)
        projection_p = basis_p @ basis_p.conj().T
        projection_q = basis_q @ basis_q.conj().T
        defect = projection_p - projection_q
        trace_norm = float(np.sum(np.linalg.svd(defect, compute_uv=False)))
        minimum = min(minimum, trace_norm)
        maximum_trace_error = max(maximum_trace_error, abs(np.trace(defect).real - 1.0))
    return {
        "dimension": dimension,
        "ranks": [rank_p, rank_q],
        "nested_pair": nested,
        "random_trials": trials,
        "minimum_random_trace_norm": minimum,
        "maximum_trace_integrality_error": maximum_trace_error,
    }


def coherent_zero_audit(cells, kappas):
    rows = []
    for size in range(1, len(cells) + 1):
        half_source = 0.5 * base_gram(cells[:size], kappas[:size])
        eigenvalues, eigenvectors = np.linalg.eigh(
            (half_source + half_source.conj().T) / 2.0
        )
        eigenvalues = np.maximum(eigenvalues, 0.0)
        synthesis = np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T
        positive = synthesis / math.sqrt(2.0)
        negative = synthesis / math.sqrt(2.0)
        defect = positive.conj().T @ positive - negative.conj().T @ negative
        total_mass = float(
            np.trace(positive.conj().T @ positive + negative.conj().T @ negative).real
        )
        rows.append(
            {
                "packet_size": size,
                "defect_trace_norm": float(np.sum(np.linalg.svd(defect, compute_uv=False))),
                "total_factor_mass": total_mass,
                "half_source_trace": float(np.trace(half_source).real),
            }
        )
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-limit", type=int, default=5_000_000)
    parser.add_argument("--depth-max", type=int, default=20)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    checkpoints = [100, 1_000, 10_000, 100_000, 1_000_000, args.prime_limit]
    checkpoints = sorted(set(value for value in checkpoints if value <= args.prime_limit))
    cells = [(2, 0), (3, 0), (2, 1), (5, 0), (3, 1), (7, 0), (11, 0), (2, 2)]
    scenarios = {
        "zero_clock": [0.0] * len(cells),
        "clustered_clock": [index * 1e-7 for index in range(len(cells))],
        "mixed_clock": [0.0, 0.3, -0.2, 1.1, -0.7, 0.05, 2.0, -1.3],
    }

    result = {
        "scope": "source-side finite falsification; no Xi-zero sampling",
        "exact_one_cell": exact_one_cell_audit(),
        "collision_budget": collision_budget(
            args.prime_limit, args.depth_max, checkpoints
        ),
        "packets": {
            name: packet_audit(cells, kappas) for name, kappas in scenarios.items()
        },
        "natural_channel_gradings": {
            name: channel_grading_audit(cells, kappas, [0.0, 0.05, 0.2, 1.0])
            for name, kappas in scenarios.items()
        },
        "optimized_natural_channel_gradings": {
            name: optimized_channel_grading_audit(cells, kappas)
            for name, kappas in scenarios.items()
        },
        "projection_pairs": random_projection_audit(seed=20260902, trials=500),
        "coherent_finite_zero": coherent_zero_audit(cells, scenarios["mixed_clock"]),
        "aperture_eigencharacter_gap": aperture_eigencharacter_gap_audit(
            cells, scenarios["mixed_clock"]
        ),
    }
    result["high_precision_natural_grading_validation"] = {
        name: high_precision_grading_validation(
            cells,
            scenarios[name],
            row["aperture"],
            row["signs"],
        )
        for name, row in result["optimized_natural_channel_gradings"].items()
    }
    payload = json.dumps(result, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)


if __name__ == "__main__":
    main()
