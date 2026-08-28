#!/usr/bin/env python3
"""Corpus-derived numerical falsifiers for the remaining JAS sewing candidates.

Numerics are route-selection evidence only.  Nothing emitted by this program is
used as evidence in a Lean proof.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import os
import platform
import time
from pathlib import Path
from typing import Any

# One BLAS thread per process.  Parallelism is across independent configurations.
for _name in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "NUMEXPR_NUM_THREADS",
):
    os.environ[_name] = "1"

import mpmath as mp
import numpy as np
import scipy
import scipy.linalg
import scipy.sparse


CORPUS_SOURCES = {
    "synchronized_weight": (
        "formal/GaloisForLFunctions/RHTower/"
        "GammaSewnSynchronizedLcmContraction.lean:31-53,408-458"
    ),
    "gamma_multiplier": (
        "formal/GaloisForLFunctions/RHTower/"
        "GammaSewnMobiusValuationContraction.lean:39-49,93-101"
    ),
    "theta_source": (
        "formal/GaloisForLFunctions/RHTower/"
        "ThetaCuspFinitePrimeSource.lean:23-29,183-185,316-318"
    ),
    "theta_reflection": (
        "formal/GaloisForLFunctions/RHTower/ThetaCuspReflection.lean:226"
    ),
    "prime_poisson_moments": (
        "formal/GaloisForLFunctions/HTGeometry/"
        "PrimePoissonProductState.lean:80-221"
    ),
    "bilateral_sewing": (
        "formal/GaloisForLFunctions/RHTower/"
        "BilateralPrimeAnglePacketSewing.lean:121-137"
    ),
}


def first_primes(count: int) -> np.ndarray:
    """Return first count primes using a vectorized Eratosthenes sieve."""
    if count < 1:
        return np.empty(0, dtype=np.int64)
    if count < 6:
        bound = 16
    else:
        c = float(count)
        bound = int(c * (math.log(c) + math.log(math.log(c))) + 32)
    while True:
        sieve = np.ones(bound + 1, dtype=np.bool_)
        sieve[:2] = False
        for p in range(2, math.isqrt(bound) + 1):
            if sieve[p]:
                sieve[p * p :: p] = False
        values = np.flatnonzero(sieve)
        if values.size >= count:
            return values[:count].astype(np.int64)
        bound *= 2


def gamma_multiplier_from_q(q: np.ndarray | float) -> np.ndarray | float:
    """Positive fourth root of corpus theorem multiplier^4=(1+q)^4/(8(1+q^4))."""
    return np.exp(0.25 * (4.0 * np.log1p(q) - math.log(8.0) - np.log1p(q**4)))


def subset_log_weights(x: float, primes: np.ndarray) -> np.ndarray:
    """Log synchronized-lcm weight for every Boolean support."""
    d = int(primes.size)
    count = 1 << d
    logp = np.log(primes.astype(np.float64))
    q = np.exp(-x * logp)
    log_local = (
        np.log(gamma_multiplier_from_q(q))
        - np.log(primes.astype(np.float64) + 1.0)
        + np.log1p(-q)
    )
    out = np.empty(count, dtype=np.float64)
    out[0] = 0.0
    for mask in range(1, count):
        bits = [j for j in range(d) if mask & (1 << j)]
        log_node = -x * float(np.sum(logp[bits]))
        out[mask] = float(np.sum(log_local[bits])) - math.log1p(-math.exp(log_node))
    return out


def creation_operators(x: float, primes: np.ndarray) -> tuple[list[scipy.sparse.csr_matrix], np.ndarray]:
    """Weighted Boolean support insertions F_p|P> = W(P+p)/W(P)|P+p>."""
    d = int(primes.size)
    n = 1 << d
    logw = subset_log_weights(x, primes)
    operators: list[scipy.sparse.csr_matrix] = []
    for j in range(d):
        rows: list[int] = []
        cols: list[int] = []
        data: list[float] = []
        bit = 1 << j
        for mask in range(n):
            if not mask & bit:
                target = mask | bit
                rows.append(target)
                cols.append(mask)
                data.append(math.exp(logw[target] - logw[mask]))
        operators.append(
            scipy.sparse.csr_matrix((data, (rows, cols)), shape=(n, n), dtype=np.float64)
        )
    return operators, logw


def _constraint(left: scipy.sparse.csr_matrix, right: scipy.sparse.csr_matrix) -> scipy.sparse.csr_matrix:
    """Matrix for vec(V left - right V), using column-major vectorization."""
    n = left.shape[0]
    eye = scipy.sparse.eye(n, format="csr")
    return scipy.sparse.kron(left.T, eye, format="csr") - scipy.sparse.kron(
        eye, right, format="csr"
    )


def _gram_spectrum(constraints: list[scipy.sparse.csr_matrix]) -> dict[str, Any]:
    stacked = scipy.sparse.vstack(constraints, format="csr")
    gram = (stacked.T @ stacked).toarray()
    eig = scipy.linalg.eigvalsh(gram, check_finite=False, driver="evd")
    scale = max(float(eig[-1]), 1.0)
    tol = 1.0e-10 * scale
    return {
        "nullity_at_relative_1e-10": int(np.count_nonzero(eig <= tol)),
        "smallest_eigenvalues": [float(v) for v in eig[: min(8, eig.size)]],
        "largest_eigenvalue": float(eig[-1]),
        "relative_smallest": float(max(eig[0], 0.0) / scale),
        "rows": int(stacked.shape[0]),
        "columns": int(stacked.shape[1]),
        "nnz": int(stacked.nnz),
    }


def intertwiner_task(config: tuple[int, float, float]) -> dict[str, Any]:
    d, x, y = config
    primes = first_primes(d)
    fx, logwx = creation_operators(x, primes)
    fy, logwy = creation_operators(y, primes)
    create_constraints = [_constraint(a, b) for a, b in zip(fx, fy)]
    star_constraints = create_constraints + [
        _constraint(a.T.tocsr(), b.T.tocsr()) for a, b in zip(fx, fy)
    ]

    # Flatness gives this exact diagonal creation intertwiner.  Its adjoint
    # residual measures precisely what is lost on imposing the *-relations.
    diagonal = np.exp(logwy - logwx)
    v = scipy.sparse.diags(diagonal, format="csr")
    create_residual = 0.0
    adjoint_residual = 0.0
    source_energy: list[float] = []
    target_energy: list[float] = []
    for a, b in zip(fx, fy):
        create_residual = max(create_residual, float(scipy.sparse.linalg.norm(v @ a - b @ v)))
        adjoint_residual = max(
            adjoint_residual, float(scipy.sparse.linalg.norm(v @ a.T - b.T @ v))
        )
        source_energy.append(float((a.T @ a).diagonal().sum()))
        target_energy.append(float((b.T @ b).diagonal().sum()))

    return {
        "experiment": "finite_star_intertwiner",
        "dimension_primes": d,
        "hilbert_dimension": 1 << d,
        "x": x,
        "y": y,
        "primes": primes.tolist(),
        "creation_only": _gram_spectrum(create_constraints),
        "creation_and_adjoint": _gram_spectrum(star_constraints),
        "canonical_diagonal_creation_residual_fro": create_residual,
        "canonical_diagonal_adjoint_residual_fro": adjoint_residual,
        "source_trace_FstarF": source_energy,
        "target_trace_FstarF": target_energy,
    }


def theta_source_positive_half(x: mp.mpf) -> mp.mpf:
    """Literal corpus theta source on x>=0; n=0 vanishes."""
    scale = mp.exp(x)
    prefactor = mp.exp(x / 2)
    total = mp.mpf("0")
    threshold = mp.power(10, -(mp.mp.dps - 12))
    for n in range(1, 10000):
        t = mp.mpf(n) * scale
        t2 = t * t
        seed = 2 * mp.pi * (2 * mp.pi * t2 * t2 - 3 * t2) * mp.exp(-mp.pi * t2)
        term = prefactor * seed
        total += term
        if n >= 4 and abs(term) <= threshold * max(mp.mpf("1"), abs(total)):
            return total
    raise RuntimeError(f"theta series failed to converge at x={x}")


def theta_moment_task(config: tuple[int, int]) -> tuple[int, str]:
    k, dps = config
    mp.mp.dps = dps

    def integrand(x: mp.mpf) -> mp.mpf:
        phi = theta_source_positive_half(x)
        return 2 * mp.cosh(k * x) * phi * phi

    # Corpus reflection reduces the full-line moment to this positive-half integral.
    cuts = [mp.mpf(v) for v in ("0", ".25", ".5", ".75", "1", "1.5", "2", "3", "4")]
    value = mp.fsum(mp.quad(integrand, [a, b]) for a, b in zip(cuts[:-1], cuts[1:]))
    return k, mp.nstr(value, n=dps - 8)


def _xor_prime_gram(primes: np.ndarray, sigma: float) -> np.ndarray:
    n = 1 << int(primes.size)
    factors = primes.astype(np.float64) ** (-sigma)
    gram = np.empty((n, n), dtype=np.float64)
    xor_value = np.ones(n, dtype=np.float64)
    for mask in range(1, n):
        low = mask & -mask
        j = low.bit_length() - 1
        xor_value[mask] = xor_value[mask ^ low] * factors[j]
    for i in range(n):
        gram[i, :] = xor_value[np.bitwise_xor(i, np.arange(n))]
    return gram


def mixed_gram_task(config: tuple[int, float, float, list[float]]) -> dict[str, Any]:
    d, sigma, x, moments = config
    primes = first_primes(d)
    n = 1 << d
    grades = np.fromiter((mask.bit_count() for mask in range(n)), dtype=np.int64, count=n)
    prime = _xor_prime_gram(primes, sigma)
    theta = np.empty((n, n), dtype=np.float64)
    for i in range(n):
        gi = int(grades[i])
        theta[i, :] = [moments[gi + int(gj)] for gj in grades]
    theta_diag = np.array([moments[2 * int(g)] for g in grades], dtype=np.float64)
    theta_corr = theta / np.sqrt(theta_diag[:, None] * theta_diag[None, :])
    normalized = prime * theta_corr
    logw = subset_log_weights(x, primes)
    weights = np.exp(logw)
    raw = normalized * np.sqrt(theta_diag[:, None] * theta_diag[None, :])
    raw *= weights[:, None] * weights[None, :]

    def stats(matrix: np.ndarray) -> dict[str, Any]:
        try:
            scipy.linalg.cholesky(matrix, lower=True, check_finite=False)
            cholesky = True
        except scipy.linalg.LinAlgError:
            cholesky = False
        eig = scipy.linalg.eigvalsh(matrix, check_finite=False, driver="evd")
        positive = eig[eig > 0]
        return {
            "cholesky_positive_definite_float64": cholesky,
            "smallest_eigenvalues": [float(v) for v in eig[: min(6, n)]],
            "largest_eigenvalue": float(eig[-1]),
            "negative_eigenvalue_count_float64": int(np.count_nonzero(eig < 0)),
            "condition_from_positive_eigenvalues": (
                float(eig[-1] / positive[0]) if positive.size else None
            ),
            "slogdet": [float(v) for v in np.linalg.slogdet(matrix)],
        }

    # Exact algebraic check: diagonal Gamma scaling must cancel on normalization.
    raw_diag = np.diag(raw)
    renormalized_raw = raw / np.sqrt(raw_diag[:, None] * raw_diag[None, :])
    return {
        "experiment": "mixed_prime_theta_gram",
        "dimension_primes": d,
        "packet_count": n,
        "sigma": sigma,
        "x": x,
        "primes": primes.tolist(),
        "normalized": stats(normalized),
        "raw": stats(raw),
        "gamma_normalization_cancellation_max_abs": float(
            np.max(np.abs(renormalized_raw - normalized))
        ),
        "log_weight_range": [float(np.min(logw)), float(np.max(logw))],
    }


def _logsumexp(values: np.ndarray) -> float:
    maximum = float(np.max(values))
    return maximum + math.log(float(np.sum(np.exp(values - maximum))))


def bilateral_tail_task(config: tuple[float, list[int]]) -> dict[str, Any]:
    x, prime_values = config
    primes = np.asarray(prime_values, dtype=np.int64)
    n = np.arange(1, primes.size + 1, dtype=np.float64)
    logp = np.log(primes.astype(np.float64))
    q = np.exp(-x * logp)
    log_c = 0.25 * (4.0 * np.log1p(q) - math.log(8.0) - np.log1p(q**4))
    log_local = log_c - np.log(primes.astype(np.float64) + 1.0) + np.log1p(-q)
    cumulative_logp = np.cumsum(logp)
    log_node = -x * cumulative_logp
    logw = np.cumsum(log_local) - np.log1p(-np.exp(log_node))

    start = primes.size // 2
    design = np.column_stack(
        [n[start:] * np.log(n[start:]), n[start:], np.log(n[start:]), np.ones(primes.size - start)]
    )
    fit, *_ = np.linalg.lstsq(design, -logw[start:], rcond=None)
    prediction = design @ fit
    relative_fit_error = float(
        np.max(np.abs(prediction + logw[start:])) / np.max(np.abs(logw[start:]))
    )

    raw_checkpoints = np.unique(
        np.clip(
            np.concatenate(
                ([1, 2, 3, 5, 10, 100, 1000, 10000, 100000, primes.size],
                 np.geomspace(1, primes.size, 20).astype(np.int64))
            ),
            1,
            primes.size,
        )
    )
    checkpoints = [
        {
            "n": int(i),
            "prime": int(primes[i - 1]),
            "log10_weight": float(logw[i - 1] / math.log(10.0)),
            "minus_log_weight_over_n": float(-logw[i - 1] / i),
            "minus_log_weight_over_n_log_n": (
                float(-logw[i - 1] / (i * math.log(i))) if i > 1 else None
            ),
            "minus_log_weight_over_chebyshev_theta": float(
                -logw[i - 1] / cumulative_logp[i - 1]
            ),
        }
        for i in raw_checkpoints
    ]
    return {
        "experiment": "bilateral_group_completion_tail",
        "x": x,
        "prime_count": int(primes.size),
        "last_prime": int(primes[-1]),
        "checkpoints": checkpoints,
        "positive_tail_log10_energy": float(_logsumexp(2.0 * logw) / math.log(10.0)),
        "reciprocal_tail_log10_energy": float(_logsumexp(-2.0 * logw) / math.log(10.0)),
        "asymptotic_fit_minus_logW": {
            "coefficient_n_log_n": float(fit[0]),
            "coefficient_n": float(fit[1]),
            "coefficient_log_n": float(fit[2]),
            "constant": float(fit[3]),
            "max_relative_error_on_last_half": relative_fit_error,
        },
        "fixed_exponential_gauge_consequence": (
            "nonzero n*log(n) coefficient means no fixed exp(alpha*n) gauge can make "
            "both W_n and 1/W_n polynomially bounded"
        ),
    }


def run_pool(function: Any, configs: list[Any], workers: int) -> list[Any]:
    with concurrent.futures.ProcessPoolExecutor(max_workers=min(workers, len(configs))) as pool:
        return list(pool.map(function, configs))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    parser.add_argument("--max-intertwiner-d", type=int, default=5)
    parser.add_argument("--gram-dimensions", default="4,6,8,10")
    parser.add_argument("--bilateral-primes", type=int, default=1_000_000)
    parser.add_argument("--dps", type=int, default=80)
    args = parser.parse_args()
    started = time.time()

    intertwiner_pairs = [(0.5, 0.5), (0.25, 0.25), (0.25, 0.75), (0.4, 0.6), (0.5, 1.0)]
    intertwiner_configs = [
        (d, x, y)
        for d in range(2, args.max_intertwiner_d + 1)
        for x, y in intertwiner_pairs
    ]
    intertwiners = run_pool(intertwiner_task, intertwiner_configs, args.workers)

    gram_dimensions = sorted({int(v) for v in args.gram_dimensions.split(",") if v})
    max_k = 2 * max(gram_dimensions)
    moment_pairs = run_pool(theta_moment_task, [(k, args.dps) for k in range(max_k + 1)], args.workers)
    moment_strings = dict(moment_pairs)
    moment_floats = [float(moment_strings[k]) for k in range(max_k + 1)]
    gram_parameters = [(0.5, 0.25), (0.5, 0.5), (0.5, 0.75), (0.25, 0.5), (0.75, 0.5)]
    gram_configs = [
        (d, sigma, x, moment_floats)
        for d in gram_dimensions
        for sigma, x in gram_parameters
    ]
    grams = run_pool(mixed_gram_task, gram_configs, args.workers)

    primes = first_primes(args.bilateral_primes)
    bilateral = run_pool(
        bilateral_tail_task,
        [(x, primes.tolist()) for x in (0.25, 0.5, 0.75, 1.0)],
        min(args.workers, 4),
    )

    payload = {
        "status": "complete",
        "warning": "Exploratory route-selection computation only; never Lean proof evidence.",
        "corpus_sources": CORPUS_SOURCES,
        "formulas": {
            "q_p": "exp(-x log p)",
            "gamma_multiplier_fourth_power": "(1+q)^4/(8(1+q^4))",
            "synchronized_weight_nonempty": (
                "prod_p[C(x,p)*(1-q_p)/(p+1)] / (1-prod_p q_p)"
            ),
            "prime_character_gram": "prod_{p in P symmetric_difference Q} p^(-sigma)",
            "theta_grade_gram": (
                "2 integral_0^infinity cosh((r+s)x) thetaCuspFullSource(x)^2 dx"
            ),
        },
        "runtime": {
            "hostname": platform.node(),
            "platform": platform.platform(),
            "python": platform.python_version(),
            "numpy": np.__version__,
            "scipy": scipy.__version__,
            "mpmath": mp.__version__,
            "cpu_count": os.cpu_count(),
            "workers": args.workers,
            "elapsed_seconds": time.time() - started,
        },
        "parameters": {
            "max_intertwiner_d": args.max_intertwiner_d,
            "gram_dimensions": gram_dimensions,
            "bilateral_primes": args.bilateral_primes,
            "decimal_precision_theta_moments": args.dps,
        },
        "theta_moments": {str(k): moment_strings[k] for k in range(max_k + 1)},
        "finite_star_intertwiners": intertwiners,
        "mixed_prime_theta_grams": grams,
        "bilateral_group_completion_tails": bilateral,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": "complete", "output": str(args.output), "elapsed_seconds": payload["runtime"]["elapsed_seconds"]}))


if __name__ == "__main__":
    main()
