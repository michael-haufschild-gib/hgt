#!/usr/bin/env python3
"""Finite-section audit of the exact Gamma--valuation Schur subtraction.

For unit aperture and prime p, the Lean source coordinate is

    f_e(p) = sqrt(q_p) (1-q_p) q_p^e,  q_p = 1/p.

The completed Gram K=sum_{e>=0} f_e f_e^T and exact Gamma subtraction
K-f_0 f_0^T=sum_{e>=1} f_e f_e^T are therefore positive.  This script
checks finite sections, evaluates deliberate over-subtractions, and records
the exact Cauchy determinant threshold

    alpha_crit = 1 / (1 - product(q_p)^2).

It is a diagnostic of the proposed negative-index mechanism, not evidence
about Xi zeros and not a substitute for the exact Lean identities.
"""

import argparse
import json
import math
import time
from pathlib import Path

import mpmath as mp
import numpy as np


def first_primes(count):
    if count <= 0:
        return []
    limit = max(16, int(count * (math.log(max(count, 2)) + math.log(math.log(max(count, 3))))) + 16)
    while True:
        sieve = bytearray(b"\x01") * (limit + 1)
        sieve[0:2] = b"\x00\x00"
        for p in range(2, math.isqrt(limit) + 1):
            if sieve[p]:
                start = p * p
                sieve[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
        primes = [n for n in range(2, limit + 1) if sieve[n]]
        if len(primes) >= count:
            return primes[:count]
        limit *= 2


def parse_csv(text, cast):
    return [cast(item.strip()) for item in text.split(",") if item.strip()]


def inertia(eigenvalues, tolerance):
    negative = int(np.count_nonzero(eigenvalues < -tolerance))
    zero = int(np.count_nonzero(np.abs(eigenvalues) <= tolerance))
    positive = int(np.count_nonzero(eigenvalues > tolerance))
    return {"negative": negative, "zero": zero, "positive": positive}


def write_result(path, result):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", default="1,2,3,4,6,8,12,16,24,32,48,64")
    parser.add_argument("--alphas", default="1,1.000001,1.001,1.01,1.1,2")
    parser.add_argument("--dps", type=int, default=100)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    sizes = sorted(set(parse_csv(args.sizes, int)))
    alphas = parse_csv(args.alphas, float)
    if not sizes or sizes[0] <= 0:
        raise SystemExit("--sizes must contain positive integers")
    if not alphas or any(alpha < 1 for alpha in alphas):
        raise SystemExit("--alphas must contain values at least one")

    mp.mp.dps = args.dps
    primes = first_primes(sizes[-1])
    started = time.time()
    sections = []

    for size in sizes:
        section_primes = primes[:size]
        q = 1.0 / np.asarray(section_primes, dtype=np.float64)
        d = np.sqrt(q) * (1.0 - q)
        q_pair = np.outer(q, q)
        d_pair = np.outer(d, d)
        total = d_pair / (1.0 - q_pair)
        vacuum = d_pair
        residual = total - vacuum
        residual_closed = d_pair * q_pair / (1.0 - q_pair)
        closed_form_error = float(np.linalg.norm(residual - residual_closed, ord="fro"))

        log_primorial = mp.fsum(mp.log(p) for p in section_primes)
        primorial_inverse_sq = mp.exp(-2 * log_primorial)
        alpha_critical = 1 / (1 - primorial_inverse_sq)

        matrices = []
        for alpha in alphas:
            matrix = total - alpha * vacuum
            eigenvalues = np.linalg.eigvalsh(matrix)
            scale = max(1.0, float(np.max(np.abs(eigenvalues))))
            tolerance = 1000 * np.finfo(np.float64).eps * size * scale
            matrix_trace = float(np.trace(matrix))
            trace_norm = float(np.sum(np.abs(eigenvalues)))
            matrices.append(
                {
                    "alpha": alpha,
                    "inertia_at_reported_tolerance": inertia(eigenvalues, tolerance),
                    "minimum_eigenvalue": float(eigenvalues[0]),
                    "maximum_eigenvalue": float(eigenvalues[-1]),
                    "trace": matrix_trace,
                    "trace_norm": trace_norm,
                    "abs_trace_to_trace_norm_ratio": (
                        abs(matrix_trace) / trace_norm if trace_norm else 0.0
                    ),
                    "eigenvalue_tolerance": tolerance,
                }
            )

        sections.append(
            {
                "size": size,
                "largest_prime": section_primes[-1],
                "primorial_inverse_squared": mp.nstr(primorial_inverse_sq, args.dps),
                "alpha_critical_exact_formula": mp.nstr(alpha_critical, args.dps),
                "alpha_critical_minus_one": mp.nstr(alpha_critical - 1, args.dps),
                "exact_subtraction_closed_form_frobenius_error_float64": closed_form_error,
                "matrices": matrices,
            }
        )

    result = {
        "metadata": {
            "sizes": sizes,
            "alphas": alphas,
            "mpmath_dps": args.dps,
            "numpy_version": np.__version__,
            "mpmath_version": mp.__version__,
            "elapsed_seconds": time.time() - started,
            "interpretation_warning": (
                "Finite source-Gram calculation only. Float64 inertia becomes unresolved "
                "when alpha-alpha_critical is below the reported eigenvalue tolerance."
            ),
        },
        "identities": {
            "disk_node": "q_p=1/p",
            "coordinate": "f_e(p)=sqrt(q_p)*(1-q_p)*q_p^e",
            "completed_gram": "K_ij=d_i*d_j/(1-q_i*q_j)",
            "exact_gamma_residual": (
                "(K-f_0*f_0^T)_ij=d_i*d_j*q_i*q_j/(1-q_i*q_j)"
            ),
            "oversubtraction": "K-alpha*f_0*f_0^T",
            "negative_index_threshold": (
                "alpha>alpha_crit, alpha_crit=1/(1-product_i(q_i)^2)"
            ),
        },
        "sections": sections,
    }
    write_result(args.output, result)
    print(json.dumps(sections[-1], sort_keys=True))


if __name__ == "__main__":
    main()
