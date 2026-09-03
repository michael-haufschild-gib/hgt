#!/usr/bin/env python3
"""Finite cyclic-Gram audit for the restricted-Hardy cubic source candidate.

For every prime-power event ``n = p^k``, set

    a_n = log(n),
    c_n = Lambda(n) / (2 n log(n)^2).

The positive half-line exponential Hankel section is

    H_X = sum_{p^k <= X} c_n |exp(-a_n x)><exp(-a_n x)|.

Its finite feature Gram is

    G_ij = sqrt(c_i c_j) / (a_i + a_j).

Hence ``Tr(H_X)`` is the truncated Route-P base cubic budget, while
``Tr(H_X^3) = Tr(G_X^3)`` retains every cyclic cross-frequency term.  This
diagnostic tests numerical margin only.  It does not identify this surrogate
with the arithmetic Hardy seam and is not evidence for an index theorem.
"""

import argparse
import json
import math
import time
from pathlib import Path

import numpy as np


def parse_cutoffs(text):
    values = sorted(set(int(item.strip()) for item in text.split(",") if item.strip()))
    if not values or values[0] < 2:
        raise SystemExit("--cutoffs must contain integers at least 2")
    return values


def primes_through(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
    return [n for n in range(2, limit + 1) if sieve[n]]


def prime_power_events(limit):
    events = []
    for p in primes_through(limit):
        log_p = math.log(p)
        power = p
        depth = 1
        while power <= limit:
            rate = depth * log_p
            coefficient = 1.0 / (2.0 * power * depth * depth * log_p)
            trace_atom = coefficient / (2.0 * rate)
            events.append((power, p, depth, rate, coefficient, trace_atom))
            if power > limit // p:
                break
            power *= p
            depth += 1
    events.sort()
    return events


def audit_cutoff(events, cutoff):
    active = [event for event in events if event[0] <= cutoff]
    rates = np.asarray([event[3] for event in active], dtype=np.float64)
    coefficients = np.asarray([event[4] for event in active], dtype=np.float64)
    trace_atoms = np.asarray([event[5] for event in active], dtype=np.float64)

    roots = np.sqrt(coefficients)
    gram = (roots[:, None] * roots[None, :]) / (rates[:, None] + rates[None, :])
    eigenvalues = np.linalg.eigvalsh(gram)
    trace_h = math.fsum(trace_atoms.tolist())
    trace_h_from_spectrum = float(np.sum(eigenvalues, dtype=np.float64))
    trace_h2 = float(np.sum(eigenvalues**2, dtype=np.float64))
    trace_h3 = float(np.sum(eigenvalues**3, dtype=np.float64))
    diagonal_cubic = math.fsum((trace_atoms**3).tolist())

    return {
        "cutoff": cutoff,
        "prime_power_events": len(active),
        "trace_h": trace_h,
        "trace_h_from_spectrum": trace_h_from_spectrum,
        "trace_residual": trace_h_from_spectrum - trace_h,
        "min_gram_eigenvalue": float(eigenvalues[0]),
        "operator_norm_h": float(eigenvalues[-1]),
        "trace_h2": trace_h2,
        "trace_h3_full_cyclic": trace_h3,
        "two_trace_h3": 2.0 * trace_h3,
        "two_trace_h3_margin_to_one": 1.0 - 2.0 * trace_h3,
        "scalar_trace_cube_upper": trace_h**3,
        "two_scalar_trace_cube_upper": 2.0 * trace_h**3,
        "diagonal_only_trace_atom_cubes": diagonal_cubic,
        "mixed_cyclic_contribution": trace_h3 - diagonal_cubic,
        "mixed_cyclic_fraction": (trace_h3 - diagonal_cubic) / trace_h3,
    }


def write_result(path, result):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoffs", default="2,3,10,100,1000,3000,10000")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    cutoffs = parse_cutoffs(args.cutoffs)
    started = time.time()
    events = prime_power_events(cutoffs[-1])
    rows = [audit_cutoff(events, cutoff) for cutoff in cutoffs]
    result = {
        "metadata": {
            "cutoffs": cutoffs,
            "largest_cutoff": cutoffs[-1],
            "numpy_version": np.__version__,
            "elapsed_seconds": time.time() - started,
            "interpretation_warning": (
                "Finite double-precision Gram spectra only. The candidate has not been "
                "identified with the arithmetic Hardy seam, and no infinite-tail, interval, "
                "trace-class, or index statement follows from these data."
            ),
        },
        "identities": {
            "rate": "a_(p,k)=k*log(p)=log(p^k)",
            "coefficient": "c_(p,k)=1/(2*p^k*k^2*log(p))",
            "gram": "G_ij=sqrt(c_i*c_j)/(a_i+a_j)",
            "trace_atom": "1/(4*p^k*k^3*log(p)^2)",
            "trace_cube": "sum_ijk G_ij*G_jk*G_ki",
        },
        "rows": rows,
    }
    write_result(args.output, result)
    print(json.dumps(rows[-1], sort_keys=True))


if __name__ == "__main__":
    main()
