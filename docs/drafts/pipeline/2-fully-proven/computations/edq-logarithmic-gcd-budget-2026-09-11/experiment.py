#!/usr/bin/env python3
"""RunPod-only numerical guidance. No output is a Lean proof premise."""
import os
for _key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
             "NUMEXPR_NUM_THREADS"):
    os.environ[_key] = "1"

import concurrent.futures
from fractions import Fraction
import json
import math
import platform
import socket
import time

import numpy as np

MAX_N = 128
WORKERS = 4
CHUNK = 8192
TAIL_BUDGET = 0.02
WORKER_SECONDS = 120


def mobius(n):
    mu = np.ones(n + 1, dtype=np.int64)
    prime = np.ones(n + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, n + 1):
        if prime[p]:
            mu[p::p] *= -1
            mu[p * p::p * p] = 0
            prime[p * p::p] = False
    mu[0] = 0
    return mu


def gram_range(spec):
    lo, hi, started = spec
    moduli = np.arange(1, MAX_N + 1, dtype=np.int64)
    mu = mobius(MAX_N)[1:]
    gram = np.zeros((MAX_N, MAX_N), dtype=np.float64)
    energy = np.zeros(MAX_N, dtype=np.float64)
    for left in range(lo, hi, CHUNK):
        if time.monotonic() - started > WORKER_SECONDS:
            raise TimeoutError("Frozen worker deadline exceeded; no extended run")
        k = np.arange(left, min(hi, left + CHUNK), dtype=np.int64)
        residue = (k[None, :] % moduli[:, None]) / moduli[:, None]
        weight = 1.0 / (k.astype(np.float64) * (k + 1))
        source = np.cumsum(mu[:, None] * residue, axis=0)
        energy += (source * source) @ weight
        feature = residue * np.sqrt(weight)[None, :]
        gram += feature @ feature.T
    return gram, energy


def rational_control():
    k = np.arange(1, 258, dtype=np.int64)
    d = np.arange(1, 9, dtype=np.int64)
    residue = (k[None, :] % d[:, None]) / d[:, None]
    w = 1.0 / (k.astype(np.float64) * (k + 1))
    numeric = (residue * w[None, :]) @ residue.T
    error = 0.0
    for m in range(1, 9):
        for n in range(1, 9):
            exact = sum((Fraction((j % m) * (j % n), m * n * j * (j + 1))
                         for j in range(1, 258)), Fraction(0))
            error = max(error, abs(float(exact) - numeric[m - 1, n - 1]))
    assert error < 1e-13, ("rational Gram control", error)
    return error


def variation_interval(mid, negative_tail, positive_tail, margin):
    low = mid - negative_tail
    high = mid + positive_tail
    lower = max(0.0, float(np.maximum(0, np.maximum(low, -high)).sum()) - margin)
    upper = float(np.maximum(abs(low), abs(high)).sum()) + margin
    return lower, upper, low, high


def classify(variation, diagonal, margin):
    if variation[1] < 4 * diagonal[0] - margin:
        return "PASS_AT_FROZEN_CONSTANT"
    if variation[0] > 4 * diagonal[1] + margin:
        return "FAIL_AT_FROZEN_CONSTANT"
    return "INCONCLUSIVE"


def main():
    if platform.system() != "Linux":
        raise RuntimeError("Run only on the authorized RunPod; local computation forbidden")
    started = time.monotonic()
    mu = mobius(MAX_N)[1:]
    mass = int(np.abs(mu[1:]).sum())  # Unit generator is identically zero.
    cutoff = math.ceil(math.log(MAX_N) * mass * mass / TAIL_BUDGET)
    edges = [1 + i * cutoff // WORKERS for i in range(WORKERS + 1)]
    specs = [(edges[i], edges[i + 1], started) for i in range(WORKERS)]
    with concurrent.futures.ProcessPoolExecutor(max_workers=WORKERS) as pool:
        pieces = list(pool.map(gram_range, specs))
    gram = sum((g for g, _ in pieces), np.zeros((MAX_N, MAX_N)))
    direct_energy = sum((e for _, e in pieces), np.zeros(MAX_N))
    rational_error = rational_control()
    entry_tail = 1.0 / (cutoff + 1)
    assert gram[1, 1] <= math.log(2) / 4 + 1e-12
    assert math.log(2) / 4 <= gram[1, 1] + entry_tail + 1e-12

    c = np.zeros(MAX_N + 1)
    ell = c.copy()
    c_negative = c.copy()
    c_positive = c.copy()
    l_negative = c.copy()
    l_positive = c.copy()
    diagonal = diagonal_log = diagonal_tail = diagonal_log_tail = 0.0
    historical_energy = 0.0
    reconstruction_error = history_error = 0.0
    results = []
    for n in range(1, MAX_N + 1):
        if n > 1:
            historical_energy += math.log(n / (n - 1)) * direct_energy[n - 2]
        for m in range(2, n + 1):
            coefficient = int(mu[m - 1] * mu[n - 1]) * (1 if m == n else 2)
            r = math.gcd(m, n)
            value = coefficient * gram[m - 1, n - 1]
            c[r] += value
            ell[r] += math.log(n) * value
            if coefficient > 0:
                c_positive[r] += coefficient * entry_tail
                l_positive[r] += coefficient * math.log(n) * entry_tail
            else:
                c_negative[r] -= coefficient * entry_tail
                l_negative[r] -= coefficient * math.log(n) * entry_tail
        if n > 1 and mu[n - 1]:
            diagonal += gram[n - 1, n - 1]
            diagonal_log += math.log(n) * gram[n - 1, n - 1]
            diagonal_tail += entry_tail
            diagonal_log_tail += math.log(n) * entry_tail
        reconstruction_error = max(reconstruction_error, abs(c.sum() - direct_energy[n - 1]))
        history_error = max(history_error, abs(ell.sum() -
            (math.log(n) * direct_energy[n - 1] - historical_energy)))
        if n == 1:
            continue
        # Sensitivity margin only; no certified floating-point interval is claimed.
        margin = 1e-8 * (1 + float(np.abs(ell).sum()) + float(np.abs(c).sum()))
        cv = variation_interval(c, c_negative, c_positive, margin)
        lv = variation_interval(ell, l_negative, l_positive, margin)
        dc = [max(0, diagonal - margin), diagonal + diagonal_tail + margin]
        dl = [max(0, diagonal_log - margin), diagonal_log + diagonal_log_tail + margin]
        result = {"N": n, "ordinary_classification": classify(cv, dc, margin),
                  "logarithmic_classification": classify(lv, dl, margin),
                  "ordinary_variation": list(cv[:2]), "logarithmic_variation": list(lv[:2]),
                  "diagonal": dc, "logarithmic_diagonal": dl,
                  "energy_estimate": float(c.sum()), "gamma_estimate": float(-ell.sum()),
                  "rounding_sensitivity_margin": margin,
                  "groups": [{"r": r, "C": float(c[r]), "C_lower": float(cv[2][r]),
                              "C_upper": float(cv[3][r]), "L": float(ell[r]),
                              "L_lower": float(lv[2][r]), "L_upper": float(lv[3][r])}
                             for r in range(1, n + 1)]}
        results.append(result)
    assert reconstruction_error < 1e-7, ("source reconstruction", reconstruction_error)
    assert history_error < 1e-7, ("logarithmic history", history_error)
    output = {"status": "NUMERICAL_GUIDANCE_ONLY", "host": socket.gethostname(),
              "python": platform.python_version(), "numpy": np.__version__,
              "workers": WORKERS, "max_N": MAX_N, "physical_cutoff": cutoff,
              "logarithmic_total_tail_allowance": math.log(MAX_N) * mass * mass * entry_tail,
              "elapsed_seconds": time.monotonic() - started,
              "controls": {"rational_error": rational_error,
                           "source_reconstruction_error": reconstruction_error,
                           "logarithmic_history_error": history_error}, "results": results}
    with open("results.json", "w") as stream:
        json.dump(output, stream, indent=2)
    print(json.dumps({k: v for k, v in output.items() if k != "results"}), flush=True)
    for result in results:
        print(json.dumps({k: v for k, v in result.items() if k != "groups"}), flush=True)


if __name__ == "__main__":
    main()
