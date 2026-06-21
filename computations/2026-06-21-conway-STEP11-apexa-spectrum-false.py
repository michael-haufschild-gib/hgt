#!/usr/bin/env python3
"""STEP 11 for Turing spectrum -> APEX-A: attack the coverage gate as false.

False nearby statement:
  "Once the coefficient spectrum covers the right monomial modes, a very small
   residual is evidence of an algebraic relation."

Attack:
  Dense random integer probes over larger heights generate increasingly small
  residuals even on actual prime logs.  Coverage is necessary for a planted
  relation, not sufficient for a certificate.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-turing-noise-apexa.py")

monomial_basis = BASE["monomial_basis"]
random_coefficients = BASE["random_coefficients"]
scan = BASE["scan"]


def main() -> None:
    rng = np.random.default_rng(2606214053)
    primes = np.array([2, 3, 5, 7, 11], dtype=float)
    actual_logs = np.log(primes)
    planted_logs = actual_logs.copy()
    planted_logs[4] = actual_logs[0] * actual_logs[1]
    names, planted_values, index = monomial_basis(planted_logs)
    _, actual_values, _ = monomial_basis(actual_logs)
    relation = np.zeros(len(names), dtype=int)
    relation[index["L0L1"]] = 1
    relation[index["L4"]] = -1

    print("STEP 11 APEX-A spectrum gate false-statement attack")
    print("method=2 attack it as false")
    print("False statement: broad coefficient-spectrum coverage plus tiny residual certifies a relation.")
    print("height samples planted_min planted_hits actual_min actual_hits actual_best_coeff_norm actual_best_resid")
    for height, samples in [(2, 4000), (3, 8000), (5, 12000), (8, 16000), (12, 20000)]:
        coeffs = random_coefficients(rng, len(names), height, samples)
        _, p_min, p_hits, _ = scan("dense", coeffs, planted_values, relation)
        _, a_min, a_hits, _ = scan("dense", coeffs, actual_values, relation)
        residuals = np.abs(coeffs @ actual_values)
        best = int(np.argmin(residuals))
        best_norm = float(np.linalg.norm(coeffs[best]))
        print(
            f"{height:02d} {samples:05d} {p_min:.3e} {p_hits:05d} "
            f"{a_min:.3e} {a_hits:05d} {best_norm:.3f} {float(residuals[best]):.3e}"
        )
    exact_resid = float(abs(relation @ planted_values))
    actual_relation_resid = float(abs(relation @ actual_values))
    print()
    print(f"target_relation_planted_resid={exact_resid:.3e}")
    print(f"target_relation_actual_resid={actual_relation_resid:.6e}")
    print(
        "Interpretation: coverage is a necessary experimental-design gate, but it is not a proof "
        "gate. Small residuals need height/volume/precision calibration; exact planted recovery "
        "requires the correct support and coefficients, while actual prime logs produce unrelated "
        "near misses under dense search."
    )


if __name__ == "__main__":
    main()
