#!/usr/bin/env python3
"""
R39 STEP 8/9 transfer to G-C18 faithful-index rigidity.

NODE: global coherence can remain while subsystems appear decohered.
Target: faithful integer index can survive while measured traces look controlled.

Method #10: test extreme cases.
"""

from __future__ import annotations

import numpy as np


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        row = [i]
        for j, cb in enumerate(b, start=1):
            row.append(min(prev[j] + 1, row[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = row
    return prev[-1]


def main() -> None:
    source = "global_coherence_remains_local_subsystems_decohered"
    attempts = [
        "faithful_index_survives_measured_trace_decoherence",
        "global_negative_direction_local_trace_blind",
        "dust_perturbation_invisible_to_source_data",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:56s} distance={levenshtein(source, a)}")
    print(f"selected={min(attempts, key=lambda x: levenshtein(source, x))}")

    rng = np.random.default_rng(3910)
    n = 80
    q, _ = np.linalg.qr(rng.normal(size=(n, n)))
    print("\nSTEP 9 method 10: tiny negative direction extremes")
    print("eps       faithful_neg_index  trace_defect  random_probe_negative_rate  min_probe")
    for eps in [1e-1, 1e-2, 1e-3, 1e-5, 1e-8]:
        vals = np.ones(n)
        vals[-1] = -eps
        h = (q * vals) @ q.T
        probes = rng.normal(size=(4000, n))
        probes /= np.linalg.norm(probes, axis=1, keepdims=True)
        quad = np.einsum("ij,jk,ik->i", probes, h, probes)
        neg_rate = float(np.mean(quad < 0))
        print(
            f"{eps:8.0e} {1:19d} {np.trace(h)/n - 1.0:12.6g} "
            f"{neg_rate:27.6f} {float(np.min(quad)):10.6g}"
        )
    print(
        "\nInterpretation: measured trace control can look perfect as eps -> 0, "
        "while the faithful integer index remains nonzero. This is exactly the G-C18 dust warning."
    )


if __name__ == "__main__":
    main()
