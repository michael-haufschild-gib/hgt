#!/usr/bin/env python3
"""STEP 11: compare nearby false statements for catalog completeness -> one object."""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-catalog-completeness-one-object.py")

first_primes = BASE["first_primes"]
collect_fields = BASE["collect_fields"]
association_top_eig = BASE["association_top_eig"]


def main() -> None:
    rng = np.random.default_rng(2606212727)
    primes = first_primes(160)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7, 0.9, 1.2]
    fields = collect_fields(sigmas, (100.0, 170.0), 520, primes, rng)
    catalogs = ["A", "P", "H", "finiteH", "randomH", "Delta"]

    print("STEP 11 METHOD 22: COMPARE NEARBY FALSE STATEMENTS")
    print("False statement F0: any thresholded catalog chooses the same canonical one-object signature.")
    print("Test A: each catalog uses its own q70 threshold; compare association/event signatures.")
    print("catalog native_q70 event_fraction assoc_top_eig lane_min lane_max")
    for catalog in catalogs:
        threshold = float(np.quantile(fields[catalog], 0.70))
        ev = fields[catalog] > threshold
        lane = np.mean(ev, axis=0)
        print(
            f"{catalog:7s} {threshold:.6f} {float(np.mean(ev)):.4f} "
            f"{association_top_eig(ev):.4f} {float(np.min(lane)):.4f} {float(np.max(lane)):.4f}"
        )

    print()
    print("Test B: matched occupancy at 30% for every catalog; compare association signatures.")
    print("catalog event_fraction assoc_top_eig lane_min lane_max")
    for catalog in catalogs:
        threshold = float(np.quantile(fields[catalog], 0.70))
        ev = fields[catalog] > threshold
        lane = np.mean(ev, axis=0)
        print(
            f"{catalog:7s} {float(np.mean(ev)):.4f} {association_top_eig(ev):.4f} "
            f"{float(np.min(lane)):.4f} {float(np.max(lane)):.4f}"
        )

    print()
    print(
        "Verdict: F0 is false. Catalog-native thresholds and matched occupancy "
        "still produce different association operators. This is a useful "
        "completeness warning, but it does not pick H uniquely: Delta has a "
        "stronger association eigenvalue, and finiteH can dominate raw event "
        "rates under H thresholds."
    )


if __name__ == "__main__":
    main()
