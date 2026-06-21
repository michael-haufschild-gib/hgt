#!/usr/bin/env python3
"""STEP 11 for SOC scaling -> one object: search for a monotone rescue.

Question:
  As the event threshold tightens, does H's joint-scaling residual improve
  monotonically or become best-ranked among candidate objects?
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-soc-scaling-one-object.py")

first_primes = BASE["first_primes"]
build_fields = BASE["build_fields"]
collect_component_stats = BASE["collect_component_stats"]
scaling_metrics = BASE["scaling_metrics"]


def main() -> None:
    rng = np.random.default_rng(2606215301)
    primes = first_primes(160)
    sigmas = np.linspace(0.20, 0.90, 9)
    cases = [("zero_low", (14.0, 84.0)), ("critical_low", (100.0, 170.0)), ("critical_high", (500.0, 570.0))]
    qs = [0.65, 0.70, 0.75, 0.80, 0.85, 0.90]
    objects = ["P", "H", "Delta", "finiteH", "randomH"]

    print("STEP 11 one-object monotone-threshold check")
    print("method=13 find a monotone quantity")
    print("case q best_object best_residual H_residual H_rank residuals")
    h_best_count = 0
    h_monotone_count = 0
    for label, window in cases:
        fields = build_fields(sigmas, window, 360, primes, rng)
        h_resids = []
        for q in qs:
            residuals = {}
            for obj in objects:
                sizes, durations, _ = collect_component_stats(fields[obj], [q])
                _, _, _, resid = scaling_metrics(sizes, durations)
                residuals[obj] = resid
            ranked = sorted(
                [(v if not np.isnan(v) else 1e9, k) for k, v in residuals.items()],
                key=lambda x: x[0],
            )
            best_resid, best_obj = ranked[0]
            h_rank = [k for _, k in ranked].index("H") + 1
            h_resid = residuals["H"]
            h_resids.append(h_resid)
            h_best_count += int(best_obj == "H")
            print(
                f"{label:13s} {q:.2f} {best_obj:8s} {best_resid:.4f} "
                f"{h_resid:.4f} {h_rank:d} "
                + ",".join(f"{k}:{residuals[k]:.3f}" for k in objects)
            )
        finite = np.array([x for x in h_resids if not np.isnan(x)])
        monotone = bool(len(finite) >= 3 and np.all(np.diff(finite) <= 1e-9))
        h_monotone_count += int(monotone)
        print(f"{label:13s} H_residual_monotone_nonincreasing={int(monotone)}")
    print()
    print(f"H_BEST_THRESHOLD_ROWS {h_best_count}/{len(cases) * len(qs)}")
    print(f"H_MONOTONE_CASES {h_monotone_count}/{len(cases)}")
    print(
        "Interpretation: no monotone-threshold rescue appears if H is rarely best-ranked and its "
        "residual does not improve monotonically under threshold tightening."
    )


if __name__ == "__main__":
    main()
