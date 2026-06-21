#!/usr/bin/env python3
"""STEP 12 battery for morphogenesis initial-noise -> C4.

Stress result:
  C4 top eigenvalue / xi_sigma can be faked by correlated random phase seeds.

Question:
  Does a simple per-lane scalar-spectrum gate reject those seed-spectrum fakes?
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-morphogenesis-noise-c4.py")

first_primes = BASE["first_primes"]
build_fields = BASE["build_fields"]
lane_standardize = BASE["lane_standardize"]
corr_metrics = BASE["corr_metrics"]

C4_PREV = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")
lane_power_rel_diff = C4_PREV["lane_power_rel_diff"]


def main() -> None:
    rng = np.random.default_rng(2606214417)
    primes = first_primes(160)
    cases = [
        ("zero_strip", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (14.0, 84.0), "critical"),
        ("critical_low", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (100.0, 170.0), "critical"),
        ("critical_high", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (500.0, 570.0), "critical"),
        ("right_low", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (100.0, 170.0), "right"),
    ]
    print("STEP 12 C4 seed-spectrum fake battery")
    print(
        "case region kind true_eig ctrl_eig eig_ratio xi_ratio scalar_power_diff "
        "fakes_top_eig passes_power_gate verdict"
    )
    fake_top = 0
    rejected_by_power = 0
    total = 0
    for label, sigmas, window, region in cases:
        fields = build_fields(sigmas, window, 260, primes, rng)
        true = lane_standardize(fields["true"])
        true_m = corr_metrics(true)
        for kind in ["iid_random", "common_mode", "low_sigma_seed", "high_sigma_seed"]:
            ctrl = lane_standardize(fields[kind])
            m = corr_metrics(ctrl)
            eig_ratio = m.top_eig / (true_m.top_eig + 1e-300)
            xi_ratio = m.corr_length / (true_m.corr_length + 1e-300)
            power_diff = lane_power_rel_diff(true, ctrl)
            fakes = eig_ratio >= 0.85
            power_gate = power_diff < 1e-10
            verdict = "fake_rejected" if fakes and not power_gate else "fake_survives" if fakes else "no_fake"
            fake_top += int(fakes)
            rejected_by_power += int(fakes and not power_gate)
            total += 1
            print(
                f"{label:13s} {region:8s} {kind:14s} {true_m.top_eig:.4f} {m.top_eig:.4f} "
                f"{eig_ratio:.4f} {xi_ratio:.4f} {power_diff:.3e} {int(fakes)} {int(power_gate)} {verdict}"
            )
    print()
    print(f"TOP_EIG_FAKES {fake_top}/{total}")
    print(f"TOP_EIG_FAKES_REJECTED_BY_PER_LANE_POWER {rejected_by_power}/{fake_top}")
    print(
        "Interpretation: correlated phase seeds can fake C4 top eigenvalue / xi_sigma, but they do "
        "not preserve per-lane scalar spectra. This keeps the earlier isospectral C4 gate alive: "
        "C4 claims must be tested against controls that preserve each lane's spectrum, not only "
        "against iid random phase or finite Euler controls."
    )


if __name__ == "__main__":
    main()
