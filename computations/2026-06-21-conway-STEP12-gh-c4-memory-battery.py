#!/usr/bin/env python3
"""STEP 12 battery for Grote-Hynes memory friction -> C4.

Stress result:
  A scalar C4 correlation length is not a complete gate. The positive
  cross-sigma correlation kernel has a frequency-dependent memory response.

Battery:
  - multiple critical/right windows;
  - finite Euler cutoffs;
  - random phase and per-lane spectrum preserving controls;
  - right-strip true/finite collapse check.
"""

from __future__ import annotations

import math
import runpy

import numpy as np


GH = runpy.run_path("computations/2026-06-21-conway-grote-hynes-c4-memory.py")
C4 = runpy.run_path("computations/2026-06-21-conway-isospectral-orientability-c4.py")

first_primes = C4["first_primes"]
gamma_part = C4["gamma_part"]
dlog_zeta = C4["dlog_zeta"]
dlog_finite = C4["dlog_finite"]
phase_defect = C4["phase_defect"]
lane_standardize = C4["lane_standardize"]
circular_shift_lanes = C4["circular_shift_lanes"]
fourier_scramble_lanes = C4["fourier_scramble_lanes"]
lane_power_rel_diff = C4["lane_power_rel_diff"]
corr_metrics = C4["corr_metrics"]
memory_metrics = GH["memory_metrics"]


def build_multi_fields(sigmas, window, samples, finite_sets, rng):
    fields = {"true": np.zeros((samples, len(sigmas))), "random": np.zeros((samples, len(sigmas)))}
    for n in finite_sets:
        fields[f"finite{n}"] = np.zeros((samples, len(sigmas)))
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        for i, sigma in enumerate(sigmas):
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            zp = dlog_zeta(s)
            theta = rng.uniform(-math.pi, math.pi)
            rp = abs(zp) * complex(math.cos(theta), math.sin(theta))
            fields["true"][j, i] = phase_defect(g, zp)
            fields["random"][j, i] = phase_defect(g, rp)
            for n, primes in finite_sets.items():
                fields[f"finite{n}"][j, i] = phase_defect(g, dlog_finite(s, primes))
    return fields


def main() -> None:
    rng = np.random.default_rng(2606215317)
    finite_counts = [40, 80, 160, 320]
    finite_sets = {n: first_primes(n) for n in finite_counts}
    cases = [
        ("zero_strip", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (14.0, 84.0), "critical"),
        ("critical_low", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (100.0, 170.0), "critical"),
        ("critical_mid", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (260.0, 330.0), "critical"),
        ("critical_high", [0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.90], (500.0, 570.0), "critical"),
        ("right_low", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (100.0, 170.0), "right"),
        ("right_high", [1.05, 1.15, 1.25, 1.35, 1.45, 1.55, 1.70], (500.0, 570.0), "right"),
    ]
    print("STEP 12 GH/C4 memory-kernel battery")
    print(f"finite_counts={finite_counts} samples=220")
    print(
        "case region true_lift true_xi true_top max_finite_lift best_finite_gap "
        "random_lift shifted_lift fourier_lift power_shift power_fourier "
        "finite_lifts verdict"
    )
    critical_ok = 0
    critical_total = 0
    right_ok = 0
    right_total = 0
    for label, sigmas, window, region in cases:
        fields = build_multi_fields(sigmas, window, 220, finite_sets, rng)
        true = lane_standardize(fields["true"])
        random = lane_standardize(fields["random"])
        shifted = circular_shift_lanes(true, rng)
        fourier = fourier_scramble_lanes(true, rng)
        true_m = memory_metrics(true)
        random_m = memory_metrics(random)
        shifted_m = memory_metrics(shifted)
        fourier_m = memory_metrics(fourier)
        finite_lifts = []
        finite_gaps = []
        for n in finite_counts:
            fm = memory_metrics(lane_standardize(fields[f"finite{n}"]))
            finite_lifts.append(fm.lift)
            finite_gaps.append(abs(true_m.lift - fm.lift))
        max_finite = max(finite_lifts)
        best_gap = min(finite_gaps)
        ctrl_max = max(max_finite, random_m.lift, shifted_m.lift, fourier_m.lift)
        if region == "critical":
            ok = true_m.lift > ctrl_max + 0.20
            critical_ok += int(ok)
            critical_total += 1
        else:
            ok = best_gap < 0.03
            right_ok += int(ok)
            right_total += 1
        p_shift = lane_power_rel_diff(true, shifted)
        p_fourier = lane_power_rel_diff(true, fourier)
        finite_str = ",".join(f"N{n}:{v:.3f}" for n, v in zip(finite_counts, finite_lifts))
        print(
            f"{label:13s} {region:8s} {true_m.lift:.4f} {true_m.xi:.4f} {true_m.top_eig:.4f} "
            f"{max_finite:.4f} {best_gap:.4f} {random_m.lift:.4f} {shifted_m.lift:.4f} "
            f"{fourier_m.lift:.4f} {p_shift:.2e} {p_fourier:.2e} {finite_str} {int(ok)}"
        )
    print()
    print(f"CRITICAL_MEMORY_GATE_SURVIVES {critical_ok}/{critical_total}")
    print(f"RIGHT_FINITE_MEMORY_COLLAPSE {right_ok}/{right_total}")
    print(
        "Interpretation: the memory-kernel gate is stable if true critical lift beats all "
        "finite/random/spectrum-preserving controls, while right-side true and finite Euler "
        "collapse. This tests a stronger object than scalar xi_sigma: a Laplace family of "
        "cross-lane kernels."
    )


if __name__ == "__main__":
    main()
