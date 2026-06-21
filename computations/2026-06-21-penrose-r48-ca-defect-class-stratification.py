#!/usr/bin/env python3
"""R48 candidate: defect-class stratification passport for C_a(tau).

ResearchNode 16: scale-matched detector C_a(tau).

NODE: grain boundaries and twin defects act as distinct catalytic environments.

Transfer: a sign-changing scale-matched detector should not aggregate distinct
defect classes before filtering.  Different off-seam widths/classes require a
class-stratified scale passport.
"""

from __future__ import annotations

import math

import numpy as np


NODE = "grain boundaries and twin defects acting as distinct catalytic environments"


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_catalyst_test() -> None:
    temps = np.array([520.0, 560.0, 600.0, 660.0, 720.0])
    classes = [
        ("terrace", 0.82, 74.0, 1.0),
        ("grain_boundary", 0.13, 48.0, 0.55),
        ("twin_defect", 0.05, 36.0, 0.20),
    ]
    r = 8.314e-3
    rates = []
    print("NODE catalyst-environment test")
    print("class fraction Ea_kJ prefactor rate_at_600K")
    for name, frac, ea, pref in classes:
        rate = frac * pref * np.exp(-ea / (r * temps))
        rates.append(rate)
        print(f"{name:14s} {frac:.2f} {ea:.1f} {pref:.2f} {rate[2]:.6e}")
    total = np.sum(rates, axis=0)
    apparent = []
    for i in range(len(temps) - 1):
        slope = (math.log(total[i + 1]) - math.log(total[i])) / (1 / temps[i + 1] - 1 / temps[i])
        apparent.append(-r * slope)
    print("apparent_Ea_windows_kJ=" + ",".join(f"{x:.2f}" for x in apparent))
    print(
        "NODE verdict: aggregate Arrhenius behavior is curved because distinct "
        "surface environments contribute simultaneous pathways."
    )


def c_a(a: float, tau: np.ndarray) -> np.ndarray:
    return 2.0 * (a * a - tau * tau) / ((a * a + tau * tau) ** 2)


def integrate(x: np.ndarray, y: np.ndarray) -> float:
    return float(np.trapezoid(y, x))


def normalized(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    return y / math.sqrt(max(integrate(x, y * y), 1e-300))


def response(grid: np.ndarray, signal: np.ndarray, a_filter: float) -> float:
    filt = normalized(grid, c_a(a_filter, grid))
    return integrate(grid, filt * signal)


def transfer_audit() -> None:
    attempts = [
        "C_a detector needs defect-class scale stratification",
        "grain-boundary scale classes require separate curvature filters",
        "change aggregate C_a readout into class-conditioned matched filters",
    ]
    print()
    print("STEP8 transfer attempts by Levenshtein distance")
    for text in sorted(attempts, key=lambda item: levenshtein(NODE, item)):
        print(f"distance={levenshtein(NODE, text):3d}  {text}")

    print()
    print("STEP9 method #17: change representation")
    print("represent signal as mixture over defect classes (a_i, weight_i), not one aggregate a")

    grid = np.linspace(-1.0, 1.0, 12001)
    classes = [
        ("narrow_boundary", 0.040, 1.00),
        ("wide_twin", 0.250, 0.18),
    ]
    signal = sum(weight * c_a(a, grid) for _, a, weight in classes)
    scan_as = np.linspace(0.030, 0.320, 180)
    scan_scores = np.array([response(grid, signal, a) for a in scan_as])
    best_idx = int(np.argmax(scan_scores))
    best_a = float(scan_as[best_idx])

    print()
    print("HGT transfer: C_a scale-class stratification")
    print("class a weight matched_response aggregate_best_response recovery_at_best cross_scale_corr")
    aggregate_best = float(scan_scores[best_idx])
    recovered_classes = 0
    for name, a, weight in classes:
        component = weight * c_a(a, grid)
        matched = response(grid, component, a)
        at_best = response(grid, component, best_a)
        corr = response(grid, normalized(grid, c_a(a, grid)), best_a)
        recovery = at_best / matched
        if recovery >= 0.70:
            recovered_classes += 1
        print(
            f"{name:15s} {a:.3f} {weight:.2f} {matched:.6e} "
            f"{aggregate_best:.6e} {recovery:.3f} {corr:.3f}"
        )

    stratified_score = sum(response(grid, weight * c_a(a, grid), a) for _, a, weight in classes)
    single_mean_a = sum(a * weight for _, a, weight in classes) / sum(weight for _, _, weight in classes)
    mean_score = response(grid, signal, single_mean_a)
    print()
    print("Summary gates")
    print(f"aggregate_best_a={best_a:.6f}")
    print(f"weighted_mean_a={single_mean_a:.6f}")
    print(f"single_mean_score={mean_score:.6e}")
    print(f"stratified_score={stratified_score:.6e}")
    print(f"classes_recovered_by_single_best={recovered_classes}/{len(classes)}")
    print(
        "passport_rule=scan and report C_a by defect/width class; one aggregate "
        "scale can hide minority off-seam widths"
    )


def main() -> None:
    print("Penrose R48: C_a defect-class stratification passport")
    print(f"NODE: {NODE}")
    node_catalyst_test()
    transfer_audit()


if __name__ == "__main__":
    main()
