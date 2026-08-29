#!/usr/bin/env python3
"""Independent consistency checks for source-Galerkin and completed-error artifacts."""

from __future__ import annotations

import argparse
import glob
import json
import math
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    failures: list[str] = []
    checks: dict[str, object] = {}

    campaign = json.loads((args.root / "campaign-summary.json").read_text(encoding="utf-8"))
    result_files = sorted(glob.glob(str(args.root / "campaign-results" / "result-*.json")))
    if len(campaign) != 66 or len(result_files) != 66:
        failures.append("campaign must contain 66 successful jobs and 66 result files")
    if any(record["status"] != "ok" for record in campaign):
        failures.append("campaign contains failed job")

    by_aperture: dict[str, list[tuple[int, float]]] = {}
    maximum_formula_error = 0.0
    maximum_eigen_residual = 0.0
    maximum_component_error = 0.0
    maximum_parity_error = 0.0
    all_positive = True
    for filename in result_files:
        payload = json.loads(Path(filename).read_text(encoding="utf-8"))
        ground = float(payload["ground_eigenvalue"])
        all_positive &= ground > 0
        by_aperture.setdefault(payload["a"], []).append((int(payload["N"]), ground))
        maximum_eigen_residual = max(maximum_eigen_residual, float(payload["eigen_residual_max"]))
        maximum_component_error = max(maximum_component_error, float(payload["component_sum_error"]))
        coefficients = [float(value) for value in payload["ground_coefficients_centered"]]
        parity = math.sqrt(sum((x - y) ** 2 for x, y in zip(coefficients, reversed(coefficients))))
        maximum_parity_error = max(maximum_parity_error, parity)
        for record in payload["formula_validation"]:
            maximum_formula_error = max(
                maximum_formula_error,
                *(float(record[key]) for key in (
                    "arch_sine_abs_error", "arch_diagonal_abs_error",
                    "polar_sine_abs_error", "polar_diagonal_abs_error",
                )),
            )
    monotone = True
    for rows in by_aperture.values():
        rows.sort()
        monotone &= all(rows[index][1] <= rows[index - 1][1] for index in range(1, len(rows)))
    if not all_positive:
        failures.append("a source-side ground eigenvalue was not positive")
    if not monotone:
        failures.append("a finite floor increased with rank")
    if maximum_formula_error >= 1e-180:
        failures.append("closed formula failed independent quadrature at 180 digits")
    if maximum_eigen_residual >= 1e-180:
        failures.append("eigen residual too large")
    if maximum_component_error >= 1e-180:
        failures.append("component reconstruction residual too large")
    if maximum_parity_error >= 1e-12:
        failures.append("ground parity residual too large")

    analysis = json.loads((args.root / "campaign-analysis.json").read_text(encoding="utf-8"))
    for key in ("C1_negative_cases", "C1_upward_cases", "C2_negative_cases"):
        if analysis[key] != 0:
            failures.append(f"{key} was nonzero")

    scan_files = [
        args.root / "completed-error-1e8-recheck.json",
        args.root / "completed-error-1e10.json",
        args.root / "completed-error-1e11.json",
    ]
    expected_prime_counts = [5_761_455, 455_052_511, 4_118_054_813]
    scans = [json.loads(path.read_text(encoding="utf-8")) for path in scan_files]
    if [scan["prime_count"] for scan in scans] != expected_prime_counts:
        failures.append("segmented sieve did not reproduce reference prime counts")
    if any(scan["negative_found"] for scan in scans):
        failures.append("completed-error scan found a negative value")
    first_scan = json.loads((args.root / "completed-error-1e8.json").read_text(encoding="utf-8"))
    recheck = scans[0]
    for key in ("prime_count", "higher_prime_power_count", "final_completed_error"):
        if first_scan[key] != recheck[key]:
            failures.append(f"independent 1e8 segmentation mismatch in {key}")

    checks.update({
        "campaign_result_count": len(result_files),
        "all_ground_eigenvalues_positive": all_positive,
        "all_rank_sequences_antitone": monotone,
        "maximum_formula_quadrature_error": maximum_formula_error,
        "maximum_eigen_residual": maximum_eigen_residual,
        "maximum_component_sum_error": maximum_component_error,
        "maximum_even_parity_error_double": maximum_parity_error,
        "C1_negative_cases": analysis["C1_negative_cases"],
        "C1_upward_cases": analysis["C1_upward_cases"],
        "C2_negative_cases": analysis["C2_negative_cases"],
        "completed_error_limits": [scan["limit"] for scan in scans],
        "completed_error_minima": [scan["minimum"] for scan in scans],
        "reference_prime_counts_reproduced": True,
        "independent_1e8_segmentation_reproduced": not failures,
        "failures": failures,
        "passed": not failures,
    })
    args.out.write_text(json.dumps(checks, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(checks, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
