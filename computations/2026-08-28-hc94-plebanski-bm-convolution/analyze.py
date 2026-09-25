#!/usr/bin/env python3
"""Summarize HC94 exploratory scan without recomputing special functions."""

from __future__ import annotations

import argparse
import csv
import json
from collections import defaultdict
from pathlib import Path


def z(value: dict[str, str]) -> complex:
    return complex(float(value["re"]), float(value["im"]))


def rel(a: complex, b: complex) -> float:
    return abs(a - b) / max(1e-300, abs(a), abs(b))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("raw")
    parser.add_argument("--json", default="analysis-summary.json")
    parser.add_argument("--csv", default="analysis-table.csv")
    args = parser.parse_args()
    raw = json.loads(Path(args.raw).read_text())
    cases = raw["cases"]

    rows = []
    lookup = {}
    for case in cases:
        rho = z(case["rho"])
        value = z(case["convolution_curvature_1"])
        finite = z(case["corner_finite_part"])
        root = None if case["curvature_zero"] is None else z(case["curvature_zero"])
        row = {
            "n": case["n"],
            "beta": rho.real,
            "gamma": rho.imag,
            "charge_model": case["charge_model"],
            "abs_convolution": abs(value),
            "abs_corner_finite_part": abs(finite),
            "abs_ratio": abs(value / finite),
            "curvature_zero_re": None if root is None else root.real,
            "curvature_zero_im": None if root is None else root.imag,
            "distance_curvature_zero_to_1": None if root is None else abs(root - 1),
        }
        rows.append(row)
        lookup[(round(rho.real, 12), round(rho.imag, 12), case["n"], case["charge_model"])] = value

    with Path(args.csv).open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    by_model = defaultdict(list)
    critical_by_model = defaultdict(list)
    for row in rows:
        by_model[row["charge_model"]].append(row)
        if abs(row["beta"] - 0.5) < 1e-12:
            critical_by_model[row["charge_model"]].append(row)

    model_summary = {}
    for model, model_rows in by_model.items():
        critical = critical_by_model[model]
        rooted = [r for r in model_rows if r["curvature_zero_re"] is not None]
        model_summary[model] = {
            "minimum_abs_all_cases": min(r["abs_convolution"] for r in model_rows),
            "minimum_abs_critical_line": min(r["abs_convolution"] for r in critical),
            "maximum_abs_critical_line": max(r["abs_convolution"] for r in critical),
            "minimum_abs_ratio_to_corner_finite_part": min(r["abs_ratio"] for r in model_rows),
            "maximum_abs_ratio_to_corner_finite_part": max(r["abs_ratio"] for r in model_rows),
            "curvature_zero_exists": bool(rooted),
            "minimum_distance_curvature_zero_to_1": None
            if not rooted
            else min(r["distance_curvature_zero_to_1"] for r in rooted),
            "curvature_zero_real_range": None
            if not rooted
            else [
                min(r["curvature_zero_re"] for r in rooted),
                max(r["curvature_zero_re"] for r in rooted),
            ],
            "curvature_zero_imag_range": None
            if not rooted
            else [
                min(r["curvature_zero_im"] for r in rooted),
                max(r["curvature_zero_im"] for r in rooted),
            ],
        }

    reflection = []
    for gamma in sorted({round(row["gamma"], 12) for row in rows}):
        for beta in (0.2, 0.35):
            for n in (0, 1, 2):
                for model in ("reflected", "same", "opposite"):
                    left = lookup[(round(beta, 12), gamma, n, model)]
                    right = lookup[(round(1 - beta, 12), gamma, n, model)]
                    reflection.append(
                        {
                            "gamma": gamma,
                            "beta": beta,
                            "n": n,
                            "charge_model": model,
                            "even_residual": rel(right, left),
                            "odd_residual": rel(right, -left),
                            "conjugate_residual": rel(right, left.conjugate()),
                        }
                    )

    reflection_summary = {}
    for model in ("reflected", "same", "opposite"):
        selected = [r for r in reflection if r["charge_model"] == model]
        reflection_summary[model] = {
            "minimum_even_residual": min(r["even_residual"] for r in selected),
            "minimum_odd_residual": min(r["odd_residual"] for r in selected),
            "minimum_conjugate_residual": min(r["conjugate_residual"] for r in selected),
            "maximum_even_residual": max(r["even_residual"] for r in selected),
            "maximum_odd_residual": max(r["odd_residual"] for r in selected),
            "maximum_conjugate_residual": max(r["conjugate_residual"] for r in selected),
        }

    beta_scan_summary = {}
    for scan in raw["beta_scans"]:
        beta_scan_summary[scan["charge_model"]] = {
            "grid_minimum_beta": float(scan["grid_minimum"]["beta"]),
            "grid_minimum_abs": float(scan["grid_minimum"]["abs"]),
            "critical_beta_abs": next(
                float(row["abs"]) for row in scan["rows"] if float(row["beta"]) == 0.5
            ),
        }

    precision_max = max(float(x["relative_difference"]) for x in raw["precision_checks"])
    quadrature_max = max(
        float(item["relative_difference"])
        for group in raw["quadrature_checks"]
        for item in group["checks"]
    )
    summary = {
        "purpose": raw["purpose"],
        "case_count": len(cases),
        "workers": raw["workers"],
        "elapsed_seconds": raw["elapsed_seconds"],
        "model_summary": model_summary,
        "reflection_summary": reflection_summary,
        "beta_scan_summary": beta_scan_summary,
        "maximum_dps60_dps90_relative_difference": precision_max,
        "maximum_hypergeometric_quadrature_relative_difference": quadrature_max,
    }
    Path(args.json).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
