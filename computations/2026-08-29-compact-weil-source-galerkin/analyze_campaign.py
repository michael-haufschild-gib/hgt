#!/usr/bin/env python3
"""Post-process source-Galerkin campaign without zeta zeros or external numerics."""

from __future__ import annotations

import argparse
import cmath
import csv
import glob
import json
import math
from pathlib import Path


def fft(values: list[complex], inverse: bool = False) -> list[complex]:
    data = list(values)
    size = len(data)
    j = 0
    for i in range(1, size):
        bit = size >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            data[i], data[j] = data[j], data[i]
    length = 2
    sign = 1 if inverse else -1
    while length <= size:
        root = cmath.exp(sign * 2j * math.pi / length)
        half = length // 2
        for start in range(0, size, length):
            phase = 1 + 0j
            for offset in range(half):
                even = data[start + offset]
                odd = data[start + offset + half] * phase
                data[start + offset] = even + odd
                data[start + offset + half] = even - odd
                phase *= root
        length *= 2
    if inverse:
        data = [value / size for value in data]
    return data


def diagnostics(payload: dict[str, object], sample_count: int) -> dict[str, object]:
    L = float(payload["L"])
    N = int(payload["N"])
    coefficients = [float(value) for value in payload["ground_coefficients_centered"]]
    spectrum = [0j] * sample_count
    for mode, coefficient in zip(range(-N, N + 1), coefficients):
        spectrum[mode % sample_count] = coefficient
    physical = [value * sample_count / math.sqrt(L) for value in fft(spectrum, inverse=True)]
    pivot = max(physical, key=lambda value: abs(value.real)).real
    orientation = 1 if pivot >= 0 else -1
    physical_real = [orientation * value.real for value in physical]
    physical_imag_max = max(abs(value.imag) for value in physical)
    physical_min = min(physical_real)
    physical_min_index = physical_real.index(physical_min)
    half = sample_count // 2
    physical_half_diffs = [physical_real[i + 1] - physical_real[i] for i in range(half)]

    padded = physical + [0j] * sample_count
    transformed = fft(padded)
    corr_raw = fft([value.conjugate() * value for value in transformed], inverse=True)
    dx = L / sample_count
    correlation = [value.real * dx for value in corr_raw[:sample_count]]
    correlation = [value / correlation[0] for value in correlation]
    corr_diffs = [correlation[i + 1] - correlation[i] for i in range(sample_count - 1)]

    F = [2 * value for value in correlation]
    polar_density = [2 * math.cosh(i * dx / 2) * F[i] for i in range(sample_count)]
    polar_cumulative = [0.0] * sample_count
    for i in range(1, sample_count):
        polar_cumulative[i] = polar_cumulative[i - 1] + (
            polar_density[i - 1] + polar_density[i]
        ) * dx / 2
    prime_cumulative = [0.0] * sample_count
    first_atom_index = sample_count
    atom_margins: list[dict[str, float | int]] = []
    for atom in payload["prime_atoms"]:
        k = int(atom["k"])
        lag = float(atom["lag"])
        weight = float(atom["weight"])
        coordinate = lag / dx
        left = min(sample_count - 2, int(coordinate))
        fraction = coordinate - left
        value = F[left] * (1 - fraction) + F[left + 1] * fraction
        contribution = weight * value
        first = min(sample_count - 1, math.ceil(coordinate))
        first_atom_index = min(first_atom_index, first)
        for index in range(first, sample_count):
            prime_cumulative[index] += contribution
        atom_margins.append({
            "k": k,
            "lag": lag,
            "F": value,
            "jump": contribution,
            "post_jump_margin": polar_cumulative[first] - prime_cumulative[first],
        })
    budget = [p - s for p, s in zip(polar_cumulative, prime_cumulative)]
    start = min(first_atom_index, sample_count - 1)
    budget_tail = budget[start:]
    tail_index = start + min(range(len(budget_tail)), key=budget_tail.__getitem__)
    return {
        "physical_min": physical_min,
        "physical_min_x": physical_min_index * dx,
        "physical_imag_max": physical_imag_max,
        "physical_half_max_upward_step": max(physical_half_diffs),
        "physical_half_upward_steps": sum(step > 1e-10 for step in physical_half_diffs),
        "autocorrelation_min": min(correlation),
        "autocorrelation_negative_points": sum(value < -1e-10 for value in correlation),
        "autocorrelation_max_upward_step": max(corr_diffs),
        "autocorrelation_upward_steps": sum(step > 1e-10 for step in corr_diffs),
        "polar_prime_min_after_first_atom": budget[tail_index],
        "polar_prime_min_after_first_atom_lag": tail_index * dx,
        "polar_prime_final": budget[-1],
        "atom_margins": atom_margins,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--grid", type=int, default=65536)
    parser.add_argument("--out-json", type=Path, required=True)
    parser.add_argument("--out-csv", type=Path, required=True)
    args = parser.parse_args()
    if args.grid & (args.grid - 1):
        raise ValueError("grid must be a power of two")
    rows: list[dict[str, object]] = []
    for filename in sorted(glob.glob(str(args.results / "result-*.json"))):
        payload = json.loads(Path(filename).read_text(encoding="utf-8"))
        detail = diagnostics(payload, args.grid)
        rows.append({
            "file": Path(filename).name,
            "a": payload["a"],
            "N": payload["N"],
            "ground_eigenvalue": payload["ground_eigenvalue"],
            "component_energies": payload["component_energies"],
            **detail,
        })
    rows.sort(key=lambda row: (float(row["a"]), int(row["N"])))
    summary = {
        "result_count": len(rows),
        "grid": args.grid,
        "C1_negative_cases": sum(row["autocorrelation_negative_points"] > 0 for row in rows),
        "C1_upward_cases": sum(row["autocorrelation_upward_steps"] > 0 for row in rows),
        "C2_negative_cases": sum(row["polar_prime_min_after_first_atom"] < -1e-10 for row in rows),
        "physical_negative_cases": sum(row["physical_min"] < -1e-10 for row in rows),
        "rows": rows,
    }
    args.out_json.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    with args.out_csv.open("w", newline="", encoding="utf-8") as handle:
        fields = [
            "a", "N", "ground_eigenvalue", "autocorrelation_min",
            "autocorrelation_negative_points", "autocorrelation_max_upward_step",
            "autocorrelation_upward_steps", "polar_prime_min_after_first_atom",
            "polar_prime_min_after_first_atom_lag", "polar_prime_final", "physical_min",
            "physical_half_upward_steps",
        ]
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row[field] for field in fields})
    print(json.dumps({key: summary[key] for key in (
        "result_count", "grid", "C1_negative_cases", "C1_upward_cases",
        "C2_negative_cases", "physical_negative_cases",
    )}, indent=2))


if __name__ == "__main__":
    main()
