#!/usr/bin/env python3
"""Compact-Weil ground floors and transform-zero locking.

Numerical experiment only. The matrix is the RH/zeros-side Gram used to propose a trial vector;
no output is a proof premise. Small cases are checked against published geometric-side values.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import mpmath as mp
from flint import acb_mat, arb, arb_mat, ctx


def load_zeros(path: Path, count: int) -> list[str]:
    rows: list[str] = []
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            if line.startswith("#") or not line.strip():
                continue
            _, value = line.split(maxsplit=1)
            rows.append(value.strip())
            if len(rows) == count:
                break
    if len(rows) != count:
        raise ValueError(f"wanted {count} zeros, found {len(rows)}")
    return rows


def build_sampling_matrix(L: arb, modes: int, zero_values: list[str]) -> arb_mat:
    pi = arb.pi()
    sqrt_L = L.sqrt()
    alphas = [pi * arb(2 * j + 1) / (2 * L) for j in range(modes)]
    matrix = arb_mat(len(zero_values), modes)
    for row, text in enumerate(zero_values):
        z = arb(text)
        common = (L * z).cos() * 2 / sqrt_L
        z_sq = z * z
        for col, alpha in enumerate(alphas):
            sign = -1 if col % 2 else 1
            matrix[row, col] = sign * common * alpha / (alpha * alpha - z_sq)
    return matrix


def midpoint_text(value: arb, digits: int) -> str:
    return value.mid().str(digits, radius=False)


def compute_ground(
    L_text: str,
    modes: int,
    zero_values: list[str],
    digits: int,
    threads: int,
) -> tuple[arb, list[arb], arb_mat, dict[str, float]]:
    ctx.dps = digits
    ctx.threads = threads
    started = time.time()
    sampling = build_sampling_matrix(arb(L_text), modes, zero_values)
    assembled = time.time()
    gram = sampling.transpose() * sampling * 2
    multiplied = time.time()
    eigenvalues, eigenvectors = acb_mat(gram).eig(right=True, algorithm="approx")
    diagonalized = time.time()

    index = min(range(modes), key=lambda k: float(eigenvalues[k].real.log()))
    vector = [eigenvectors[row, index].real for row in range(modes)]
    norm_sq = sum((entry * entry for entry in vector), arb(0))
    norm = norm_sq.sqrt()
    vector = [entry / norm for entry in vector]
    column = arb_mat([[entry] for entry in vector])
    rayleigh = (column.transpose() * gram * column)[0, 0]
    timings = {
        "sampling_seconds": assembled - started,
        "gram_seconds": multiplied - assembled,
        "eigensolve_seconds": diagonalized - multiplied,
    }
    return rayleigh, vector, sampling, timings


def tail_for_vector(
    L_text: str,
    vector: list[arb],
    zero_values: list[str],
) -> arb:
    if not zero_values:
        return arb(0)
    sampling = build_sampling_matrix(arb(L_text), len(vector), zero_values)
    column = arb_mat([[entry] for entry in vector])
    values = sampling * column
    return sum((2 * values[row, 0] * values[row, 0] for row in range(values.nrows())), arb(0))


def root_lock_statistics(
    L_text: str,
    vector_text: list[str],
    zero_text: list[str],
    digits: int,
) -> dict[str, object]:
    mp.mp.dps = digits
    L = mp.mpf(L_text)
    coefficients = [mp.mpf(value) for value in vector_text]
    alphas = [mp.pi * (j + mp.mpf("0.5")) / L for j in range(len(coefficients))]
    zeros = [mp.mpf(value) for value in zero_text]
    cutoff = 2 * mp.pi * mp.e ** (2 * L)
    target_count = sum(1 for z in zeros if z <= cutoff)
    targets = zeros[:target_count]

    def transform(t: mp.mpf) -> mp.mpf:
        total = mp.mpf("0")
        for j, (coefficient, alpha) in enumerate(zip(coefficients, alphas)):
            if abs(t - alpha) < mp.eps ** mp.mpf("0.25"):
                basis_value = L / mp.sqrt(L)
            else:
                basis_value = (
                    2
                    * ((-1) ** j)
                    * alpha
                    * mp.cos(L * t)
                    / (mp.sqrt(L) * (alpha * alpha - t * t))
                )
            total += coefficient * basis_value
        return total

    roots: list[mp.mpf | None] = []
    records: list[dict[str, str | int | bool]] = []
    for index, target in enumerate(targets):
        left_neighbor = mp.mpf("0") if index == 0 else targets[index - 1]
        right_neighbor = cutoff if index + 1 == len(targets) else targets[index + 1]
        left = (left_neighbor + target) / 2
        right = (target + right_neighbor) / 2
        grid = [left + (right - left) * k / 64 for k in range(65)]
        root: mp.mpf | None = None
        previous_x = grid[0]
        previous_y = transform(previous_x)
        brackets: list[tuple[mp.mpf, mp.mpf]] = []
        for current_x in grid[1:]:
            current_y = transform(current_x)
            if previous_y == 0 or current_y == 0 or previous_y * current_y < 0:
                brackets.append((previous_x, current_x))
            previous_x, previous_y = current_x, current_y
        if brackets:
            bracket = min(brackets, key=lambda pair: abs((pair[0] + pair[1]) / 2 - target))
            try:
                root = mp.findroot(transform, bracket, solver="anderson", verify=True)
            except (ValueError, ZeroDivisionError):
                root = None
        if root is None:
            try:
                candidate = mp.findroot(transform, (target - (target - left) / 4,
                                                    target + (right - target) / 4),
                                        verify=True)
                if left < candidate < right:
                    root = candidate
            except (ValueError, ZeroDivisionError):
                root = None
        roots.append(root)
        local_gap = min(target - left_neighbor, right_neighbor - target)
        records.append({
            "index": index + 1,
            "zeta_ordinate": mp.nstr(target, 30),
            "root_found": root is not None,
            "transform_root": "" if root is None else mp.nstr(root, 30),
            "absolute_offset": "" if root is None else mp.nstr(abs(root - target), 18),
            "gap_normalized_offset": "" if root is None else mp.nstr(abs(root - target) / local_gap, 18),
            "residual": "" if root is None else mp.nstr(abs(transform(root)), 8),
        })

    offsets = [abs(root - target) / min(
        target - (mp.mpf("0") if index == 0 else targets[index - 1]),
        (cutoff if index + 1 == len(targets) else targets[index + 1]) - target,
    ) for index, (root, target) in enumerate(zip(roots, targets)) if root is not None]
    return {
        "cutoff_T_star": mp.nstr(cutoff, 30),
        "target_zero_count": target_count,
        "matched_root_count": len(offsets),
        "max_gap_normalized_offset": None if not offsets else mp.nstr(max(offsets), 18),
        "median_gap_normalized_offset": None if not offsets else mp.nstr(sorted(offsets)[len(offsets) // 2], 18),
        "records": records,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zeros", type=Path, required=True)
    parser.add_argument("--L", required=True)
    parser.add_argument("--modes", type=int, required=True)
    parser.add_argument("--ground-zeros", type=int, required=True)
    parser.add_argument("--tail-zeros", type=int, required=True)
    parser.add_argument("--digits", type=int, required=True)
    parser.add_argument("--threads", type=int, default=32)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    all_zeros = load_zeros(args.zeros, args.ground_zeros + args.tail_zeros)
    rayleigh, vector, _, timings = compute_ground(
        args.L, args.modes, all_zeros[: args.ground_zeros], args.digits, args.threads
    )
    tail = tail_for_vector(args.L, vector, all_zeros[args.ground_zeros :])
    vector_text = [midpoint_text(entry, args.digits - 10) for entry in vector]
    total = rayleigh + tail
    locking = root_lock_statistics(
        args.L, vector_text, all_zeros, min(args.digits - 10, 180)
    )
    payload = {
        "L": args.L,
        "modes": args.modes,
        "ground_zero_count": args.ground_zeros,
        "tail_zero_count": args.tail_zeros,
        "digits": args.digits,
        "rayleigh_ground_truncation": midpoint_text(rayleigh, args.digits - 10),
        "fixed_vector_tail_contribution": midpoint_text(tail, args.digits - 10),
        "fixed_vector_total": midpoint_text(total, args.digits - 10),
        "minus_log_fixed_vector_total": midpoint_text(-total.log(), 40),
        "coefficient_l2_error": midpoint_text(
            abs(sum((entry * entry for entry in vector), arb(0)) - 1), 20
        ),
        "timings": timings,
        "locking": locking,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: payload[key] for key in (
        "L", "modes", "fixed_vector_total", "minus_log_fixed_vector_total", "timings"
    )}, indent=2))


if __name__ == "__main__":
    main()
