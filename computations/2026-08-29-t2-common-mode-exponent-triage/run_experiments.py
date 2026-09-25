#!/usr/bin/env python3
"""Route-T2 common-mode exponent and finite Fourier adversarial audit.

This is exploratory route triage only.  Nothing emitted by this program is an
input to a Lean proof.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import multiprocessing as mp
import os
import platform
import random
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction
from pathlib import Path
from typing import Any

# Prevent 128 Python processes from each starting a threaded BLAS team.
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("NUMEXPR_NUM_THREADS", "1")

import numpy as np


def qstr(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def qrecord(x: Fraction) -> dict[str, Any]:
    return {"fraction": qstr(x), "decimal": float(x)}


# Exact constants copied from the named corpus definitions listed in REPORT.md.
DELTA = Fraction(1, 3 * (2**47) * 380)
NU = Fraction(1, 2) - DELTA / 2
THETA = Fraction(3, 4) - DELTA / 2
MU_BUFFER = Fraction(4, 1) / (1 + 3 * DELTA / 2)
S_BUFFER = 1 / MU_BUFFER
PAIRED_RESERVE = MU_BUFFER * (1 - THETA) - 1
PHYSICAL_RESERVE = 2 - MU_BUFFER * (1 - NU)

S_MIN = Fraction(1, 8)
S_MAX = Fraction(5, 8)
S_FORCED_MIN = Fraction(5, 11)
G_MIN = Fraction(31, 80)
G_CORPUS_MAX = Fraction(71, 100)
G_LITERATURE_MAX = Fraction(13, 25)  # Runbo Li's x^0.52 result.
TARGET_ROUTE = 1 + NU
TARGET_CRITICAL = Fraction(3, 2)


def paired_fixed_raw(s: Fraction) -> Fraction:
    """Power of physical x in the proved buffered L2 bad-measure RHS."""
    return 1 + s * (1 - 2 * PAIRED_RESERVE)


def paired_unfrozen_raw(s: Fraction) -> Fraction:
    """Hypothetical power retaining the exact yR gain before buffer freezing."""
    return 1 + s - 2 * ((1 - THETA) - s)


def selected_raw(s: Fraction) -> Fraction:
    """Power of physical x in the forced-second spatial measure term."""
    return s + NU


def capped(x: Fraction) -> Fraction:
    """The physical block itself has volume exponent one."""
    return min(Fraction(1), x)


def exact_audit() -> dict[str, Any]:
    paired_current_bottom = G_MIN + paired_fixed_raw(S_MIN)
    paired_current_buffer = G_MIN + paired_fixed_raw(S_BUFFER)
    paired_unfrozen_bottom = G_MIN + paired_unfrozen_raw(S_MIN)
    paired_unfrozen_buffer = G_MIN + paired_unfrozen_raw(S_BUFFER)
    selected_current_top = G_MIN + selected_raw(S_MAX)

    # Largest central exponent compatible with a strict-subcritical low-shell
    # moment, before any logarithmic losses.
    central_limit_critical = (Fraction(1, 2) - G_MIN) / (1 - 2 * PAIRED_RESERVE)
    central_limit_route = (NU - G_MIN) / (1 - 2 * PAIRED_RESERVE)

    # A K-th order absolute tail at target reciprocal exponent 49/80 needs
    # v_K=(49/80)(1+1/K).  It can never recover the exact 1+nu route exponent.
    # It is merely sub-3/2 when 49/(80K)<delta/2.
    k_threshold = Fraction(49, 40) / DELTA
    k_min_strict = k_threshold.numerator // k_threshold.denominator + 1

    return {
        "constants": {
            "maynard_long_global_amplitude_deficit_delta": qrecord(DELTA),
            "routeT_gap_moment_nu": qrecord(NU),
            "routeT_physical_slice_handoff_theta": qrecord(THETA),
            "routeT_paired_kernel_buffered_mu": qrecord(MU_BUFFER),
            "paired_shell_x_exponent_boundary_1_over_mu": qrecord(S_BUFFER),
            "routeT_paired_kernel_decay_reserve": qrecord(PAIRED_RESERVE),
            "routeT_physical_slice_buffered_reserve": qrecord(PHYSICAL_RESERVE),
            "paired_reserve_identity_delta_over_2_plus_3delta": qrecord(
                DELTA / (2 + 3 * DELTA)
            ),
        },
        "domains": {
            "shell_x_exponent": [qrecord(S_MIN), qrecord(S_MAX)],
            "paired_shell_x_exponent": [qrecord(S_MIN), qrecord(S_BUFFER)],
            "forced_second_shell_x_exponent": [qrecord(S_FORCED_MIN), qrecord(S_MAX)],
            "uncovered_common_mode_packet_interval": [
                qrecord(S_BUFFER),
                qrecord(S_FORCED_MIN),
            ],
            "uncovered_interval_width": qrecord(S_FORCED_MIN - S_BUFFER),
            "gap_x_exponent_corpus": [qrecord(G_MIN), qrecord(G_CORPUS_MAX)],
            "gap_x_exponent_literature": [qrecord(G_MIN), qrecord(G_LITERATURE_MAX)],
        },
        "decisive_losses": {
            "proved_buffered_L2_raw_bottom_minus_route_target": qrecord(
                paired_current_bottom - TARGET_ROUTE
            ),
            "proved_buffered_L2_raw_buffer_minus_route_target": qrecord(
                paired_current_buffer - TARGET_ROUTE
            ),
            "unfrozen_kernel_bottom_minus_route_target": qrecord(
                paired_unfrozen_bottom - TARGET_ROUTE
            ),
            "unfrozen_kernel_buffer_minus_route_target": qrecord(
                paired_unfrozen_buffer - TARGET_ROUTE
            ),
            "forced_second_top_minus_route_target": qrecord(
                selected_current_top - TARGET_ROUTE
            ),
            "forced_second_top_minus_three_halves": qrecord(
                selected_current_top - TARGET_CRITICAL
            ),
            "trivial_cap_literature_gap_minus_three_halves": qrecord(
                1 + G_LITERATURE_MAX - TARGET_CRITICAL
            ),
            "trivial_cap_corpus_gap_minus_three_halves": qrecord(
                1 + G_CORPUS_MAX - TARGET_CRITICAL
            ),
        },
        "necessary_repairs": {
            "max_central_shell_exponent_for_sub_three_halves": qrecord(
                central_limit_critical
            ),
            "max_central_shell_exponent_for_route_1_plus_nu": qrecord(
                central_limit_route
            ),
            "current_central_shell_exponent": qrecord(S_MIN),
            "max_outer_shell_exponent_at_min_gap_for_route_1_plus_nu": qrecord(
                1 - G_MIN
            ),
            "current_outer_shell_exponent": qrecord(S_MAX),
            "minimum_density_saving_over_trivial_for_literature_gap": qrecord(
                G_LITERATURE_MAX - Fraction(1, 2)
            ),
            "minimum_density_saving_over_trivial_for_corpus_gap": qrecord(
                G_CORPUS_MAX - Fraction(1, 2)
            ),
            "absolute_tail_order_threshold_for_any_sub_three_halves": {
                "strictly_greater_than": qrecord(k_threshold),
                "minimum_integer": k_min_strict,
            },
            "finite_absolute_tail_order_can_reach_exact_1_plus_nu": False,
        },
    }


def model_measure(name: str, s: np.ndarray, nu: float, theta: float,
                  s_buffer: float, s_forced: float, paired_reserve: float) -> np.ndarray:
    ones = np.ones_like(s)
    paired_fixed = np.minimum(ones, 1 + s * (1 - 2 * paired_reserve))
    paired_exact = np.minimum(ones, 2 * theta - 1 + 3 * s)
    selected = np.minimum(ones, s + nu)
    if name == "current_interfaces":
        return np.where(s <= s_buffer, paired_fixed,
                        np.where(s >= s_forced, selected, ones))
    if name == "unfrozen_kernel":
        return np.where(s <= s_buffer, paired_exact,
                        np.where(s >= s_forced, selected, ones))
    if name == "physical_slice_weld":
        return np.where(s <= s_buffer, paired_exact, selected)
    if name == "all_selected":
        return selected
    raise ValueError(name)


def grid_chunk(task: tuple[str, float, float, int, int, int]) -> dict[str, Any]:
    name, g_lo, g_hi, denominator, i0, i1 = task
    s0 = math.ceil(float(S_MIN) * denominator)
    s1 = math.floor(float(S_MAX) * denominator)
    s = np.arange(s0, s1 + 1, dtype=np.float64) / denominator
    g = np.linspace(g_lo, g_hi, i1 - i0, endpoint=False, dtype=np.float64)
    if i1 == i0:
        return {"max": -math.inf, "arg": None, "violations": 0, "points": 0}
    # Offset this worker's regular subgrid deterministically.
    total_g = 8192
    gi = np.arange(i0, i1, dtype=np.float64)
    g = g_lo + (g_hi - g_lo) * gi / (total_g - 1)
    base_name = name.removeprefix("target_cut_")
    m = model_measure(
        base_name,
        s,
        float(NU),
        float(THETA),
        float(S_BUFFER),
        float(S_FORCED_MIN),
        float(PAIRED_RESERVE),
    )
    e = g[:, None] + m[None, :]
    valid = np.ones_like(e, dtype=bool)
    if name.startswith("target_cut_"):
        # Exact reciprocal target cutoff A <= x/h, i.e. s+g <= 1.
        valid = s[None, :] + g[:, None] <= 1.0 + 1e-15
        e = np.where(valid, e, -np.inf)
    flat = int(np.argmax(e))
    row, col = np.unravel_index(flat, e.shape)
    return {
        "max": float(e[row, col]),
        "arg": [float(g[row]), float(s[col])],
        "violations": int(np.count_nonzero(valid & (e >= 1.5))),
        "points": int(np.count_nonzero(valid)),
    }


def multicore_grid(workers: int, denominator: int) -> list[dict[str, Any]]:
    models = [
        "current_interfaces",
        "unfrozen_kernel",
        "physical_slice_weld",
        "all_selected",
        "target_cut_physical_slice_weld",
        "target_cut_all_selected",
    ]
    ranges = [
        ("corpus", float(G_MIN), float(G_CORPUS_MAX)),
        ("literature", float(G_MIN), float(G_LITERATURE_MAX)),
    ]
    total_g = 8192
    chunks = []
    chunk_size = math.ceil(total_g / workers)
    for model in models:
        for label, g_lo, g_hi in ranges:
            for i0 in range(0, total_g, chunk_size):
                chunks.append((model, label, (model, g_lo, g_hi, denominator,
                                              i0, min(total_g, i0 + chunk_size))))

    merged: dict[tuple[str, str], dict[str, Any]] = {}
    with ProcessPoolExecutor(max_workers=workers) as pool:
        futures = {
            pool.submit(grid_chunk, task): (model, label)
            for model, label, task in chunks
        }
        for future in as_completed(futures):
            key = futures[future]
            item = future.result()
            acc = merged.setdefault(key, {
                "max": -math.inf,
                "arg": None,
                "violations": 0,
                "points": 0,
            })
            if item["max"] > acc["max"]:
                acc["max"] = item["max"]
                acc["arg"] = item["arg"]
            acc["violations"] += item["violations"]
            acc["points"] += item["points"]

    rows = []
    for (model, label), acc in sorted(merged.items()):
        rows.append({
            "model": model,
            "gap_range": label,
            "maximum_moment_exponent": acc["max"],
            "argmax_gap_shell": acc["arg"],
            "fraction_at_or_above_three_halves": acc["violations"] / acc["points"],
            "grid_points": acc["points"],
        })
    return rows


def additive_energy(subset: tuple[int, ...] | np.ndarray, q: int) -> int:
    a = np.asarray(subset, dtype=np.int64)
    counts = np.bincount(((a[:, None] + a[None, :]) % q).ravel(), minlength=q)
    return int(counts @ counts)


def additive_energy_small(subset: tuple[int, ...], q: int) -> int:
    counts = [0] * q
    for a in subset:
        for b in subset:
            counts[(a + b) % q] += 1
    return sum(value * value for value in counts)


def exhaustive_energy_worker(task: tuple[int, int, int]) -> dict[str, Any]:
    q, n, second = task
    best = -1
    example: tuple[int, ...] | None = None
    count = 0
    tested = 0
    for tail in itertools.combinations(range(second + 1, q), n - 2):
        subset = (0, second, *tail)
        energy = additive_energy_small(subset, q)
        tested += 1
        if energy > best:
            best = energy
            example = subset
            count = 1
        elif energy == best:
            count += 1
    return {"best": best, "example": example, "count": count, "tested": tested}


def exhaustive_energy_search(workers: int, q: int = 31, n: int = 8) -> dict[str, Any]:
    tasks = [(q, n, second) for second in range(1, q - n + 2)]
    best = -1
    examples = []
    maximizer_count = 0
    tested = 0
    with ProcessPoolExecutor(max_workers=min(workers, len(tasks))) as pool:
        for item in pool.map(exhaustive_energy_worker, tasks):
            tested += item["tested"]
            if item["best"] > best:
                best = item["best"]
                examples = [item["example"]]
                maximizer_count = item["count"]
            elif item["best"] == best:
                if len(examples) < 8:
                    examples.append(item["example"])
                maximizer_count += item["count"]
    ap_energy = (2 * n**3 + n) // 3
    return {
        "q": q,
        "cardinality": n,
        "subsets_tested_after_translation_normalization": tested,
        "maximum_additive_energy_found": best,
        "arithmetic_progression_energy": ap_energy,
        "maximum_equals_arithmetic_progression_energy": best == ap_energy,
        "maximizers_in_normalized_search": maximizer_count,
        "examples": examples,
        "energy_over_cardinality_cubed": best / n**3,
    }


def anneal_worker(task: tuple[int, int, int, int]) -> dict[str, Any]:
    q, n, steps, seed = task
    rng = random.Random(seed)
    if seed % 2:
        start = rng.randrange(q)
        step = rng.randrange(1, q)
        while math.gcd(step, q) != 1:
            step = rng.randrange(1, q)
        subset = {(start + j * step) % q for j in range(n)}
        # Perturb a few entries so the search is not handed the answer.
        for _ in range(max(1, n // 8)):
            subset.remove(rng.choice(tuple(subset)))
            subset.add(rng.choice(tuple(set(range(q)) - subset)))
    else:
        subset = set(rng.sample(range(q), n))
    current = additive_energy(tuple(sorted(subset)), q)
    best = current
    best_subset = tuple(sorted(subset))
    for k in range(steps):
        out = rng.choice(tuple(subset))
        incoming = rng.randrange(q)
        while incoming in subset:
            incoming = rng.randrange(q)
        proposal = set(subset)
        proposal.remove(out)
        proposal.add(incoming)
        energy = additive_energy(tuple(sorted(proposal)), q)
        temperature = max(0.05, 3.0 * (1 - k / steps))
        if energy >= current or rng.random() < math.exp((energy - current) / temperature):
            subset = proposal
            current = energy
        if current > best:
            best = current
            best_subset = tuple(sorted(subset))
    return {"energy": best, "subset": best_subset, "seed": seed}


def anneal_energy_search(workers: int, q: int = 521, n: int = 64,
                         steps: int = 2500) -> dict[str, Any]:
    tasks = [(q, n, steps, 99173 + i) for i in range(workers)]
    best = max(
        (anneal_worker(task) for task in tasks),
        key=lambda item: item["energy"],
    ) if workers == 1 else None
    if workers > 1:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            best = max(pool.map(anneal_worker, tasks), key=lambda item: item["energy"])
    assert best is not None
    ap_energy = (2 * n**3 + n) // 3
    return {
        "q": q,
        "cardinality": n,
        "workers": workers,
        "steps_per_worker": steps,
        "best_energy_found": best["energy"],
        "arithmetic_progression_energy": ap_energy,
        "best_over_arithmetic_progression": best["energy"] / ap_energy,
        "best_energy_over_cardinality_cubed": best["energy"] / n**3,
        "best_seed": best["seed"],
        "best_subset": best["subset"],
    }


def structured_fourier_packets() -> list[dict[str, Any]]:
    rows = []
    for n in [8, 16, 32, 64, 128, 256, 512, 1024, 4096, 16384]:
        energy = (2 * n**3 + n) // 3
        rows.append({
            "cardinality": n,
            "exact_additive_energy": energy,
            "energy_over_n_cubed": energy / n**3,
            "l2_character_moment": n,
            "l4_character_moment": energy,
            "peak_character_sum": n,
        })
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--grid-denominator", type=int, default=16384)
    parser.add_argument("--anneal-steps", type=int, default=2500)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    workers = max(1, min(args.workers, os.cpu_count() or args.workers))
    started = time.time()

    exact = exact_audit()
    grid = multicore_grid(workers, args.grid_denominator)
    exhaustive = exhaustive_energy_search(workers)
    anneal = anneal_energy_search(workers, steps=args.anneal_steps)
    structured = structured_fourier_packets()

    result = {
        "purpose": "Exploratory route triage only; never a Lean proof input.",
        "environment": {
            "python": platform.python_version(),
            "numpy": np.__version__,
            "platform": platform.platform(),
            "cpu_count": os.cpu_count(),
            "workers": workers,
        },
        "exact_rational_audit": exact,
        "multicore_grid_audit": grid,
        "finite_fourier_adversarial_search": {
            "exhaustive": exhaustive,
            "parallel_local_search": anneal,
            "structured_arithmetic_progressions": structured,
            "interpretation": (
                "Arithmetic-progression cell sets have additive energy asymptotic to "
                "(2/3)n^3 and Dirichlet-kernel peak n. Thus the generic interval-cell "
                "L4/R* branch cannot supply a power saving beyond the cubic exponent."
            ),
        },
        "elapsed_seconds": time.time() - started,
    }
    (args.output / "results.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    with (args.output / "model_summary.csv").open("w", encoding="utf-8") as handle:
        handle.write(
            "model,gap_range,maximum_moment_exponent,argmax_gap,argmax_shell,"
            "fraction_at_or_above_three_halves,grid_points\n"
        )
        for row in grid:
            handle.write(
                f"{row['model']},{row['gap_range']},"
                f"{row['maximum_moment_exponent']:.17g},"
                f"{row['argmax_gap_shell'][0]:.17g},"
                f"{row['argmax_gap_shell'][1]:.17g},"
                f"{row['fraction_at_or_above_three_halves']:.17g},"
                f"{row['grid_points']}\n"
            )
    with (args.output / "fourier_packets.csv").open("w", encoding="utf-8") as handle:
        handle.write(
            "cardinality,exact_additive_energy,energy_over_n_cubed,"
            "l2_character_moment,l4_character_moment,peak_character_sum\n"
        )
        for row in structured:
            handle.write(
                f"{row['cardinality']},{row['exact_additive_energy']},"
                f"{row['energy_over_n_cubed']:.17g},"
                f"{row['l2_character_moment']},{row['l4_character_moment']},"
                f"{row['peak_character_sum']}\n"
            )
    print(json.dumps({
        "elapsed_seconds": result["elapsed_seconds"],
        "workers": workers,
        "exhaustive": exhaustive,
        "anneal_best_ratio": anneal["best_over_arithmetic_progression"],
        "output": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    mp.set_start_method("fork")
    main()
