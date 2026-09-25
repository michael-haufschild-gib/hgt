#!/usr/bin/env python3
"""Independent consistency checks for downloaded Route-T2 experiment data."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


def parse_q(record: dict[str, object]) -> Fraction:
    return Fraction(str(record["fraction"]))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=Path)
    args = parser.parse_args()
    data = json.loads(args.results.read_text(encoding="utf-8"))
    exact = data["exact_rational_audit"]
    constants = exact["constants"]
    domains = exact["domains"]
    losses = exact["decisive_losses"]

    delta = parse_q(constants["maynard_long_global_amplitude_deficit_delta"])
    nu = parse_q(constants["routeT_gap_moment_nu"])
    theta = parse_q(constants["routeT_physical_slice_handoff_theta"])
    mu_buffer = parse_q(constants["routeT_paired_kernel_buffered_mu"])
    reserve = parse_q(constants["routeT_paired_kernel_decay_reserve"])
    physical_reserve = parse_q(constants["routeT_physical_slice_buffered_reserve"])

    assert delta == Fraction(1, 3 * 2**47 * 380)
    assert nu == Fraction(1, 2) - delta / 2
    assert theta == Fraction(3, 4) - delta / 2
    assert mu_buffer == Fraction(4, 1) / (1 + 3 * delta / 2)
    assert reserve == delta / (2 + 3 * delta)
    assert physical_reserve == 2 * reserve
    assert parse_q(domains["uncovered_interval_width"]) > 0

    assert parse_q(losses["forced_second_top_minus_route_target"]) == Fraction(1, 80)
    assert parse_q(losses["forced_second_top_minus_three_halves"]) == Fraction(1, 80) - delta / 2
    assert parse_q(losses["trivial_cap_literature_gap_minus_three_halves"]) == Fraction(1, 50)
    assert parse_q(losses["trivial_cap_corpus_gap_minus_three_halves"]) == Fraction(21, 100)

    finite = data["finite_fourier_adversarial_search"]
    exhaustive = finite["exhaustive"]
    assert exhaustive["maximum_equals_arithmetic_progression_energy"]
    for row in finite["structured_arithmetic_progressions"]:
        n = int(row["cardinality"])
        assert int(row["exact_additive_energy"]) == (2 * n**3 + n) // 3
        assert int(row["peak_character_sum"]) == n

    grid = {(row["model"], row["gap_range"]): row
            for row in data["multicore_grid_audit"]}
    assert grid[("current_interfaces", "corpus")]["maximum_moment_exponent"] > 1.5
    assert grid[("current_interfaces", "literature")]["maximum_moment_exponent"] > 1.5
    assert grid[("target_cut_physical_slice_weld", "corpus")]["maximum_moment_exponent"] > 1.5
    assert grid[("target_cut_all_selected", "corpus")]["maximum_moment_exponent"] < 1.500000000001
    assert grid[("target_cut_all_selected", "literature")]["maximum_moment_exponent"] < 1.500000000001
    print("verified: exact identities, route losses, grid verdicts, Fourier countermodels")


if __name__ == "__main__":
    main()
