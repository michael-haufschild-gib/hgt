#!/usr/bin/env python3
"""Clean GPT-topic finding 54 candidate: A/B implication measure counterexample."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Cell:
    a: int
    b: int
    weight: float


def conditional_b_given_a(cells: list[Cell]) -> float:
    denom = sum(c.weight for c in cells if c.a == 1)
    numer = sum(c.weight for c in cells if c.a == 1 and c.b == 1)
    return numer / denom


def conditional_a_given_b(cells: list[Cell]) -> float:
    denom = sum(c.weight for c in cells if c.b == 1)
    numer = sum(c.weight for c in cells if c.a == 1 and c.b == 1)
    return numer / denom


def counterexample_mass(cells: list[Cell], a: int, b: int) -> float:
    total = sum(c.weight for c in cells)
    return sum(c.weight for c in cells if c.a == a and c.b == b) / total


def node_anthropic_measure_problem() -> None:
    # Same coarse "observers exist" selection, different measure over worlds.
    worlds = [
        ("ordinary_observers", 1.0, 1.0),
        ("youngness_runaway", 1.0, 500.0),
        ("boltzmann_tail", 0.2, 5000.0),
    ]
    print("NODE: measure choice can dominate anthropic weighting")
    print("measure posterior_ordinary posterior_runaway posterior_boltzmann")
    for measure_name, measure_weights in [
        ("flat_pocket", [1.0, 1.0, 1.0]),
        ("volume_weighted", [1.0, 80.0, 40.0]),
        ("bb_suppressed", [1.0, 80.0, 0.001]),
    ]:
        raw = [m * obs for (_, obs, m), m in zip(worlds, measure_weights)]
        total = sum(raw)
        probs = [x / total for x in raw]
        print(f"{measure_name:15s} {probs[0]:.4f} {probs[1]:.4f} {probs[2]:.4f}")
    print("constraint: selection factors do not define predictions until the measure/reference class is fixed")


def transfer_ab_counterexample() -> None:
    measures = {
        "uniform_all_cells": [
            Cell(0, 0, 1.0),
            Cell(0, 1, 1.0),
            Cell(1, 0, 1.0),
            Cell(1, 1, 1.0),
        ],
        "looks_A_implies_B": [
            Cell(0, 0, 1.0),
            Cell(0, 1, 1.0),
            Cell(1, 0, 0.001),
            Cell(1, 1, 1.0),
        ],
        "looks_A_excludes_B": [
            Cell(0, 0, 1.0),
            Cell(0, 1, 1.0),
            Cell(1, 0, 1.0),
            Cell(1, 1, 0.001),
        ],
        "looks_coupled_both_ways": [
            Cell(0, 0, 20.0),
            Cell(0, 1, 0.2),
            Cell(1, 0, 0.2),
            Cell(1, 1, 20.0),
        ],
    }
    print()
    print("TRANSFER: ResearchNode #68 Schanuel-vs-RH independence")
    print("method #16 minimal counterexample: all four A/B cells exist, weights fake implication")
    print("measure P_B_given_A P_A_given_B mass_A_not_B mass_A_and_B logical_implication")
    for name, cells in measures.items():
        logical = "false" if any(c.a == 1 and c.b == 0 and c.weight > 0 for c in cells) else "possible"
        print(
            f"{name:24s} {conditional_b_given_a(cells):.4f} {conditional_a_given_b(cells):.4f} "
            f"{counterexample_mass(cells, 1, 0):.6f} {counterexample_mass(cells, 1, 1):.6f} {logical}"
        )
    print()
    print("GATE SUMMARY")
    print(
        "empirical A/B association is not implication unless the counterexample cell is ruled out, "
        "not merely down-weighted by the chosen ensemble"
    )
    print(
        "Schanuel-vs-RH experiments need a measure/reference-class passport: report all four cells "
        "or prove that a cell is impossible structurally"
    )


def main() -> None:
    node_anthropic_measure_problem()
    transfer_ab_counterexample()


if __name__ == "__main__":
    main()
