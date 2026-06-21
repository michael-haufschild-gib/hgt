#!/usr/bin/env python3
"""STEP 12 HGT follow-up for fire access -> APEX-D.

The finite Hall examples are only a graph-theory warning.  This script asks
whether the same all-lane obstruction can be built from actual HGT lane data:
individual Euler-prime lanes versus archimedean time slots.

Edges mean: prime lane p has one of its strongest gamma-vs-local-Euler phase
defect events in that time slot.  The false certification rule is "all lanes
and all pairs can be assigned slots, so the joint weld is feasible."  Hall
checks the all-lane assignment.
"""

from __future__ import annotations

from itertools import combinations
import math

import mpmath as mp
import numpy as np


def first_primes(n: int) -> list[int]:
    out: list[int] = []
    candidate = 2
    while len(out) < n:
        ok = True
        for p in out:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            out.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return out


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def local_prime_term(s: complex, p: int) -> complex:
    q = mp.fp.power(p, -s)
    return complex(-math.log(p) * q / (1.0 - q))


def phase_defect(a: complex, b: complex) -> float:
    return max(0.0, math.log(max(abs(a), abs(b)) + 1e-300) - math.log(abs(a + b) + 1e-300))


def max_bipartite_matching(left: list[int], edges: dict[int, set[int]]) -> int:
    match_r: dict[int, int] = {}

    def aug(u: int, seen: set[int]) -> bool:
        for v in edges.get(u, set()):
            if v in seen:
                continue
            seen.add(v)
            if v not in match_r or aug(match_r[v], seen):
                match_r[v] = u
                return True
        return False

    return sum(1 for u in left if aug(u, set()))


def hall_defect(left: list[int], edges: dict[int, set[int]]) -> tuple[int, str]:
    best = 0
    witness = "-"
    for r in range(1, len(left) + 1):
        for subset in combinations(left, r):
            union = set()
            for u in subset:
                union |= edges[u]
            defect = len(subset) - len(union)
            if defect > best:
                best = defect
                witness = "{" + ",".join(f"p{left[u]}" for u in subset) + "}->{" + ",".join(
                    f"A{v}" for v in sorted(union)
                ) + "}"
    return best, witness


def pairwise_pass(left: list[int], edges: dict[int, set[int]]) -> bool:
    for subset in combinations(left, 2):
        sub_edges = {u: edges[u] for u in subset}
        if max_bipartite_matching(list(subset), sub_edges) < 2:
            return False
    return True


def bin_scores(
    sigma: float,
    window: tuple[float, float],
    samples: int,
    primes: list[int],
    slots: int,
    kind: str,
    rng: np.random.Generator,
) -> np.ndarray:
    values = np.zeros((samples, len(primes)), dtype=float)
    for j, t in enumerate(np.linspace(window[0], window[1], samples)):
        s = complex(sigma, float(t))
        a = gamma_part(s)
        for i, p in enumerate(primes):
            b = local_prime_term(s, p)
            if kind == "random_phase":
                theta = rng.uniform(-math.pi, math.pi)
                b = abs(b) * complex(math.cos(theta), math.sin(theta))
            values[j, i] = phase_defect(a, b)
    if kind == "time_shift":
        for i in range(values.shape[1]):
            shift = int(rng.integers(samples // 5, 4 * samples // 5))
            values[:, i] = np.roll(values[:, i], shift)

    scores = np.zeros((len(primes), slots), dtype=float)
    cuts = np.array_split(np.arange(samples), slots)
    for lane in range(len(primes)):
        for slot, idx in enumerate(cuts):
            scores[lane, slot] = float(np.max(values[idx, lane]))
    return scores


def incidence_from_top(scores: np.ndarray, degree: int) -> dict[int, set[int]]:
    edges: dict[int, set[int]] = {}
    for lane in range(scores.shape[0]):
        order = np.argsort(scores[lane])[::-1]
        edges[lane] = set(int(x) for x in order[: min(degree, scores.shape[1])])
    return edges


def summarize_case(
    sigma: float,
    label: str,
    window: tuple[float, float],
    lanes: int,
    slots: int,
    degree: int,
    kind: str,
    rng: np.random.Generator,
) -> tuple[str, bool, bool, bool]:
    primes = first_primes(lanes)
    scores = bin_scores(sigma, window, 420, primes, slots, kind, rng)
    edges = incidence_from_top(scores, degree)
    left = list(range(lanes))
    individual = all(bool(edges[u]) for u in left)
    pairwise = pairwise_pass(left, edges)
    matching = max_bipartite_matching(left, edges)
    joint = matching == lanes
    defect, witness = hall_defect(left, edges)
    loads = [sum(int(slot in edges[u]) for u in left) for slot in range(slots)]
    line = (
        f"{label:13s} {kind:12s} sigma={sigma:.2f} lanes={lanes:02d} slots={slots:02d} degree={degree:d} "
        f"individual={int(individual)} pairwise={int(pairwise)} joint={int(joint)} "
        f"matching={matching:02d}/{lanes:02d} hall_defect={defect:d} "
        f"max_slot_load={max(loads):02d} witness={witness}"
    )
    return line, pairwise, joint, defect > 0


def main() -> None:
    rng = np.random.default_rng(2606213021)
    cases = [
        ("low_zero", 0.50, (14.0, 84.0)),
        ("critical", 0.50, (100.0, 170.0)),
        ("off_seam", 0.70, (100.0, 170.0)),
        ("right", 1.20, (100.0, 170.0)),
    ]
    configs = [
        (4, 4, 2),
        (5, 5, 2),
        (6, 6, 2),
        (8, 8, 2),
        (8, 9, 2),
        (8, 8, 3),
    ]
    kinds = ["true", "time_shift", "random_phase"]

    print("STEP 12 HGT APEX-D joint-access battery")
    print("Edges: prime lane p -> archimedean time slot A when p has a top local gamma/Euler phase-defect event there.")
    print("The finite Hall theorem is known; the HGT question is whether pairwise certification misses all-lane access in actual lane data.")
    print()
    print("case          kind         params and verdict")

    pairwise_miss = {kind: 0 for kind in kinds}
    total = {kind: 0 for kind in kinds}
    defects = {kind: 0 for kind in kinds}
    true_specific = 0
    true_total = 0

    for label, sigma, window in cases:
        for lanes, slots, degree in configs:
            rows = {}
            for kind in kinds:
                line, pairwise, joint, defect = summarize_case(
                    sigma, label, window, lanes, slots, degree, kind, rng
                )
                rows[kind] = (line, pairwise, joint, defect)
                print(line)
                total[kind] += 1
                pairwise_miss[kind] += int(pairwise and not joint)
                defects[kind] += int(defect)
            true_pairwise, true_joint = rows["true"][1], rows["true"][2]
            control_joint = rows["time_shift"][2] or rows["random_phase"][2]
            true_specific += int(true_pairwise and not true_joint and control_joint)
            true_total += 1
        print()

    print("SUMMARY")
    for kind in kinds:
        print(
            f"{kind:12s} pairwise_misses_joint={pairwise_miss[kind]}/{total[kind]} "
            f"hall_defects={defects[kind]}/{total[kind]}"
        )
    print(f"true_pairwise_miss_with_some_control_joint_pass={true_specific}/{true_total}")
    print()
    print(
        "Interpretation: if true pairwise-miss rows occur while at least one control jointly passes, "
        "the useful APEX-D output is not Hall's theorem itself. It is a concrete all-lane access "
        "diagnostic for weld experiments: single-lane and pairwise checks are an insufficient C5* "
        "certification protocol."
    )


if __name__ == "__main__":
    main()
