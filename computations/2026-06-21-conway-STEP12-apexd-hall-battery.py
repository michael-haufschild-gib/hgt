#!/usr/bin/env python3
"""STEP 12 stress for fire access -> APEX-D joint access gate.

Question:
  How often do single-lane or pairwise checks miss a joint obstruction?
"""

from __future__ import annotations

from itertools import combinations

import numpy as np


def max_bipartite_matching(left: list[int], right: list[int], edges: dict[int, set[int]]) -> int:
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


def hall_defect(left: list[int], edges: dict[int, set[int]]) -> int:
    best = 0
    for r in range(1, len(left) + 1):
        for subset in combinations(left, r):
            union = set()
            for u in subset:
                union |= edges[u]
            best = max(best, len(subset) - len(union))
    return best


def pairwise_pass(left: list[int], edges: dict[int, set[int]]) -> bool:
    for subset in combinations(left, 2):
        union = set().union(*(edges[u] for u in subset))
        sub_edges = {u: edges[u] for u in subset}
        if max_bipartite_matching(list(subset), list(union), sub_edges) < 2:
            return False
    return True


def random_edges(rng: np.random.Generator, lanes: int, slots: int, degree: int) -> dict[int, set[int]]:
    edges: dict[int, set[int]] = {}
    for u in range(lanes):
        deg = min(degree, slots)
        edges[u] = set(int(x) for x in rng.choice(slots, size=deg, replace=False))
    return edges


def main() -> None:
    rng = np.random.default_rng(2606212819)
    print("STEP 12 APEX-D Hall/access battery")
    print("lanes slots degree trials individual_pass pairwise_pass joint_pass pairwise_misses_joint hall_defect_rate")
    for lanes in [3, 4, 5, 6, 8]:
        for slots in [max(2, lanes - 1), lanes, lanes + 1]:
            for degree in [1, 2, 3]:
                if degree > slots:
                    continue
                trials = 600
                individual_count = 0
                pairwise_count = 0
                joint_count = 0
                miss_count = 0
                defect_count = 0
                left = list(range(lanes))
                right = list(range(slots))
                for _ in range(trials):
                    edges = random_edges(rng, lanes, slots, degree)
                    individual = all(edges[u] for u in left)
                    pairwise = pairwise_pass(left, edges)
                    joint = max_bipartite_matching(left, right, edges) == lanes
                    defect = hall_defect(left, edges) > 0
                    individual_count += int(individual)
                    pairwise_count += int(pairwise)
                    joint_count += int(joint)
                    miss_count += int(pairwise and not joint)
                    defect_count += int(defect)
                print(
                    f"{lanes:02d} {slots:02d} {degree:d} {trials:d} "
                    f"{individual_count/trials:.3f} {pairwise_count/trials:.3f} "
                    f"{joint_count/trials:.3f} {miss_count/trials:.3f} {defect_count/trials:.3f}"
                )
    print()
    print(
        "Interpretation: pairwise tests can miss joint failures in finite "
        "incidence systems, especially when slots are scarce. This gives a "
        "minimal finite witness format for APEX-D: C5* cannot be certified by "
        "single-lane or pairwise weld checks alone; it needs all-subset/joint "
        "access data."
    )


if __name__ == "__main__":
    main()
