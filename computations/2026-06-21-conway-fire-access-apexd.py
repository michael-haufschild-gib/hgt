#!/usr/bin/env python3
"""THE-MACHINE tick: urban fire access constraints -> APEX-D C5/C5*.

NODE:
  Road closures, access obstructions, hydrant access problems, and staging
  constraints.

Consolidated target:
  APEX-D -- C5/C5*: the native joint sigma_p weld / branchhood lock.

STEP 9 method:
  16. Use a minimal counterexample.
"""

from __future__ import annotations

from collections import deque
from itertools import combinations


NODE = "road closures access obstructions hydrant access problems and staging constraints"

TRANSFER_ATTEMPTS = [
    "joint sigma weld access can fail from shared staging constraints although each lane is open",
    "APEX D needs simultaneous access not per lane route feasibility",
    "single prime access checks miss a Hall obstruction in the joint weld",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def max_bipartite_matching(left: list[str], right: list[str], edges: dict[str, set[str]]) -> int:
    match_r: dict[str, str] = {}

    def aug(u: str, seen: set[str]) -> bool:
        for v in edges.get(u, set()):
            if v in seen:
                continue
            seen.add(v)
            if v not in match_r or aug(match_r[v], seen):
                match_r[v] = u
                return True
        return False

    return sum(1 for u in left if aug(u, set()))


def hall_defect(left: list[str], edges: dict[str, set[str]]) -> tuple[int, str]:
    best_defect = 0
    witness = "-"
    for r in range(1, len(left) + 1):
        for subset in combinations(left, r):
            union = set()
            for u in subset:
                union |= edges.get(u, set())
            defect = len(subset) - len(union)
            if defect > best_defect:
                best_defect = defect
                witness = "{" + ",".join(subset) + "}->{" + ",".join(sorted(union)) + "}"
    return best_defect, witness


def node_rows() -> list[str]:
    lines = ["STEP 6 NODE TEST: fire response access is a joint resource constraint"]
    lines.append(
        "Each incident may have a route and a hydrant/staging option alone, "
        "but simultaneous response can fail if multiple incidents require the "
        "same bottleneck resource."
    )
    cases = {
        "single_pass": {
            "incidents": ["A"],
            "resources": ["hydrant_1"],
            "edges": {"A": {"hydrant_1"}},
        },
        "two_incidents_one_hydrant": {
            "incidents": ["A", "B"],
            "resources": ["hydrant_1"],
            "edges": {"A": {"hydrant_1"}, "B": {"hydrant_1"}},
        },
        "two_incidents_two_hydrants": {
            "incidents": ["A", "B"],
            "resources": ["hydrant_1", "hydrant_2"],
            "edges": {"A": {"hydrant_1"}, "B": {"hydrant_2"}},
        },
        "three_incidents_two_staging_slots": {
            "incidents": ["A", "B", "C"],
            "resources": ["slot_1", "slot_2"],
            "edges": {"A": {"slot_1"}, "B": {"slot_1", "slot_2"}, "C": {"slot_2"}},
        },
    }
    lines.append("case individual_feasible matching_size demand hall_defect witness verdict")
    for name, c in cases.items():
        left = c["incidents"]
        right = c["resources"]
        edges = c["edges"]
        individual = all(len(edges.get(u, set())) > 0 for u in left)
        matching = max_bipartite_matching(left, right, edges)
        defect, witness = hall_defect(left, edges)
        verdict = "joint_fail" if matching < len(left) else "joint_pass"
        lines.append(
            f"{name:28s} {int(individual):d} {matching:d} {len(left):d} "
            f"{defect:d} {witness:20s} {verdict}"
        )
    lines.append(
        "NODE verdict: individual access is necessary but not sufficient; "
        "a Hall/staging obstruction is the minimal constraint."
    )
    return lines


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "Fire access matching formulas are graph diagnostics. Applied unchanged "
        "they are not HGT. The transfer uses them as a finite witness format "
        "for APEX-D: single sigma-lane access versus simultaneous joint weld "
        "access."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 16: USE A MINIMAL COUNTEREXAMPLE")
    lines.append(
        "Counterexample to the false APEX-D test: 'if every prime lane can be "
        "paired with an archimedean access slot individually, then the joint "
        "C5* weld is feasible.'"
    )
    cases = {
        "one_lane": {
            "lanes": ["p2"],
            "slots": ["A0"],
            "edges": {"p2": {"A0"}},
        },
        "two_lanes_shared_slot": {
            "lanes": ["p2", "p3"],
            "slots": ["A0"],
            "edges": {"p2": {"A0"}, "p3": {"A0"}},
        },
        "two_lanes_two_slots": {
            "lanes": ["p2", "p3"],
            "slots": ["A0", "A1"],
            "edges": {"p2": {"A0"}, "p3": {"A1"}},
        },
        "three_lanes_pairwise_ok_joint_fail": {
            "lanes": ["p2", "p3", "p5"],
            "slots": ["A0", "A1"],
            "edges": {"p2": {"A0"}, "p3": {"A0", "A1"}, "p5": {"A1"}},
        },
        "three_lanes_joint_ok": {
            "lanes": ["p2", "p3", "p5"],
            "slots": ["A0", "A1", "A2"],
            "edges": {"p2": {"A0"}, "p3": {"A1"}, "p5": {"A2"}},
        },
    }
    lines.append("case individual_access pairwise_subsets_pass matching_size demand hall_defect witness verdict")
    for name, c in cases.items():
        left = c["lanes"]
        edges = c["edges"]
        individual = all(len(edges.get(u, set())) > 0 for u in left)
        pairwise = True
        for subset in combinations(left, 2):
            sub_edges = {u: edges[u] for u in subset}
            if max_bipartite_matching(list(subset), list(set().union(*sub_edges.values())), sub_edges) < 2:
                pairwise = False
        if len(left) < 2:
            pairwise = True
        matching = max_bipartite_matching(left, c["slots"], edges)
        defect, witness = hall_defect(left, edges)
        verdict = "joint_weld_fail" if matching < len(left) else "joint_weld_pass"
        lines.append(
            f"{name:34s} {int(individual):d} {int(pairwise):d} {matching:d} {len(left):d} "
            f"{defect:d} {witness:24s} {verdict}"
        )
    lines.append(
        "\nAPEX-D provisional verdict: the minimal obstruction is not a single "
        "prime lane and not a single archimedean slot. It is the simultaneous "
        "Hall condition for joint access. This is only a finite witness format "
        "unless it predicts a real C5* observable."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: fire access constraints -> APEX-D C5/C5*")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 21/32 APEX-D C5/C5*")
    out.extend(node_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
