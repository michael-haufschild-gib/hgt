#!/usr/bin/env python3
"""
Attempt 7 NODE experiment.

NODE: static sparsity versus temporal sparsity of contacts.

Constraint tested:
  Temporal transport requires a nondecreasing-time path.  The aggregate graph
  can be connected with identical static edges while chronological ordering
  either permits or blocks propagation.
"""

from __future__ import annotations

from collections import deque


Contact = tuple[int, int, int]


def aggregate_edges(contacts: list[Contact]) -> set[tuple[int, int]]:
    return {tuple(sorted((u, v))) for _, u, v in contacts}


def temporal_reachable(contacts: list[Contact], source: int) -> dict[int, int]:
    earliest = {source: -1}
    changed = True
    while changed:
        changed = False
        for t, u, v in sorted(contacts):
            for a, b in [(u, v), (v, u)]:
                if a in earliest and earliest[a] <= t and (b not in earliest or t < earliest[b]):
                    earliest[b] = t
                    changed = True
    return earliest


def static_reachable(contacts: list[Contact], source: int) -> set[int]:
    adj: dict[int, set[int]] = {}
    for u, v in aggregate_edges(contacts):
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    seen = {source}
    q = deque([source])
    while q:
        u = q.popleft()
        for v in adj.get(u, set()):
            if v not in seen:
                seen.add(v)
                q.append(v)
    return seen


def summarize(label: str, contacts: list[Contact]) -> None:
    print(label)
    print(f"  contacts={sorted(contacts)}")
    print(f"  aggregate_edges={sorted(aggregate_edges(contacts))}")
    print(f"  static reachable from 0={sorted(static_reachable(contacts, 0))}")
    tr = temporal_reachable(contacts, 0)
    print(f"  temporal reachable from 0={sorted(tr)} with earliest={tr}")
    print()


def main() -> None:
    print("STATIC AGGREGATE CONNECTIVITY VS TEMPORAL TRANSPORT")
    print()
    forward = [(1, 0, 1), (2, 1, 2), (3, 2, 3)]
    reversed_order = [(1, 2, 3), (2, 1, 2), (3, 0, 1)]
    shuffled_block = [(1, 1, 2), (2, 0, 1), (3, 2, 3)]
    summarize("chronology permits 0->3", forward)
    summarize("same aggregate, chronology blocks 0->3", reversed_order)
    summarize("same aggregate, partial block", shuffled_block)


if __name__ == "__main__":
    main()
