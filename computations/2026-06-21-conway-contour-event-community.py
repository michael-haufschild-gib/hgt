#!/usr/bin/env python3
"""Workflow pass: event count is not event community structure."""

from __future__ import annotations

import importlib.util
import math
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-poincare-contour-root-gate.py")
spec = importlib.util.spec_from_file_location("root_gate", BASE)
root_gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(root_gate)


def gini(x: np.ndarray) -> float:
    y = np.sort(np.asarray(x, dtype=float))
    if y.sum() == 0:
        return 0.0
    n = len(y)
    return float((2 * np.arange(1, n + 1) @ y) / (n * y.sum()) - (n + 1) / n)


def node_preferential_attachment(seed: int = 20260621) -> None:
    rng = np.random.default_rng(seed)

    def make_graph(blocked: bool, n: int = 260, m: int = 2) -> tuple[np.ndarray, np.ndarray]:
        adj = np.zeros((n, n), dtype=bool)
        labels = np.arange(n) % 2
        # Seed each block with a triangle.
        for block in [0, 1]:
            nodes = np.where(labels[:6] == block)[0]
            for i in nodes:
                for j in nodes:
                    if i < j:
                        adj[i, j] = adj[j, i] = True
        deg = adj.sum(axis=1).astype(float) + 1.0
        for v in range(6, n):
            candidates = np.arange(v)
            weights = deg[:v].copy()
            if blocked:
                weights[labels[:v] != labels[v]] *= 0.08
            weights /= weights.sum()
            targets = rng.choice(candidates, size=m, replace=False, p=weights)
            for t in targets:
                adj[v, t] = adj[t, v] = True
            deg = adj.sum(axis=1).astype(float) + 1.0
        return adj, labels

    def modularity(adj: np.ndarray, labels: np.ndarray) -> float:
        deg = adj.sum(axis=1)
        two_m = deg.sum()
        q = 0.0
        for i in range(len(labels)):
            for j in range(len(labels)):
                if labels[i] == labels[j]:
                    q += adj[i, j] - deg[i] * deg[j] / two_m
        return float(q / two_m)

    print("NODE: preferential attachment alone does not explain community structure")
    print("case degree_gini top5_degree_share planted_modularity cross_block_edge_frac")
    for name, blocked in [("plain_PA", False), ("block_PA", True)]:
        adj, labels = make_graph(blocked)
        deg = adj.sum(axis=1)
        top5 = np.sort(deg)[-5:].sum() / deg.sum()
        edges = np.argwhere(np.triu(adj, 1))
        cross = np.mean(labels[edges[:, 0]] != labels[edges[:, 1]])
        print(f"{name:8s} {gini(deg):.3f} {top5:.3f} {modularity(adj, labels):.3f} {cross:.3f}")


def contour_events(rect: tuple[float, float, float, float], n_edge: int = 160, k_events: int = 28) -> dict[str, object]:
    pts = root_gate.boundary(rect, n_edge)
    vals = [complex(root_gate.xi(z)) for z in pts]
    jumps = []
    sides = []
    for idx, (v0, v1) in enumerate(zip(vals, vals[1:])):
        phase = abs(root_gate.principal_angle(math.atan2(v1.imag, v1.real) - math.atan2(v0.imag, v0.real)))
        logjump = abs(math.log(abs(v1) + 1e-300) - math.log(abs(v0) + 1e-300))
        jumps.append(phase + 0.35 * logjump)
        sides.append(min(3, idx // n_edge))
    jumps_arr = np.asarray(jumps)
    order = np.argsort(jumps_arr)[::-1][:k_events]
    event_mask = np.zeros(len(jumps_arr), dtype=bool)
    event_mask[order] = True
    side_counts = np.bincount(np.asarray(sides)[event_mask], minlength=4).astype(float)
    p = side_counts / side_counts.sum()
    entropy = float(-np.sum([q * math.log(q) for q in p if q > 0]) / math.log(4))
    clusters = 0
    longest = 0
    run = 0
    doubled = np.r_[event_mask, event_mask]
    # Break cyclic runs at a non-event if possible.
    if np.any(~event_mask):
        start = int(np.where(~event_mask)[0][0]) + 1
        seq = [event_mask[(start + i) % len(event_mask)] for i in range(len(event_mask))]
    else:
        seq = event_mask.tolist()
    prev = False
    for flag in seq:
        if flag:
            run += 1
            if not prev:
                clusters += 1
            longest = max(longest, run)
        else:
            run = 0
        prev = bool(flag)
    wind, max_jump, min_abs, _ = root_gate.winding_from_points(pts)
    return {
        "winding": wind,
        "max_jump": max_jump,
        "min_abs": min_abs,
        "side_counts": side_counts.astype(int).tolist(),
        "side_entropy": entropy,
        "largest_side_share": float(p.max()),
        "clusters": clusters,
        "longest_cluster": longest,
    }


def transfer_contours() -> None:
    print()
    print("TRANSFER: ResearchNode #21 event-certified contour certificate")
    print("method #19 fake proof: enough boundary events certify a contour")
    zero1 = 14.134725141734693790457251983562
    rects = {
        "contains_zero": (0.45, 0.55, zero1 - 0.11, zero1 + 0.11),
        "near_right_nozero": (0.5005, 0.62, zero1 - 0.11, zero1 + 0.11),
        "far_right_nozero": (0.62, 0.82, zero1 - 0.11, zero1 + 0.11),
        "wide_contains": (0.2, 0.8, zero1 - 0.11, zero1 + 0.11),
    }
    print("rect k_events winding side_counts side_entropy largest_side_share clusters longest_cluster max_jump min_abs_xi")
    for name, rect in rects.items():
        row = contour_events(rect)
        print(
            f"{name:17s} 28 {row['winding']:+.3f} {row['side_counts']} "
            f"{row['side_entropy']:.3f} {row['largest_side_share']:.3f} "
            f"{row['clusters']:02d} {row['longest_cluster']:02d} {row['max_jump']:.3f} {row['min_abs']:.2e}"
        )


def main() -> None:
    node_preferential_attachment()
    transfer_contours()


if __name__ == "__main__":
    main()
