#!/usr/bin/env python3
"""
Attempt 7 transfer experiment.

ResearchNode: Transport, not amplitude.
NODE constraint: temporal order changes transport reachability even when the
static aggregate graph is identical.

Transfer:
  Use elementary noncommuting connection increments.  The aggregate amplitude
  K=sum A_i is identical for each schedule, but the path-ordered holonomy
  product depends on order and can create or block downstream transport.
"""

from __future__ import annotations

import numpy as np


def edge_increment(src: int, dst: int, eps: float, n: int = 4) -> np.ndarray:
    A = np.eye(n)
    A[dst, src] = eps
    return A


def generator(src: int, dst: int, eps: float, n: int = 4) -> np.ndarray:
    A = np.zeros((n, n))
    A[dst, src] = eps
    return A


def ordered_product(edges: list[tuple[int, int]], eps: float) -> np.ndarray:
    H = np.eye(4)
    for src, dst in edges:
        H = edge_increment(src, dst, eps) @ H
    return H


def aggregate_generator(edges: list[tuple[int, int]], eps: float) -> np.ndarray:
    K = np.zeros((4, 4))
    for src, dst in edges:
        K += generator(src, dst, eps)
    return K


def summarize(label: str, edges: list[tuple[int, int]], eps: float) -> tuple[np.ndarray, np.ndarray]:
    H = ordered_product(edges, eps)
    K = aggregate_generator(edges, eps)
    e0 = np.array([1.0, 0.0, 0.0, 0.0])
    transported = H @ e0
    print(label)
    print(f"  ordered edges={edges}")
    print(f"  aggregate nonzeros={list(zip(*np.nonzero(K)))}")
    print(f"  aggregate Frobenius norm={np.linalg.norm(K):.6f}, trace={np.trace(K):.6f}")
    print(f"  holonomy H[3,0]={H[3,0]:+.6f}; transported e0={transported}")
    print()
    return H, K


def main() -> None:
    print("AGGREGATE AMPLITUDE VS ORDERED HOLONOMY")
    print("same connection increments; only order changes")
    print()
    eps = 0.5
    forward = [(0, 1), (1, 2), (2, 3)]
    reverse = [(2, 3), (1, 2), (0, 1)]
    partial = [(1, 2), (0, 1), (2, 3)]
    Hf, Kf = summarize("order permits downstream transport", forward, eps)
    Hr, Kr = summarize("same aggregate, order blocks downstream transport", reverse, eps)
    Hp, Kp = summarize("same aggregate, partial order block", partial, eps)
    print("aggregate comparisons:")
    print(f"  K_forward == K_reverse: {np.allclose(Kf, Kr)}")
    print(f"  K_forward == K_partial: {np.allclose(Kf, Kp)}")
    print(f"  ||H_forward-H_reverse||_F={np.linalg.norm(Hf-Hr):.6f}")
    print(f"  ||H_forward-H_partial||_F={np.linalg.norm(Hf-Hp):.6f}")
    print()
    print("method #1 subclaims:")
    print(f"  A aggregate data identical: {np.allclose(Kf, Kr) and np.allclose(Kf, Kp)}")
    print(f"  B ordered holonomy differs: {not np.allclose(Hf, Hr) and not np.allclose(Hf, Hp)}")
    print(f"  C downstream 0->3 transport differs: {Hf[3,0] != Hr[3,0] and Hf[3,0] != Hp[3,0]}")


if __name__ == "__main__":
    main()
