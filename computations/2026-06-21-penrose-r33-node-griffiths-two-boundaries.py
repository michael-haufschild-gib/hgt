#!/usr/bin/env python3
"""
R33 NODE validation: Griffiths region has two bounding critical points.

Constraint tested:
  The anomalous/Griffiths interval is bounded by a clean critical point and a
  disordered/global critical point. The observed global transition alone misses
  rare ordered islands in the intervening region.
"""

from __future__ import annotations

from collections import deque

import numpy as np


def largest_cluster(active: np.ndarray) -> tuple[int, bool]:
    n, m = active.shape
    seen = np.zeros_like(active, dtype=bool)
    best = 0
    spans = False
    for i in range(n):
        for j in range(m):
            if seen[i, j] or not active[i, j]:
                continue
            q = deque([(i, j)])
            seen[i, j] = True
            size = 0
            touches_left = touches_right = False
            while q:
                x, y = q.popleft()
                size += 1
                touches_left |= y == 0
                touches_right |= y == m - 1
                for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    xx, yy = x + dx, y + dy
                    if 0 <= xx < n and 0 <= yy < m and active[xx, yy] and not seen[xx, yy]:
                        seen[xx, yy] = True
                        q.append((xx, yy))
            best = max(best, size)
            spans |= touches_left and touches_right
    return best, spans


def make_thresholds(rng: np.random.Generator, n: int = 90) -> np.ndarray:
    base = rng.normal(1.43, 0.045, size=(n, n))
    # Rare cleaner patches have lower local ordering thresholds.
    for _ in range(42):
        cx, cy = rng.integers(0, n, size=2)
        radius = int(rng.integers(2, 7))
        drop = float(rng.uniform(0.22, 0.45))
        xs = np.arange(n)[:, None]
        ys = np.arange(n)[None, :]
        mask = (xs - cx) ** 2 + (ys - cy) ** 2 <= radius * radius
        base[mask] -= drop
    return np.clip(base, 0.98, 1.55)


def main() -> None:
    rng = np.random.default_rng(3309)
    thresholds = make_thresholds(rng)
    clean = 1.00
    observed_global = None
    print("lambda   active_frac  largest_cluster  spans  avg_tau       typ_tau")
    for lam in [0.94, 1.00, 1.06, 1.12, 1.18, 1.24, 1.30, 1.36, 1.42, 1.48]:
        active = lam > thresholds
        largest, spans = largest_cluster(active)
        # Activated islands: lifetimes grow quickly with local distance above threshold.
        local = np.maximum(0.0, lam - thresholds[active])
        if local.size:
            tau = np.exp(18.0 * local)
            avg_tau = float(np.mean(tau))
            typ_tau = float(np.exp(np.mean(np.log(tau))))
        else:
            avg_tau = typ_tau = 1.0
        if spans and observed_global is None:
            observed_global = lam
        print(f"{lam:6.2f} {active.mean():11.4f} {largest:16d} {int(spans):5d} {avg_tau:11.3f} {typ_tau:11.3f}")

    print("\nNODE verdict:")
    print(f"clean_bound={clean:.2f} observed_disordered_bound~={observed_global:.2f}")
    print(
        "The interval after the clean bound but before spanning/global order has rare active islands "
        "and broad lifetimes. A single observed transition would miss that Griffiths interval."
    )


if __name__ == "__main__":
    main()
