#!/usr/bin/env python3
"""
Attempt 8 NODE experiment.

NODE: global shape coordinates without self-intersections and ambiguities.

Constraint tested:
  A smooth local parameterization of a shape family is not enough.  The chart is
  valid for embedded global shapes only where the sampled curve has no
  self-intersections and no degenerate identifications.
"""

from __future__ import annotations

import math

import numpy as np


Point = tuple[float, float]


def polar_curve(a: float, n: int = 400) -> list[Point]:
    pts: list[Point] = []
    for j in range(n):
        theta = 2 * math.pi * j / n
        r = 1.0 + a * math.cos(2 * theta)
        pts.append((r * math.cos(theta), r * math.sin(theta)))
    return pts


def orient(a: Point, b: Point, c: Point) -> float:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def segments_intersect(a: Point, b: Point, c: Point, d: Point) -> bool:
    o1 = orient(a, b, c)
    o2 = orient(a, b, d)
    o3 = orient(c, d, a)
    o4 = orient(c, d, b)
    return (o1 * o2 < -1e-12) and (o3 * o4 < -1e-12)


def self_intersections(pts: list[Point]) -> int:
    n = len(pts)
    count = 0
    for i in range(n):
        a, b = pts[i], pts[(i + 1) % n]
        for j in range(i + 2, n):
            if (j + 1) % n == i:
                continue
            c, d = pts[j], pts[(j + 1) % n]
            if segments_intersect(a, b, c, d):
                count += 1
    return count


def min_radius(a: float, n: int = 400) -> float:
    return min(1.0 + a * math.cos(2 * 2 * math.pi * j / n) for j in range(n))


def descriptor(pts: list[Point]) -> tuple[float, float]:
    arr = np.array(pts)
    radius = np.sqrt(np.sum(arr * arr, axis=1))
    return float(np.mean(radius)), float(np.std(radius))


def main() -> None:
    print("LOCAL SHAPE PARAMETER VS GLOBAL EMBEDDING VALIDITY")
    print("family: r(theta)=1+a*cos(2theta)")
    print()
    for a in [0.0, 0.5, 0.9, 1.0, 1.1, 1.5]:
        pts = polar_curve(a)
        inter = self_intersections(pts)
        mean_r, std_r = descriptor(pts)
        print(
            f"a={a:3.1f}: min_r={min_radius(a):+.3f}, "
            f"self_intersections={inter}, "
            f"mean_radius={mean_r:.3f}, radius_std={std_r:.3f}"
        )
    print()
    print("boundary: min_r crosses 0 at a=1; beyond it the local polar chart folds through the origin.")


if __name__ == "__main__":
    main()
