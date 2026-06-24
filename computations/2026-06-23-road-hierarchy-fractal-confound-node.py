#!/usr/bin/env python3
"""Workflow W6: road hierarchy as fractal-morphology confound."""

from __future__ import annotations

import argparse
import math
import random
from dataclasses import dataclass

import mpmath as mp


Point = tuple[int, int]


@dataclass
class PatternResult:
    name: str
    points: set[Point]
    dimension: float
    r2: float
    occupancy_cv: float
    anisotropy: float


def linear_fit(xs: list[float], ys: list[float]) -> tuple[float, float, float]:
    n = len(xs)
    sx = sum(xs)
    sy = sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    denom = n * sxx - sx * sx
    if abs(denom) < 1e-30:
        return 0.0, 0.0, 0.0
    slope = (n * sxy - sx * sy) / denom
    intercept = (sy - slope * sx) / n
    ybar = sy / n
    ss_tot = sum((y - ybar) ** 2 for y in ys)
    ss_res = sum((y - (slope * x + intercept)) ** 2 for x, y in zip(xs, ys))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 1e-30 else 0.0
    return slope, intercept, r2


def draw_line(points: set[Point], x0: int, y0: int, x1: int, y1: int) -> None:
    if x0 == x1:
        ylo, yhi = sorted((y0, y1))
        for y in range(max(0, ylo), min(yhi, max(y0, y1)) + 1):
            points.add((x0, y))
    elif y0 == y1:
        xlo, xhi = sorted((x0, x1))
        for x in range(max(0, xlo), min(xhi, max(x0, x1)) + 1):
            points.add((x, y0))


def hierarchical_roads(size: int, depth: int = 6) -> set[Point]:
    """Deterministic H-tree-like road hierarchy.

    It is a designed hierarchy, not an organic growth process, but it has
    branching across scales and can look fractal under box-counting.
    """
    pts: set[Point] = set()

    def rec(cx: int, cy: int, length: int, level: int, horizontal: bool) -> None:
        if level <= 0 or length < 4:
            return
        half = length // 2
        if horizontal:
            draw_line(pts, cx - half, cy, cx + half, cy)
            for sx in (cx - half, cx + half):
                draw_line(pts, sx, cy - half // 2, sx, cy + half // 2)
                rec(sx, cy - half // 2, half, level - 1, not horizontal)
                rec(sx, cy + half // 2, half, level - 1, not horizontal)
        else:
            draw_line(pts, cx, cy - half, cx, cy + half)
            for sy in (cy - half, cy + half):
                draw_line(pts, cx - half // 2, sy, cx + half // 2, sy)
                rec(cx - half // 2, sy, half, level - 1, not horizontal)
                rec(cx + half // 2, sy, half, level - 1, not horizontal)

    rec(size // 2, size // 2, size // 2, depth, True)
    pts = {(x, y) for x, y in pts if 0 <= x < size and 0 <= y < size}
    return pts


def dendritic_growth(size: int, steps: int, seed: int) -> set[Point]:
    rng = random.Random(seed)
    center = size // 2
    pts: set[Point] = {(center, center)}
    frontier = [(center, center)]
    directions = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    while len(pts) < steps and frontier:
        x, y = rng.choice(frontier)
        dirs = directions[:]
        rng.shuffle(dirs)
        grew = False
        for dx, dy in dirs:
            nx, ny = x + dx, y + dy
            if 2 <= nx < size - 2 and 2 <= ny < size - 2 and (nx, ny) not in pts:
                # Prefer extensions that are near existing tips but not too dense.
                neigh = sum((nx + ax, ny + ay) in pts for ax, ay in directions)
                if neigh <= 2 and rng.random() < 0.78:
                    pts.add((nx, ny))
                    frontier.append((nx, ny))
                    grew = True
                    break
        if not grew and rng.random() < 0.2:
            frontier.remove((x, y))
    return pts


def random_points(size: int, count: int, seed: int) -> set[Point]:
    rng = random.Random(seed)
    pts: set[Point] = set()
    while len(pts) < count:
        pts.add((rng.randrange(size), rng.randrange(size)))
    return pts


def box_count(points: set[Point], size: int, box: int) -> tuple[int, list[int]]:
    counts: dict[tuple[int, int], int] = {}
    for x, y in points:
        key = (x // box, y // box)
        counts[key] = counts.get(key, 0) + 1
    return len(counts), list(counts.values())


def anisotropy(points: set[Point]) -> float:
    if len(points) < 2:
        return 0.0
    xs = [x for x, _ in points]
    ys = [y for _, y in points]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    cxx = sum((x - mx) ** 2 for x in xs) / len(xs)
    cyy = sum((y - my) ** 2 for y in ys) / len(ys)
    cxy = sum((x - mx) * (y - my) for x, y in points) / len(points)
    tr = cxx + cyy
    det = cxx * cyy - cxy * cxy
    disc = max(tr * tr - 4.0 * det, 0.0)
    l1 = 0.5 * (tr + math.sqrt(disc))
    l2 = 0.5 * (tr - math.sqrt(disc))
    return l1 / max(l2, 1e-12)


def analyze_pattern(name: str, points: set[Point], size: int, boxes: list[int]) -> PatternResult:
    xs = []
    ys = []
    all_cv = []
    for box in boxes:
        nbox, occupancies = box_count(points, size, box)
        xs.append(math.log(size / box))
        ys.append(math.log(max(nbox, 1)))
        if len(occupancies) > 1:
            m = sum(occupancies) / len(occupancies)
            var = sum((o - m) ** 2 for o in occupancies) / len(occupancies)
            all_cv.append(math.sqrt(var) / max(m, 1e-12))
    slope, _, r2 = linear_fit(xs, ys)
    return PatternResult(name, points, slope, r2, sum(all_cv) / max(len(all_cv), 1), anisotropy(points))


def node_simulation(size: int, seed: int) -> None:
    boxes = [2, 4, 8, 16, 32, 64]
    hier = hierarchical_roads(size)
    dend = dendritic_growth(size, steps=len(hier), seed=seed + 1)
    rand = random_points(size, len(hier), seed=seed + 2)
    print("NODE: road hierarchy can mimic fractal branching")
    print(f"size={size} occupied_target={len(hier)} boxes={boxes}")
    print("pattern occupied box_dimension box_r2 occupancy_cv anisotropy")
    for result in [
        analyze_pattern("designed_hierarchy", hier, size, boxes),
        analyze_pattern("stochastic_growth", dend, size, boxes),
        analyze_pattern("random_occupancy", rand, size, boxes),
    ]:
        print(
            f"{result.name:18s} {len(result.points):8d} {result.dimension:13.5f} "
            f"{result.r2:6.4f} {result.occupancy_cv:12.5f} {result.anisotropy:10.5f}"
        )


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def first_primes(n: int) -> list[int]:
    primes: list[int] = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return primes


def gamma_part(s: complex) -> complex:
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s: complex, h: float = 2e-4) -> complex:
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s: complex, primes: list[int]) -> complex:
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def phase_defect(g: complex, p: complex) -> float:
    return math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)


def threshold_points(values: list[float], width: int, height: int, q: float) -> set[Point]:
    cutoff = sorted(values)[int(q * (len(values) - 1))]
    pts = set()
    for idx, value in enumerate(values):
        if value >= cutoff:
            pts.add((idx % width, idx // width))
    return pts


def ht_transfer(width: int, height: int, prime_count: int, seed: int) -> None:
    node_sig = "road hierarchy mimics fractal branching without self organization"
    candidates = [
        "prime hierarchy mimics fractal phase branching without native organization",
        "threshold hierarchy mimics fractal zero-shadow branching",
        "finite-euler hierarchy mimics fractal seam morphology",
    ]
    print("\nSTEP8 Levenshtein transfer candidates")
    best: tuple[int, int, str] | None = None
    for idx, cand in enumerate(candidates, 1):
        dist = levenshtein(node_sig, cand)
        ratio = dist / max(len(node_sig), len(cand))
        print(f"{idx} distance={dist} ratio={ratio:.4f} {cand}")
        if best is None or dist < best[0]:
            best = (dist, idx, cand)
    assert best is not None
    print(f"selected={best[1]} {best[2]}")

    primes = first_primes(prime_count)
    rng = random.Random(seed)
    boxes = [2, 4, 8, 16, 32]
    print("\nSTEP9 method=1 split subclaims: HT morphology hierarchy confound")
    print("kind sigma occupied box_dimension box_r2 occupancy_cv anisotropy")
    for sigma in [0.3, 0.5, 1.2]:
        vals: dict[str, list[float]] = {"true": [], "finite": [], "random": []}
        for y in range(height):
            for x in range(width):
                t = 80.0 + 0.12 * y + 0.015 * x
                s = complex(float(sigma), t)
                g = gamma_part(s)
                z = dlog_zeta(s)
                f = dlog_finite_euler(s, primes)
                theta = rng.uniform(-math.pi, math.pi)
                r = abs(z) * complex(math.cos(theta), math.sin(theta))
                vals["true"].append(phase_defect(g, z))
                vals["finite"].append(phase_defect(g, f))
                vals["random"].append(phase_defect(g, r))
        for kind, series in vals.items():
            pts = threshold_points(series, width, height, 0.82)
            result = analyze_pattern(kind, pts, width, boxes)
            print(
                f"{kind:6s} {sigma:.1f} {len(pts):8d} {result.dimension:13.5f} "
                f"{result.r2:6.4f} {result.occupancy_cv:12.5f} {result.anisotropy:10.5f}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=256)
    parser.add_argument("--width", type=int, default=192)
    parser.add_argument("--height", type=int, default=96)
    parser.add_argument("--prime-count", type=int, default=70)
    parser.add_argument("--seed", type=int, default=1096590896978984582 % (2**32))
    args = parser.parse_args()
    node_simulation(args.size, args.seed)
    ht_transfer(args.width, args.height, args.prime_count, args.seed + 11)


if __name__ == "__main__":
    main()
