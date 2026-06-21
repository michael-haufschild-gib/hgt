#!/usr/bin/env python3
from itertools import combinations


def d2(points, rect):
    xmin, xmax, ymin, ymax = rect
    total = 0.0
    for beta, gamma, mult in points:
        if xmin < beta < xmax and ymin < gamma < ymax:
            total += mult * (beta - 0.5) ** 2
    return total


def find_detector(points, target, grid):
    tx, ty, _ = target
    xs = sorted(grid)
    ys = sorted(grid)
    for xmin, xmax in combinations(xs, 2):
        if not (xmin < tx < xmax):
            continue
        for ymin, ymax in combinations(ys, 2):
            if not (ymin < ty < ymax):
                continue
            rect = (xmin, xmax, ymin, ymax)
            val = d2(points, rect)
            if val > 0:
                return rect, val
    return None, 0.0


def main():
    print("ResearchNode: prove all-window D2(R)=0 or find exact obstruction")
    print("NODE constraint: topology/motifs matter; local structure must be separated, not averaged.")
    print()
    seam_only = [(0.5, 1.0, 1), (0.5, 2.0, 1)]
    off_seam = [(0.5, 1.0, 1), (0.57, 2.0, 1)]
    grid = [i / 10 for i in range(0, 11)] + [1.5, 2.5]
    print("Extreme case A: seam-only divisor")
    print(f"  D2 on broad rect = {d2(seam_only, (0.0, 1.0, 0.0, 3.0)):.6f}")
    print("Extreme case B: one isolated off-seam atom beta=0.57")
    rect, val = find_detector(off_seam, off_seam[1], grid)
    print(f"  detector rect = {rect}, D2 = {val:.6f}")
    print("Extreme case C: boundary issue")
    boundary_rect = (0.5, 0.57, 1.5, 2.5)
    print(f"  if atom lies on open boundary, D2 = {d2(off_seam, boundary_rect):.6f}")
    repaired_rect = (0.56, 0.58, 1.5, 2.5)
    print(f"  smaller rational isolating rect D2 = {d2(off_seam, repaired_rect):.6f}")
    print()
    print("Lemma:")
    print("  For a discrete zero set, all-window D2=0 is equivalent to D2=0 on")
    print("  a countable basis of rational rectangles whose boundaries avoid zeros.")
    print("  Any off-seam zero has positive atomic D2 mass and can be isolated by")
    print("  one such rectangle; seam-only atoms contribute zero.")


if __name__ == "__main__":
    main()
