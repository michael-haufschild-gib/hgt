#!/usr/bin/env python3
import numpy as np


def participation(weights):
    w = np.abs(np.asarray(weights, dtype=float))
    if np.all(w == 0):
        return 0.0
    return float((w.sum() ** 2) / np.sum(w * w))


def main():
    print("NODE test: community boundaries can trap oscillatory energy")
    print("Two weakly coupled communities; a localized mode can be mistaken for a global mode.")
    print()
    mode = np.array([1, -1, 0, 0, 0, 0, 0, 0, 0, 0], dtype=float)
    left_energy = float(np.sum(mode[:5] ** 2))
    right_energy = float(np.sum(mode[5:] ** 2))
    print(f"localized mode energy: left={left_energy:.3f}, right={right_energy:.3f}, participation={participation(mode):.3f}")
    print()
    print("ResearchNode mutation: forward contour moments and local pocket dominance")
    zeros = np.array([1.0, 2.0, 3.0, 10.0])
    print("zeros/proxy positions:", [float(z) for z in zeros])
    print("k | M_k global | largest contribution share | participation")
    print("--|------------|----------------------------|--------------")
    for k in [1, 2, 3, 4, 5]:
        contrib = zeros ** k
        total = float(np.sum(contrib))
        share = float(np.max(np.abs(contrib)) / np.sum(np.abs(contrib)))
        pr = participation(contrib)
        print(f"{k:1d} | {total:10.3f} | {share:26.6f} | {pr:12.6f}")
    print()
    print("Step-12 follow-up: partition additivity")
    for k in [2, 4]:
        local = float(np.sum(zeros[:3] ** k))
        pocket = float(zeros[3] ** k)
        print(f"k={k}: local-window={local:.3f}, pocket-window={pocket:.3f}, sum={local+pocket:.3f}")
    print()
    print("Finding:")
    print("  Forward contour moments are exact local sums, but their scalar values can be")
    print("  dominated by a localized pocket. A contour-moment claim needs a localization")
    print("  passport: window partition, boundary guard, contribution shares, and additivity")
    print("  checks before local moments are interpreted as global divisor information.")


if __name__ == "__main__":
    main()
