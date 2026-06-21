#!/usr/bin/env python3
import math


alpha = (math.sqrt(5) - 1) / 2


def rot(x):
    return (x + alpha) % 1.0


def rot_modified(x):
    if x == 0.0:
        return 0.0
    return rot(x)


def orbit(f, x0, n):
    x = x0
    out = []
    for _ in range(n):
        out.append(x)
        x = f(x)
    return out


def occupancy(points, bins):
    counts = [0] * bins
    for x in points:
        counts[min(int(x * bins), bins - 1)] += 1
    return counts


def main():
    print("NODE test: null-set modification of an irrational rotation")
    print("T(x)=x+alpha mod 1; T'(0)=0 and T'(x)=T(x) otherwise")
    print("The maps differ only at one point, but the orbit of that point changes.")
    print()

    n = 2000
    bins = 20
    for x0 in [0.0, 0.12345]:
        o1 = orbit(rot, x0, n)
        o2 = orbit(rot_modified, x0, n)
        c1 = occupancy(o1, bins)
        c2 = occupancy(o2, bins)
        l1 = sum(abs(a - b) for a, b in zip(c1, c2)) / n
        print(f"x0={x0:.5f}")
        print(f"  first five original={o1[:5]}")
        print(f"  first five modified={o2[:5]}")
        print(f"  bin-count L1 difference per sample={l1:.6f}")
        print(f"  occupied_bins original={sum(c>0 for c in c1)} modified={sum(c>0 for c in c2)}")
        print()


if __name__ == "__main__":
    main()
