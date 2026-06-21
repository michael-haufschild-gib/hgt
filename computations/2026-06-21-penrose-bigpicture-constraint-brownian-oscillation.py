#!/usr/bin/env python3
import math
import random


def brownian_path(n, seed=1729):
    rng = random.Random(seed)
    dt = 1.0 / n
    x = 0.0
    vals = [x]
    for _ in range(n):
        x += rng.gauss(0.0, math.sqrt(dt))
        vals.append(x)
    return vals


def smooth_path(n):
    return [math.sin(2 * math.pi * k / n) for k in range(n + 1)]


def stats(vals):
    n = len(vals) - 1
    dt = 1.0 / n
    increments = [vals[i + 1] - vals[i] for i in range(n)]
    total_variation = sum(abs(dx) for dx in increments)
    quadratic_variation = sum(dx * dx for dx in increments)
    max_slope = max(abs(dx) / dt for dx in increments)
    rms_slope = math.sqrt(sum((dx / dt) ** 2 for dx in increments) / n)
    return total_variation, quadratic_variation, max_slope, rms_slope


def main():
    print("NODE test: local oscillation replaces tangent")
    print("Compare Brownian sample path with a smooth sine path on [0,1].")
    print()
    print("n     path       total_var      quad_var      max_slope      rms_slope")
    for n in [256, 1024, 4096, 16384]:
        for label, maker in [("brownian", brownian_path), ("smooth", smooth_path)]:
            tv, qv, max_slope, rms_slope = stats(maker(n))
            print(f"{n:<5d} {label:<9s} {tv:13.6f} {qv:13.6f} {max_slope:14.6f} {rms_slope:14.6f}")
        print()


if __name__ == "__main__":
    main()
