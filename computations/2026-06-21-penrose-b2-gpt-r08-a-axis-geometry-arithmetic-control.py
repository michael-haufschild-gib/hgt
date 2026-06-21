#!/usr/bin/env python3
import itertools
import math
import random


def mean(xs):
    return sum(xs) / len(xs)


def variance(xs):
    mu = mean(xs)
    return sum((x - mu) ** 2 for x in xs) / len(xs)


def normalize_to(xs, target_mean, target_var):
    mu = mean(xs)
    sd = math.sqrt(variance(xs))
    target_sd = math.sqrt(target_var)
    return [(x - mu) / sd * target_sd + target_mean for x in xs]


def best_integer_relation(xs, H):
    best = (float("inf"), None)
    for coeffs in itertools.product(range(-H, H + 1), repeat=len(xs)):
        if all(c == 0 for c in coeffs):
            continue
        val = abs(sum(c * x for c, x in zip(coeffs, xs)))
        norm = sum(abs(c) for c in coeffs)
        if norm and val < best[0]:
            best = (val, coeffs)
    return best


def main():
    print("NODE test: aggregate WIP inventory hides process variability")
    print("ResearchNode mutation: A-axis separation needs arithmetic controls, not geometry aggregates")
    print()
    A = [1.0, 2.0, 3.0, 4.0]
    random.seed(612021)
    candidates = []
    for _ in range(500):
        raw = [random.uniform(-3, 5) for _ in range(4)]
        trial = normalize_to(raw, mean(A), variance(A))
        residual, coeffs = best_integer_relation(trial, H=3)
        candidates.append((residual, coeffs, trial))
    _, _, B = max(candidates, key=lambda row: row[0])
    for label, xs in [("relation-rich control A", A), ("same-geometry control B", B)]:
        residual, coeffs = best_integer_relation(xs, H=3)
        print(f"{label}:")
        print(f"  values={[round(x, 12) for x in xs]}")
        print(f"  mean={mean(xs):.12f}, variance={variance(xs):.12f}")
        print(f"  best height<=3 relation residual={residual:.3e}, coeffs={coeffs}")
    print()
    print("Finding:")
    print("  Two candidate divisor samples can share aggregate geometry (mean/variance/count) while")
    print("  their integer-relation profile differs sharply. A-axis evidence must include relation")
    print("  searches or same-geometry/different-arithmetic controls; geometry summaries cannot be")
    print("  promoted to value-arithmetic evidence.")


if __name__ == "__main__":
    main()
