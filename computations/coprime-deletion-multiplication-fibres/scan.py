#!/usr/bin/env python3
"""Exact multicore scan of coprime deletion-grid multiplication fibres.

This experiment is conjecture discovery only.  Lean proofs do not depend on its output.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def deletion_weight(base: int, n: int) -> int:
    return 1 - base if n % base == 0 else 1


def analyze(pair: tuple[int, int]) -> dict[str, int | float | bool]:
    p, q = pair
    fibres: dict[int, int] = defaultdict(int)
    fibre_sizes: dict[int, int] = defaultdict(int)
    pre_square = 0
    pre_l1 = 0
    for m in range(1, p + 1):
        wm = deletion_weight(p, m)
        for n in range(1, q + 1):
            w = wm * deletion_weight(q, n)
            k = m * n
            fibres[k] += w
            fibre_sizes[k] += 1
            pre_square += w * w
            pre_l1 += abs(w)

    post_square = sum(value * value for value in fibres.values())
    post_l1 = sum(abs(value) for value in fibres.values())
    defect = pre_square - post_square
    collision_excess = p * q - len(fibres)
    cancelled_l1 = pre_l1 - post_l1
    return {
        "p": p,
        "q": q,
        "both_prime": is_prime(p) and is_prime(q),
        "pre_square": pre_square,
        "post_square": post_square,
        "defect": defect,
        "defect_over_pre": defect / pre_square,
        "pre_l1": pre_l1,
        "post_l1": post_l1,
        "cancelled_l1": cancelled_l1,
        "collision_excess": collision_excess,
        "max_fibre_size": max(fibre_sizes.values()),
        "zero_fibres": sum(value == 0 for value in fibres.values()),
    }


def summarize(rows: list[dict[str, int | float | bool]]) -> dict[str, object]:
    ordered = sorted(rows, key=lambda row: (int(row["p"]), int(row["q"])))
    by_defect = sorted(ordered, key=lambda row: int(row["defect"]))
    negative = [row for row in ordered if int(row["defect"]) < 0]
    zero = [row for row in ordered if int(row["defect"]) == 0]
    positive = [row for row in ordered if int(row["defect"]) > 0]
    primes = [row for row in ordered if bool(row["both_prime"])]
    prime_negative = [row for row in primes if int(row["defect"]) < 0]
    prime_zero = [row for row in primes if int(row["defect"]) == 0]
    ratios = [float(row["defect_over_pre"]) for row in ordered]
    return {
        "case_count": len(ordered),
        "negative_count": len(negative),
        "zero_count": len(zero),
        "positive_count": len(positive),
        "prime_case_count": len(primes),
        "prime_negative_count": len(prime_negative),
        "prime_zero_count": len(prime_zero),
        "minimum_defect_cases": by_defect[:10],
        "maximum_defect_cases": by_defect[-10:],
        "negative_examples": negative[:20],
        "zero_examples": zero[:20],
        "prime_negative_examples": prime_negative[:20],
        "prime_zero_examples": prime_zero[:20],
        "minimum_defect_ratio": min(ratios),
        "maximum_defect_ratio": max(ratios),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--coprime-limit", type=int, default=80)
    parser.add_argument("--prime-limit", type=int, default=300)
    parser.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    pairs = {
        (p, q)
        for p in range(2, args.coprime_limit + 1)
        for q in range(p + 1, args.coprime_limit + 1)
        if math.gcd(p, q) == 1
    }
    primes = [p for p in range(2, args.prime_limit + 1) if is_prime(p)]
    pairs.update((p, q) for i, p in enumerate(primes) for q in primes[i + 1 :])
    ordered_pairs = sorted(pairs)

    args.out.mkdir(parents=True, exist_ok=True)
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(analyze, ordered_pairs, chunksize=8))
    rows.sort(key=lambda row: (int(row["p"]), int(row["q"])))

    fields = list(rows[0].keys())
    with (args.out / "cases.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)

    payload = {
        "parameters": {
            "coprime_limit": args.coprime_limit,
            "prime_limit": args.prime_limit,
            "workers": args.workers,
            "exact_integer_arithmetic": True,
        },
        "summary": summarize(rows),
    }
    with (args.out / "results.json").open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    print(json.dumps(payload["summary"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
