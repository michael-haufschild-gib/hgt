#!/usr/bin/env python3
"""Multicore sign scan of 4*sinh(h/2)-sum Lambda(k)/sqrt(k).

The minimum occurs immediately after a prime-power jump, so segmented workers need only return
their local minimum and total mass. Computational evidence only; no result is a Lean premise.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import os
import time
from pathlib import Path


BASE_PRIMES: list[int] = []


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        sieve[0] = 0
    if limit >= 1:
        sieve[1] = 0
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
    return [index for index, flag in enumerate(sieve) if flag]


def initialize_worker(base_primes: list[int]) -> None:
    global BASE_PRIMES
    BASE_PRIMES = base_primes


def add_kahan(total: float, correction: float, value: float) -> tuple[float, float]:
    adjusted = value - correction
    updated = total + adjusted
    correction = (updated - total) - adjusted
    return updated, correction


def scan_segment(task: tuple[int, int, int]) -> dict[str, int | float]:
    index, low, high = task
    length = high - low + 1
    sieve = bytearray(b"\x01") * length
    if low <= 1:
        for value in range(low, min(high, 1) + 1):
            sieve[value - low] = 0
    for p in BASE_PRIMES:
        square = p * p
        if square > high:
            break
        start = max(square, ((low + p - 1) // p) * p)
        sieve[start - low : length : p] = b"\x00" * (((high - start) // p) + 1)

    events: list[tuple[int, float]] = []
    position = sieve.find(1)
    prime_count = 0
    while position >= 0:
        prime = low + position
        events.append((prime, math.log(prime) / math.sqrt(prime)))
        prime_count += 1
        position = sieve.find(1, position + 1)
    power_count = 0
    for p in BASE_PRIMES:
        power = p * p
        if power > high:
            break
        log_p = math.log(p)
        while power <= high:
            if power >= low:
                events.append((power, log_p / math.sqrt(power)))
                power_count += 1
            if power > high // p:
                break
            power *= p
    events.sort(key=lambda event: event[0])

    local_mass = 0.0
    correction = 0.0
    local_min = math.inf
    local_argmin = low
    local_mass_at_min = 0.0
    for value, mass in events:
        local_mass, correction = add_kahan(local_mass, correction, mass)
        root = math.sqrt(value)
        polar = 2 * (root - 1 / root)
        score = polar - local_mass
        if score < local_min:
            local_min = score
            local_argmin = value
            local_mass_at_min = local_mass
    if not events:
        local_min = 2 * (math.sqrt(low) - 1 / math.sqrt(low))
    return {
        "index": index,
        "low": low,
        "high": high,
        "prime_count": prime_count,
        "higher_power_count": power_count,
        "event_count": len(events),
        "total_mass": local_mass,
        "local_min_before_prior_mass": local_min,
        "local_argmin": local_argmin,
        "local_mass_at_min": local_mass_at_min,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, required=True)
    parser.add_argument("--segment-size", type=int, default=2_000_000)
    parser.add_argument("--workers", type=int, default=min(96, os.cpu_count() or 1))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.limit < 2:
        raise ValueError("limit must be at least 2")
    started = time.time()
    base_primes = primes_up_to(math.isqrt(args.limit))
    tasks = []
    index = 0
    for low in range(2, args.limit + 1, args.segment_size):
        high = min(args.limit, low + args.segment_size - 1)
        tasks.append((index, low, high))
        index += 1
    records: list[dict[str, int | float]] = []
    with concurrent.futures.ProcessPoolExecutor(
        max_workers=args.workers,
        initializer=initialize_worker,
        initargs=(base_primes,),
    ) as pool:
        for record in pool.map(scan_segment, tasks, chunksize=1):
            records.append(record)
            if len(records) % 25 == 0 or len(records) == len(tasks):
                print(f"segments {len(records)}/{len(tasks)}", flush=True)
    records.sort(key=lambda record: int(record["index"]))

    prior_mass = 0.0
    correction = 0.0
    global_min = math.inf
    global_argmin = 2
    endpoint_trace: list[dict[str, int | float]] = []
    for record in records:
        candidate = float(record["local_min_before_prior_mass"]) - prior_mass
        if candidate < global_min:
            global_min = candidate
            global_argmin = int(record["local_argmin"])
        prior_mass, correction = add_kahan(prior_mass, correction, float(record["total_mass"]))
        high = int(record["high"])
        root = math.sqrt(high)
        endpoint_trace.append({
            "high": high,
            "completed_error": 2 * (root - 1 / root) - prior_mass,
        })
    root = math.sqrt(args.limit)
    payload = {
        "definition": "2*(sqrt(x)-1/sqrt(x))-sum_{k<=x} Lambda(k)/sqrt(k)",
        "limit": args.limit,
        "segment_size": args.segment_size,
        "workers": args.workers,
        "base_prime_count": len(base_primes),
        "prime_count": sum(int(record["prime_count"]) for record in records),
        "higher_prime_power_count": sum(int(record["higher_power_count"]) for record in records),
        "event_count": sum(int(record["event_count"]) for record in records),
        "minimum": global_min,
        "minimum_at_integer": global_argmin,
        "final_mass": prior_mass,
        "final_completed_error": 2 * (root - 1 / root) - prior_mass,
        "negative_found": global_min < -1e-8,
        "elapsed_seconds": time.time() - started,
        "endpoint_trace": endpoint_trace,
        "segments": records,
    }
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: payload[key] for key in (
        "limit", "prime_count", "higher_prime_power_count", "minimum",
        "minimum_at_integer", "final_completed_error", "negative_found", "elapsed_seconds",
    )}, indent=2))


if __name__ == "__main__":
    main()
