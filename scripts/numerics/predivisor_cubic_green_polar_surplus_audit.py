#!/usr/bin/env python3
"""Finite-aperture audit of the exact CCM/Route-P cubic-Green fracture.

For horizon height H=2a and L=log 2, the common Green test gives

    pole(H) = integral_0^H (1+exp(-h))/(4*max(h,L)^3) dh,

while the prime channel is the negative truncated Route-P base budget

    prime(N) = sum_{p^k <= N} 1/(4*p^k*k^3*log(p)^2),  N=floor(exp H).

The exact Lean identity is therefore pole(H)-prime(N).  This script only
measures finite cutoffs.  It does not construct a Schur complement, prove a
trace-class operator identity, or certify an infinite-limit inequality.
"""

import argparse
import bisect
import json
import math
import sys
import time
from pathlib import Path

import mpmath as mp


def parse_cutoffs(text):
    values = sorted(set(int(item.strip()) for item in text.split(",") if item.strip()))
    if not values or values[0] < 2:
        raise SystemExit("--cutoffs must contain integers at least 2")
    return values


def primes_through(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
    return [n for n in range(2, limit + 1) if sieve[n]]


def pole_mass(height, dps):
    mp.mp.dps = dps
    height_mp = mp.mpf(height)
    log_two = mp.log(2)
    low_end = min(height_mp, log_two)
    low = (low_end + 1 - mp.exp(-low_end)) / (4 * log_two**3)
    if height_mp <= log_two:
        return low
    tail = mp.quad(lambda h: (1 + mp.exp(-h)) / (4 * h**3), [log_two, height_mp])
    return low + tail


def write_result(path, result):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cutoffs",
        default="2,3,10,100,1000,10000,100000,1000000,10000000,50000000",
    )
    parser.add_argument("--dps", type=int, default=100)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    cutoffs = parse_cutoffs(args.cutoffs)
    started = time.time()
    primes = primes_through(cutoffs[-1])
    print("primes={}".format(len(primes)), file=sys.stderr, flush=True)

    buckets = [[] for _ in cutoffs]
    event_counts = [0 for _ in cutoffs]
    for index, p in enumerate(primes, start=1):
        log_p = math.log(p)
        power = p
        depth = 1
        while power <= cutoffs[-1]:
            first_cutoff = bisect.bisect_left(cutoffs, power)
            weight = 1.0 / (4.0 * power * depth**3 * log_p**2)
            buckets[first_cutoff].append(weight)
            event_counts[first_cutoff] += 1
            if power > cutoffs[-1] // p:
                break
            power *= p
            depth += 1
        if index % 500000 == 0:
            print("processed_primes={}".format(index), file=sys.stderr, flush=True)

    rows = []
    prime_mass = 0.0
    cumulative_events = 0
    for cutoff, bucket, new_events in zip(cutoffs, buckets, event_counts):
        prime_mass += math.fsum(bucket)
        cumulative_events += new_events
        height = math.log(cutoff)
        polar = pole_mass(height, args.dps)
        prime_mp = mp.mpf(prime_mass)
        surplus = polar - prime_mp
        rows.append(
            {
                "cutoff": cutoff,
                "aperture_a": height / 2.0,
                "prime_power_events": cumulative_events,
                "polar_mass": mp.nstr(polar, args.dps),
                "truncated_route_p_base_budget": prime_mass,
                "polar_surplus": mp.nstr(surplus, args.dps),
                "prime_to_polar_ratio": mp.nstr(prime_mp / polar, args.dps),
            }
        )

    infinite_polar = pole_mass(mp.inf, args.dps)
    result = {
        "metadata": {
            "cutoffs": cutoffs,
            "largest_cutoff": cutoffs[-1],
            "prime_count": len(primes),
            "mpmath_dps": args.dps,
            "mpmath_version": mp.__version__,
            "elapsed_seconds": time.time() - started,
            "interpretation_warning": (
                "Finite uncensored floating-point prime-power sum. The polar integral is "
                "high precision, but no interval certificate or infinite prime-tail bound is supplied."
            ),
        },
        "identities": {
            "green_profile": "exp(-h/2)/(4*max(h,log(2))^3)",
            "polar_integrand": "(1+exp(-h))/(4*max(h,log(2))^3)",
            "prime_power_weight": "1/(4*p^k*k^3*log(p)^2)",
            "fracture": "polar_mass-truncated_route_p_base_budget",
        },
        "infinite_polar_mass": mp.nstr(infinite_polar, args.dps),
        "rows": rows,
    }
    write_result(args.output, result)
    print(json.dumps(rows[-1], sort_keys=True))


if __name__ == "__main__":
    main()
