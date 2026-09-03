#!/usr/bin/env python3
"""Audit the Gamma-completed cubic Green tail above the first prime clock.

For L = log 2 and F(h) = exp(-h/2)/(4 h^3), the literal completed
Guinand--Weil window on (L,H] has channels

    prime  = sum_{2 < p^k <= exp(H)} 1/(4 p^k k^3 log(p)^2),
    polar  = integral_L^H (1 + exp(-h))/(4 h^3) dh,
    gamma  = integral_L^H exp(-h)/(4 h^3 (1-exp(-2h))) dh.

The completed scalar window is prime - polar + gamma.  The strict lower
window convention excludes the p^k = 2 atom; it is reported separately.
This is a numerical diagnostic, not an interval proof or operator estimate.
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


def polar_tail(height):
    lower = mp.log(2)
    if height <= lower:
        return mp.mpf("0")
    return mp.quad(lambda h: (1 + mp.exp(-h)) / (4 * h**3), [lower, height])


def gamma_tail(height):
    lower = mp.log(2)
    if height <= lower:
        return mp.mpf("0")
    return mp.quad(
        lambda h: mp.exp(-h) / (4 * h**3 * (1 - mp.exp(-2 * h))),
        [lower, height],
    )


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

    mp.mp.dps = args.dps
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

    first_atom = mp.mpf(1) / (8 * mp.log(2) ** 2)
    rows = []
    prime_mass_including_first = 0.0
    cumulative_events = 0
    for cutoff, bucket, new_events in zip(cutoffs, buckets, event_counts):
        prime_mass_including_first += math.fsum(bucket)
        cumulative_events += new_events
        height = mp.log(cutoff)
        prime_open = mp.mpf(prime_mass_including_first) - first_atom
        polar = polar_tail(height)
        gamma = gamma_tail(height)
        completed = prime_open - polar + gamma
        rows.append(
            {
                "cutoff": cutoff,
                "height": mp.nstr(height, args.dps),
                "prime_power_events_including_first": cumulative_events,
                "first_prime_atom": mp.nstr(first_atom, args.dps),
                "open_window_prime_mass": mp.nstr(prime_open, args.dps),
                "polar_tail": mp.nstr(polar, args.dps),
                "gamma_tail": mp.nstr(gamma, args.dps),
                "completed_open_window": mp.nstr(completed, args.dps),
                "completed_abs": mp.nstr(abs(completed), args.dps),
            }
        )

    infinite_polar = polar_tail(mp.inf)
    infinite_gamma = gamma_tail(mp.inf)
    result = {
        "metadata": {
            "cutoffs": cutoffs,
            "largest_cutoff": cutoffs[-1],
            "prime_count": len(primes),
            "mpmath_dps": args.dps,
            "mpmath_version": mp.__version__,
            "elapsed_seconds": time.time() - started,
            "interpretation_warning": (
                "Floating-point prime-power sum and high-precision quadrature only; no interval "
                "certificate or infinite prime-tail bound. The strict lower window excludes n=2."
            ),
        },
        "identities": {
            "lower_wall": "log(2)",
            "green_profile": "exp(-h/2)/(4*h^3)",
            "prime_power_weight": "1/(4*p^k*k^3*log(p)^2)",
            "polar_integrand": "(1+exp(-h))/(4*h^3)",
            "gamma_integrand": "exp(-h)/(4*h^3*(1-exp(-2*h)))",
            "completed_window": "prime-polar+gamma",
        },
        "infinite_polar_tail": mp.nstr(infinite_polar, args.dps),
        "infinite_gamma_tail": mp.nstr(infinite_gamma, args.dps),
        "rows": rows,
    }
    write_result(args.output, result)
    print(json.dumps(rows[-1], sort_keys=True))


if __name__ == "__main__":
    main()
