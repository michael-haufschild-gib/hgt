#!/usr/bin/env python3
"""Numerical audit of the Route-P two-step wild-saddle Xi relocation.

The Lean corpus proves that the signed diagonal difference is Schatten-1, but
does not give a useful numerical trace-norm bound.  This script evaluates its
finite sections against critical-line Xi ordinates returned by mpmath.

The computation is diagnostic only.  It neither verifies completeness of the
zero list nor tests horizontal displacement of a hypothetical off-line zero.
"""

import argparse
import json
import math
import sys
import time
from pathlib import Path

import mpmath as mp


def two_step_source_reciprocal(index):
    """Lean's routePTwoStepWildSaddleReciprocal, with zero-based index."""
    mass = max(mp.exp(3), mp.mpf(index) + mp.mpf(1) / 8)
    log_phase = mp.log(mass / mp.e)
    first_phase = log_phase - mp.log(log_phase)
    second_phase = log_phase - mp.log(first_phase)
    return second_phase / (2 * mp.pi * mass)


def smooth_rvm_reciprocal(index):
    """Exact reciprocal of the smooth RVM quantile used by the corpus."""
    count = mp.mpf(index) + mp.mpf(1) / 8
    u = mp.lambertw(count / mp.e)
    return u / (2 * mp.pi * count)


def critical_zero_reciprocal(index):
    """Reciprocal ordinate of mpmath's (index+1)-st critical-line zero."""
    zero = mp.zetazero(index + 1)
    return 1 / mp.im(zero), mp.im(zero)


def as_float(value):
    return float(value)


def load_zero_cache(path):
    cached = {}
    if path is None or not path.exists():
        return cached
    with path.open() as handle:
        for line_number, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            record = json.loads(line)
            index = int(record["index_zero_based"])
            ordinate = mp.mpf(record["ordinate"])
            if index in cached and cached[index] != ordinate:
                raise SystemExit(
                    f"conflicting cache entry for index {index} at line {line_number}"
                )
            cached[index] = ordinate
    return cached


def write_result(path, result):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--count", type=int, default=2000)
    parser.add_argument("--dps", type=int, default=50)
    parser.add_argument(
        "--checkpoints",
        default="10,25,50,100,250,500,1000,2000",
        help="Comma-separated one-based finite-section sizes",
    )
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--zero-cache",
        type=Path,
        help="Append-only JSONL cache of zero ordinates for restartable runs",
    )
    parser.add_argument("--progress-every", type=int, default=25)
    args = parser.parse_args()

    if args.count <= 0:
        raise SystemExit("--count must be positive")

    mp.mp.dps = args.dps
    zero_cache = load_zero_cache(args.zero_cache)
    cache_handle = None
    if args.zero_cache is not None:
        args.zero_cache.parent.mkdir(parents=True, exist_ok=True)
        cache_handle = args.zero_cache.open("a", buffering=1)
    requested = {
        int(item)
        for item in args.checkpoints.split(",")
        if item.strip() and 0 < int(item) <= args.count
    }
    requested.add(args.count)

    started = time.time()
    abs_xi_source = mp.mpf(0)
    signed_xi_source = mp.mpf(0)
    abs_xi_rvm = mp.mpf(0)
    abs_source_rvm = mp.mpf(0)
    rows = []
    block_abs = []
    first_terms = []

    for index in range(args.count):
        if index in zero_cache:
            ordinate = zero_cache[index]
            xi_reciprocal = 1 / ordinate
        else:
            xi_reciprocal, ordinate = critical_zero_reciprocal(index)
            if cache_handle is not None:
                cache_handle.write(
                    json.dumps(
                        {
                            "index_zero_based": index,
                            "ordinate": mp.nstr(ordinate, n=args.dps),
                        },
                        sort_keys=True,
                    )
                    + "\n"
                )
        source_reciprocal = two_step_source_reciprocal(index)
        rvm_reciprocal = smooth_rvm_reciprocal(index)

        xi_source = xi_reciprocal - source_reciprocal
        xi_rvm = xi_reciprocal - rvm_reciprocal
        source_rvm = source_reciprocal - rvm_reciprocal

        abs_xi_source += abs(xi_source)
        signed_xi_source += xi_source
        abs_xi_rvm += abs(xi_rvm)
        abs_source_rvm += abs(source_rvm)
        block_abs.append(abs(xi_source))

        if index < 25:
            first_terms.append(
                {
                    "index_zero_based": index,
                    "ordinate": as_float(ordinate),
                    "xi_reciprocal": as_float(xi_reciprocal),
                    "source_reciprocal": as_float(source_reciprocal),
                    "smooth_rvm_reciprocal": as_float(rvm_reciprocal),
                    "xi_minus_source": as_float(xi_source),
                    "abs_xi_minus_source": as_float(abs(xi_source)),
                }
            )

        size = index + 1
        if size in requested:
            half = size // 2
            last_half_mass = mp.fsum(block_abs[half:]) if half else mp.fsum(block_abs)
            previous_quarter_mass = (
                mp.fsum(block_abs[size // 4 : half]) if size >= 4 else mp.nan
            )
            block_ratio = (
                last_half_mass / previous_quarter_mass
                if size >= 4 and previous_quarter_mass != 0
                else mp.nan
            )
            rows.append(
                {
                    "count": size,
                    "one_sided_trace_norm_partial": as_float(abs_xi_source),
                    "signed_double_trace_norm_partial": as_float(2 * abs_xi_source),
                    "one_sided_signed_trace_partial": as_float(signed_xi_source),
                    "signed_double_trace_partial": 0.0,
                    "xi_to_rvm_l1_partial": as_float(abs_xi_rvm),
                    "source_to_rvm_l1_partial": as_float(abs_source_rvm),
                    "last_half_block_l1": as_float(last_half_mass),
                    "previous_quarter_to_last_half_ratio": as_float(block_ratio),
                }
            )
            partial_result = {
                "metadata": {
                    "count_requested": args.count,
                    "count_completed": size,
                    "mpmath_dps": args.dps,
                    "mpmath_version": mp.__version__,
                    "elapsed_seconds": time.time() - started,
                    "complete": size == args.count,
                    "interpretation_warning": (
                        "Finite critical-line zero computation only. It cannot detect "
                        "hypothetical off-line zeros or certify the infinite trace norm."
                    ),
                },
                "definitions": {
                    "source_mass": "max(exp(3), n + 1/8)",
                    "source_reciprocal": (
                        "(L-log(L-log L))/(2*pi*mass), L=log(mass/e)"
                    ),
                    "smooth_rvm_reciprocal": "W((n+1/8)/e)/(2*pi*(n+1/8))",
                    "signed_trace_norm_partial": "2*sum_{n<N}|1/gamma_n-r_n|",
                    "signed_trace_partial": "sum(d_n-d_n)=0",
                },
                "checkpoints": rows,
                "first_terms": first_terms,
            }
            write_result(args.output, partial_result)

        if args.progress_every > 0 and size % args.progress_every == 0:
            elapsed = time.time() - started
            print(
                f"zeros={size}/{args.count} signed-S1-partial={float(2 * abs_xi_source):.12g} "
                f"elapsed={elapsed:.1f}s",
                file=sys.stderr,
                flush=True,
            )

    if cache_handle is not None:
        cache_handle.close()

    result = {
        "metadata": {
            "count_requested": args.count,
            "count_completed": args.count,
            "mpmath_dps": args.dps,
            "mpmath_version": mp.__version__,
            "elapsed_seconds": time.time() - started,
            "complete": True,
            "interpretation_warning": (
                "Finite critical-line zero computation only. It cannot detect hypothetical "
                "off-line zeros or certify the infinite trace norm."
            ),
        },
        "definitions": {
            "source_mass": "max(exp(3), n + 1/8)",
            "source_reciprocal": (
                "(L-log(L-log L))/(2*pi*mass), L=log(mass/e)"
            ),
            "smooth_rvm_reciprocal": "W((n+1/8)/e)/(2*pi*(n+1/8))",
            "signed_trace_norm_partial": "2*sum_{n<N}|1/gamma_n-r_n|",
            "signed_trace_partial": "sum(d_n-d_n)=0",
        },
        "checkpoints": rows,
        "first_terms": first_terms,
    }

    write_result(args.output, result)
    print(json.dumps(result["checkpoints"][-1], sort_keys=True))


if __name__ == "__main__":
    main()
