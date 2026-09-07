#!/usr/bin/env python3
"""Frozen EDQ cutoff-average experiment. Execute only on the authorized RunPod.

Finite numerical evidence only; no output is a Lean certificate.
"""
import concurrent.futures
import hashlib
import json
import os
import platform
import time

import numpy as np

LD = np.longdouble
SCALES = tuple(range(10, 17))
MU = None


def direct_mu(n):
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -sign if n > 1 else sign


def mobius_sieve(limit):
    mu = np.ones(limit + 1, dtype=np.int8)
    prime = np.ones(limit + 1, dtype=bool)
    prime[:2] = False
    mu[0] = 0
    for p in range(2, limit + 1):
        if prime[p]:
            mu[p::p] *= -1
            if p * p <= limit:
                prime[p * p::p] = False
                mu[p * p::p * p] = 0
    checks = sorted(set(list(range(1, 101)) +
                        [1024, 1558, 2161, 5297, 15045, 65521, 65536,
                         81017, 131071, limit - 1, limit]))
    for n in checks:
        assert int(mu[n]) == direct_mu(n), ("mobius", n)
    return mu, checks


def channel(x, support, averaged):
    t = 256 * x
    d = np.arange(1, support + 1, dtype=np.int64)
    coeff = MU[1:support + 1].astype(LD)
    coefficient_check = None
    if averaged:
        denominator = np.log(LD(support) / x)
        taper = np.log(LD(support) / np.maximum(x, d).astype(LD)) / denominator
        j = np.arange(x, support, dtype=np.int64).astype(LD)
        alpha = np.log1p(1 / j) / denominator
        suffix = np.cumsum(alpha[::-1], dtype=LD)[::-1]
        expected = np.zeros(support, dtype=LD)
        expected[:x] = suffix[0]
        expected[x:support - 1] = suffix[1:]
        coefficient_check = float(np.max(np.abs(expected - taper)))
        assert coefficient_check < 1e-14
        assert abs(np.sum(alpha, dtype=LD) - 1) < LD('1e-14')
        coeff *= taper
    h = np.sum(coeff / d, dtype=LD)
    mass = np.sum(np.abs(coeff), dtype=LD)
    jump = np.zeros(t + 1, dtype=LD if averaged else np.int64)
    for index in np.flatnonzero(coeff):
        divisor = int(index) + 1
        value = coeff[index] if averaged else int(MU[divisor])
        jump[divisor::divisor] += value
    np.cumsum(jump, dtype=jump.dtype, out=jump)
    head_limit = x if averaged else support
    head_deviation = float(np.max(np.abs(jump[1:head_limit + 1] - 1)))
    assert head_deviation < 1e-8, ("head", x, support, averaged, head_deviation)
    coordinates = sorted(set([1, x // 2, x, x + 1, 2 * x, 4 * x, t]))
    direct_checks = []
    for n in coordinates:
        direct_floor = np.sum(coeff * (n // d), dtype=LD)
        direct_value = direct_floor - LD(n) * h
        sieve_value = LD(jump[n]) - LD(n) * h
        delta = abs(direct_value - sieve_value)
        assert delta < LD('2e-7'), ("coordinate", n, float(delta))
        direct_checks.append({"n": n, "value": float(sieve_value),
                              "absolute_discrepancy": float(delta)})
    boundaries = [0] + [x * (2 ** j) for j in range(9)]
    blocks = []
    for lo, hi in zip(boundaries, boundaries[1:]):
        norm, error = LD(0), LD(0)
        for start in range(lo + 1, hi + 1, 262144):
            stop = min(start + 262144, hi + 1)
            n = np.arange(start, stop, dtype=np.int64).astype(LD)
            values = jump[start:stop].astype(LD) - n * h
            weight = 1 / (n * (n + 1))
            norm += np.sum(values * values * weight, dtype=LD)
            error += np.sum((1 - values) ** 2 * weight, dtype=LD)
        blocks.append({"lo_exclusive": lo, "hi_inclusive": hi,
                       "target_error_energy": float(error),
                       "raw_norm_squared": float(norm)})
    return {"name": ("average" if averaged else "raw") + "_" + str(support // x),
            "support_endpoint": support, "harmonic_compensator": float(h),
            "coefficient_l1": float(mass),
            "coefficient_suffix_max_error": coefficient_check,
            "head_floor_max_error": head_deviation,
            "direct_coordinate_checks": direct_checks, "blocks": blocks,
            "omitted_target_error_upper": float((1 + mass) ** 2 / (t + 1)),
            "omitted_raw_norm_upper": float(mass ** 2 / (t + 1))}


def scale_job(k):
    started = time.monotonic()
    x = 2 ** k
    channels = [channel(x, width * x, False) for width in (1, 2, 4)]
    channels += [channel(x, width * x, True) for width in (2, 4)]
    lookup = {row['name']: row for row in channels}
    ratios = []
    for width in (2, 4):
        totals = []
        for name in ('average_' + str(width), 'raw_' + str(width)):
            totals.append(sum(block['target_error_energy']
                              for block in lookup[name]['blocks']
                              if block['lo_exclusive'] >= width * x))
        ratios.append({"width": width, "average_post_support_energy": totals[0],
                       "raw_endpoint_post_support_energy": totals[1],
                       "ratio": totals[0] / totals[1]})
    result = {"k": k, "X": x, "T": 256 * x, "channels": channels,
              "primary_ratios": ratios, "seconds": time.monotonic() - started}
    print(json.dumps({"completed_k": k, "seconds": result['seconds'],
                      "primary_ratios": ratios}), flush=True)
    return result


def main():
    global MU
    started = time.monotonic()
    MU, sieve_checks = mobius_sieve(4 * (2 ** max(SCALES)))
    with concurrent.futures.ProcessPoolExecutor(max_workers=7) as pool:
        scales = list(pool.map(scale_job, SCALES))
    ratios = [r for scale in scales for r in scale['primary_ratios']]
    strong = all(r['ratio'] <= 0.25 for r in ratios)
    persistent_count = sum(r['width'] == 4 and r['ratio'] >= 0.75 for r in ratios)
    classification = ('strong post-support suppression' if strong else
                      'persistent post-support error' if persistent_count >= 4 else 'mixed')
    with open(__file__, 'rb') as script:
        script_sha256 = hashlib.sha256(script.read()).hexdigest()
    result = {"status": "completed", "classification": classification,
              "width_four_persistent_count": persistent_count,
              "finite_prefix_only": True, "seconds": time.monotonic() - started,
              "workers": 7, "cpu_count": os.cpu_count(),
              "python": platform.python_version(), "numpy": np.__version__,
              "longdouble_mantissa_bits": int(np.finfo(LD).nmant),
              "script_sha256": script_sha256, "sieve_checks": sieve_checks,
              "scales": scales}
    with open('results.json', 'w') as output:
        json.dump(result, output, indent=2)
        output.write('\n')
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ('scales', 'sieve_checks')}), flush=True)


if __name__ == '__main__':
    main()
