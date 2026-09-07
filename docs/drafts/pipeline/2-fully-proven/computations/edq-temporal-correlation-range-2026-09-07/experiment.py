#!/usr/bin/env python3
"""RunPod-only frozen temporal covariance discriminator; never a Lean certificate."""
import concurrent.futures
import hashlib
import json
import math
import os
import platform
import time

import numpy as np

LD = np.longdouble
MU = None


def direct_mu(n):
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
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


def channel(x, averaged):
    m, t = (4 * x if averaged else x), 256 * x
    d = np.arange(1, m + 1, dtype=np.int64)
    a = MU[1:m + 1].astype(LD)
    suffix_error = None
    if averaged:
        denominator = np.log(LD(m) / x)
        taper = np.log(LD(m) / np.maximum(x, d).astype(LD)) / denominator
        j = np.arange(x, m, dtype=np.int64).astype(LD)
        alpha = np.log1p(1 / j) / denominator
        suffix = np.cumsum(alpha[::-1], dtype=LD)[::-1]
        expected = np.zeros(m, dtype=LD)
        expected[:x] = suffix[0]
        expected[x:m - 1] = suffix[1:]
        suffix_error = float(np.max(np.abs(expected - taper)))
        assert suffix_error < 1e-14
        assert abs(np.sum(alpha, dtype=LD) - 1) < LD('1e-14')
        a *= taper
    harmonic = np.sum(a / d, dtype=LD)
    mass = np.sum(np.abs(a), dtype=LD)
    g = np.zeros(t + 1, dtype=LD if averaged else np.int64)
    for index in np.flatnonzero(a):
        divisor = int(index) + 1
        g[divisor::divisor] += a[index] if averaged else int(MU[divisor])
    cumulative = np.cumsum(g, dtype=LD)
    for start in range(1, t + 1, 262144):
        stop = min(start + 262144, t + 1)
        n = np.arange(start, stop, dtype=np.int64).astype(LD)
        cumulative[start:stop] = 1 + n * harmonic - cumulative[start:stop]
    cumulative[0] = 0
    head_n = np.arange(1, x + 1, dtype=np.int64).astype(LD)
    head_error = float(np.max(np.abs(cumulative[1:x + 1] - head_n * harmonic)))
    assert head_error < 1e-8
    direct_checks = []
    for n in sorted(set([1, x // 2, x, x + 1, 2 * x, 4 * x, t])):
        direct_error = 1 + LD(n) * harmonic - np.sum(a * (n // d), dtype=LD)
        discrepancy = float(abs(direct_error - cumulative[n]))
        direct_divisor = np.sum(a[n % d == 0], dtype=LD)
        divisor_discrepancy = float(abs(direct_divisor - g[n]))
        assert discrepancy < 2e-7
        assert divisor_discrepancy < 1e-10
        direct_checks.append({"n": n, "error": float(cumulative[n]),
                              "cumulative_discrepancy": discrepancy,
                              "divisor_discrepancy": divisor_discrepancy})
    ranges = [('one', 1), ('sqrt_X', math.isqrt(x)), ('X_over_16', x // 16),
              ('X_over_4', x // 4), ('X', x), ('4X', 4 * x),
              ('16X', 16 * x), ('64X', 64 * x), ('T', t)]
    cross = {label: LD(0) for label, _ in ranges}
    diagonal, energy = LD(0), LD(0)
    for start in range(1, t + 1, 262144):
        stop = min(start + 262144, t + 1)
        integers = np.arange(start, stop, dtype=np.int64)
        n = integers.astype(LD)
        increment = harmonic - g[start:stop].astype(LD)
        if start == 1:
            increment[0] += 1
        kernel = 1 / n - 1 / LD(t + 1)
        diagonal += np.sum(increment * increment * kernel, dtype=LD)
        energy += np.sum(cumulative[start:stop] ** 2 / (n * (n + 1)), dtype=LD)
        weighted = 2 * increment * kernel
        prior = cumulative[integers - 1]
        for label, radius in ranges:
            lower = np.maximum(integers - radius - 1, 0)
            cross[label] += np.sum(weighted * (prior - cumulative[lower]), dtype=LD)
    records = []
    for label, radius in ranges:
        band = diagonal + cross[label]
        omitted = energy - band
        records.append({"label": label, "radius": radius,
                        "signed_band_covariance": float(band),
                        "signed_cross_contribution": float(cross[label]),
                        "signed_omitted_covariance": float(omitted),
                        "absolute_relative_discrepancy": float(abs(omitted) / energy)})
    full_discrepancy = float(abs(diagonal + cross['T'] - energy))
    assert full_discrepancy < 2e-7, ("full_covariance", x, averaged, full_discrepancy)
    assert energy > 0
    return {"name": "average_4" if averaged else "raw_1", "M": m, "T": t,
            "harmonic_compensator": float(harmonic), "coefficient_l1": float(mass),
            "finite_error_energy": float(energy), "diagonal_covariance": float(diagonal),
            "bands": records, "full_covariance_absolute_discrepancy": full_discrepancy,
            "omitted_infinite_error_upper": float((1 + mass) ** 2 / (t + 1)),
            "suffix_check_max_error": suffix_error, "head_check_max_error": head_error,
            "direct_coordinate_checks": direct_checks}


def scale_job(k):
    started, x = time.monotonic(), 2 ** k
    rows = [channel(x, False), channel(x, True)]
    avg_bands = {row['label']: row for row in rows[1]['bands']}
    result = {"k": k, "X": x, "channels": rows,
              "seconds": time.monotonic() - started}
    print(json.dumps({"completed_k": k, "seconds": result['seconds'],
                      "avg_sqrt_relative_discrepancy": avg_bands['sqrt_X']['absolute_relative_discrepancy'],
                      "avg_X_relative_discrepancy": avg_bands['X']['absolute_relative_discrepancy']}), flush=True)
    return result


def main():
    global MU
    started = time.monotonic()
    MU, checks = mobius_sieve(4 * (2 ** 16))
    with concurrent.futures.ProcessPoolExecutor(max_workers=7) as pool:
        scales = list(pool.map(scale_job, range(10, 17)))
    bands = [{r['label']: r for r in scale['channels'][1]['bands']} for scale in scales]
    local = all(row['sqrt_X']['absolute_relative_discrepancy'] <= 0.25 for row in bands)
    nonlocal_count = sum(row['X']['absolute_relative_discrepancy'] > 1 for row in bands)
    classification = 'local' if local else 'nonlocal' if nonlocal_count >= 4 else 'mixed'
    with open(__file__, 'rb') as script:
        digest = hashlib.sha256(script.read()).hexdigest()
    result = {"status": "completed", "classification": classification,
              "nonlocal_count": nonlocal_count, "finite_prefix_only": True,
              "seconds": time.monotonic() - started, "workers": 7,
              "cpu_count": os.cpu_count(), "python": platform.python_version(),
              "numpy": np.__version__, "longdouble_mantissa_bits": int(np.finfo(LD).nmant),
              "script_sha256": digest, "sieve_checks": checks, "scales": scales}
    with open('results.json', 'w') as output:
        json.dump(result, output, indent=2)
        output.write('\n')
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ('scales', 'sieve_checks')}), flush=True)


if __name__ == '__main__':
    main()
