#!/usr/bin/env python3
"""Frozen modulus-ratio diagnostic of the complete EDQ reciprocal flux."""
import os
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[name] = '1'
import concurrent.futures
import json
import math
import platform
import time
from pathlib import Path
import numpy as np

LD = np.longdouble
CUTOFFS = (32, 48, 64, 96, 128, 192, 256, 384, 512)
RATIOS = (2, 4, 8, 16, 32, 64)
WORKERS = 8
DMAX = 32768
DIRECT_J = 4096
MARGIN = LD('1e-8')


def mobius(n):
    mu = np.ones(n + 1, dtype=np.int64)
    prime = np.ones(n + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, n + 1):
        if prime[p]:
            mu[p::p] *= -1
            mu[p*p::p*p] = 0
            prime[p*p::p] = False
    mu[0] = 0
    return mu


def factor_mu(n):
    sign, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def inputs():
    data = np.load('baseline_kernel_bounds.npz')
    baseline = json.loads(Path('baseline_results.json').read_text())
    return data['lower'], data['upper'], data['mu'], baseline


def lifted_kernel(d, e, lo, hi):
    r = d % e
    scale = (r.astype(LD)/d.astype(LD))**2
    return scale*lo[r, e], scale*hi[r, e]


def signed_sum(sign, lower, upper):
    return (np.sum(np.where(sign >= 0, sign*lower, sign*upper), dtype=LD),
            np.sum(np.where(sign >= 0, sign*upper, sign*lower), dtype=LD))


def record_interval(lower, upper):
    assert lower <= upper
    return {'lower': str(lower), 'upper': str(upper)}


def cutoff(n):
    lo, hi, _, baseline = inputs()
    mu = mobius(64*n)
    full = baseline['cutoffs'][n-1]
    rlo = LD(full['flux_lo'])-MARGIN
    rhi = LD(full['flux_hi'])+MARGIN
    assert 0 < rlo <= rhi
    band_lo = np.zeros(len(RATIOS), dtype=LD)
    band_hi = np.zeros(len(RATIOS), dtype=LD)
    for e in range(2, n+1):
        if mu[e] == 0:
            continue
        previous = n
        for b, ratio in enumerate(RATIOS):
            last = ratio*e
            if last > previous:
                d = np.arange(previous+1, last+1, dtype=np.int64)
                a, z = lifted_kernel(d, e, lo, hi)
                sa, sz = signed_sum(-mu[d]*mu[e], a, z)
                band_lo[b] += sa
                band_hi[b] += sz
            previous = max(previous, last)
    records = []
    slo, shi = LD(0), LD(0)
    for b, ratio in enumerate(RATIOS):
        slo += band_lo[b]
        shi += band_hi[b]
        tlo, thi = rlo-shi-MARGIN, rhi-slo+MARGIN
        distance = max(tlo, -thi, LD(0))
        absolute = max(abs(tlo), abs(thi))
        records.append({'ratio': ratio,
                        'band': record_interval(band_lo[b]-MARGIN, band_hi[b]+MARGIN),
                        'partial': record_interval(slo-MARGIN, shi+MARGIN),
                        'complete_remainder': record_interval(tlo, thi),
                        'relative_remainder': record_interval(distance/rhi, absolute/rlo)})
    return {'n': n, 'full_flux': record_interval(rlo, rhi), 'ratios': records}


def validate(lo, hi, saved_mu):
    mu = mobius(DMAX)
    checks = list(range(1, 257))+list(range(32700, DMAX+1))
    assert all(mu[n] == factor_mu(n) for n in checks)
    assert np.array_equal(mu[:len(saved_mu)], saved_mu)
    divisor_sum = np.zeros(DMAX+1, dtype=np.int64)
    for d in range(1, DMAX+1):
        if mu[d]:
            divisor_sum[d::d] += mu[d]
    assert divisor_sum[1] == 1 and np.all(divisor_sum[2:] == 0)
    d = np.arange(1, 513, dtype=np.int64)
    for e in range(1, 513):
        a, b = lifted_kernel(d, e, lo, hi)
        assert np.all(np.maximum(a, lo[d, e]) <= np.minimum(b, hi[d, e])+MARGIN)
        assert np.all(a[d % e == 0] == 0) and np.all(b[d % e == 0] == 0)
    direct = []
    j = np.arange(1, DIRECT_J+1, dtype=np.int64)
    for d, e in ((513, 511), (1025, 512), (2039, 127), (32767, 31)):
        rem = (d*j) % e
        p = (rem*(rem-e)).astype(LD)/(2*LD(e))
        partial = np.sum(p/(LD(d)*j.astype(LD))**2, dtype=LD)
        tail = LD(e)/(8*LD(d)**2*DIRECT_J)
        a, b = lifted_kernel(np.array([d], dtype=np.int64), e, lo, hi)
        assert max(a[0], partial-tail) <= min(b[0], partial)+MARGIN
        direct.append({'d': d, 'e': e, 'periodic': record_interval(a[0], b[0]),
                       'direct_series': record_interval(partial-tail, partial)})
    columns = []
    ds = np.arange(1, DMAX+1, dtype=np.int64)
    pi = np.arccos(LD(-1))
    for e in (2, 7, 31):
        a, b = lifted_kernel(ds, e, lo, hi)
        sa, sb = signed_sum(mu[ds], a, b)
        tail = LD(e)*(pi*pi/6)/(8*DMAX)
        target = -LD(e-1)/(2*e)
        assert sa-tail-MARGIN <= target <= sb+tail+MARGIN
        columns.append({'e': e, 'finite_column': record_interval(sa, sb),
                        'tail_absolute_bound': str(tail), 'target': str(target)})
    n2 = cutoff(2)
    for row, target in zip(n2['ratios'][:2],
                          (pi*pi/(32*9), pi*pi/32*(LD(1)/9+LD(1)/25+LD(1)/49))):
        interval = row['partial']
        assert LD(interval['lower']) <= target <= LD(interval['upper'])
    return {'mobius_factorization_count': len(checks),
            'divisor_identity_through': DMAX, 'periodic_pairs_checked': 512*512,
            'direct_new_pairs': direct, 'complete_columns': columns, 'n2': n2}


def main():
    started = time.monotonic()
    lo, hi, saved_mu, baseline = inputs()
    controls = validate(lo, hi, saved_mu)
    with concurrent.futures.ProcessPoolExecutor(max_workers=WORKERS) as pool:
        records = list(pool.map(cutoff, CUTOFFS))
    primary = [record['ratios'][1]['relative_remainder'] for record in records]
    local = all(LD(row['upper']) <= LD(1)/4 for row in primary)
    large = sum(LD(row['lower']) > 1 for row in primary)
    classification = 'LOCAL' if local else ('CROSS-RATIO CANCELLATION' if large >= 5 else 'MIXED')
    reversed_prediction = any(LD(row['lower']) > LD(1)/4 for row in primary)
    result = {'parameters': {'cutoffs': CUTOFFS, 'ratios': RATIOS, 'workers': WORKERS,
                             'direct_j': DIRECT_J, 'floating_margin': str(MARGIN)},
              'environment': {'python': platform.python_version(), 'numpy': np.__version__,
                              'longdouble_mantissa_bits': np.finfo(LD).nmant},
              'classification': classification,
              'prediction': 'REVERSED' if reversed_prediction else ('SURVIVES_FINITE_TEST' if local else 'UNRESOLVED'),
              'ratio_four_lower_above_one_count': large,
              'cutoffs': records, 'controls': controls,
              'scope': 'Floating evaluations of analytic enclosures, not certified intervals or Lean evidence.',
              'wall_seconds': time.monotonic()-started}
    Path('results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in
                      ('classification', 'prediction', 'ratio_four_lower_above_one_count', 'wall_seconds')}, indent=2), flush=True)
    for record in records:
        print(json.dumps({'n': record['n'], 'ratios': record['ratios']}), flush=True)


if __name__ == '__main__':
    main()
