#!/usr/bin/env python3
"""Frozen full-series sign diagnostic for the literal EDQ reciprocal flux."""
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
NMAX = 512
BLOCKS = 512
WORKERS = 8
MARGIN = LD('1e-8')
DIRECT_T = 262144


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


def kernel_column(e):
    d = np.arange(1, NMAX + 1, dtype=np.int64)
    if e == 1:
        return e, np.zeros(NMAX, dtype=LD), np.zeros(NMAX, dtype=LD)
    r = np.arange(1, e + 1, dtype=np.int64)
    m = np.arange(BLOCKS, dtype=np.int64)
    base = (r[:, None] + e*m[None, :]).astype(LD)
    partial = np.sum(1/(base*base), axis=1, dtype=LD)
    a = (r + BLOCKS*e).astype(LD)
    wlo = partial + 1/(LD(e)*a)
    whi = wlo + 1/(a*a)
    rem = (d[:, None]*r[None, :]) % e
    numerator = rem*(rem-e)
    assert np.all(numerator <= 0)
    primitive = numerator.astype(LD)/(2*LD(e))
    dsq = d.astype(LD)**2
    lo = np.sum(primitive*whi[None, :], axis=1, dtype=LD)/dsq
    hi = np.sum(primitive*wlo[None, :], axis=1, dtype=LD)/dsq
    assert np.all(lo <= hi)
    assert lo[e-1] == 0 and hi[e-1] == 0
    assert np.all(lo[d % e == 0] == 0)
    assert np.all(hi[d % e == 0] == 0)
    return e, lo, hi


def direct_flux(n):
    mu = mobius(n)
    k = np.arange(1, DIRECT_T + 1, dtype=np.int64)
    u = np.zeros(DIRECT_T, dtype=LD)
    g = np.zeros(DIRECT_T, dtype=np.int64)
    for d in range(1, n + 1):
        if mu[d]:
            rem = k % d
            u += LD(mu[d])*(rem*(rem-d)).astype(LD)/(2*LD(d))
            g[d-1::d] += mu[d]
    assert g[0] == 1 and np.all(g[1:n] == 0)
    kk = k[n:].astype(LD)
    prefix = np.sum(u[n:]*g[n:].astype(LD)/(kk*kk), dtype=LD)
    d = np.arange(1, n + 1, dtype=np.int64)
    absmu = np.abs(mu[1:]).astype(LD)
    bound_u = np.sum(absmu*d.astype(LD), dtype=LD)/8
    tail = bound_u*np.sum(absmu/(d.astype(LD)**2*(DIRECT_T//d).astype(LD)), dtype=LD)
    return {'n': n, 'T': DIRECT_T, 'prefix': str(prefix),
            'tail_absolute_bound': str(tail), 'lo': str(prefix-tail), 'hi': str(prefix+tail)}


def interval_quadratic(n, lo, hi, mu):
    sign = mu[1:n+1, None]*mu[None, 1:n+1]
    a, b = lo[1:n+1, 1:n+1], hi[1:n+1, 1:n+1]
    return (np.sum(np.where(sign >= 0, sign*a, sign*b), dtype=LD),
            np.sum(np.where(sign >= 0, sign*b, sign*a), dtype=LD))


def main():
    started = time.monotonic()
    mu = mobius(NMAX)
    lo = np.zeros((NMAX+1, NMAX+1), dtype=LD)
    hi = np.zeros_like(lo)
    with concurrent.futures.ProcessPoolExecutor(max_workers=WORKERS) as pool:
        for e, a, b in pool.map(kernel_column, range(1, NMAX+1), chunksize=4):
            lo[1:, e], hi[1:, e] = a, b
        direct = list(pool.map(direct_flux, (2, 7, 31)))
    assert np.all(np.diag(lo) == 0) and np.all(np.diag(hi) == 0)
    records = []
    phi_lo, phi_hi, harmonic = LD(0), LD(0), LD(0)
    mertens = 0
    recurrence_controls = []
    for n in range(1, NMAX+1):
        signs = mu[n]*mu[1:n]
        a = lo[n, 1:n] + lo[1:n, n]
        b = hi[n, 1:n] + hi[1:n, n]
        phi_lo += np.sum(np.where(signs >= 0, signs*a, signs*b), dtype=LD)
        phi_hi += np.sum(np.where(signs >= 0, signs*b, signs*a), dtype=LD)
        harmonic += LD(mu[n])/LD(n)
        mertens += int(mu[n])
        c = (LD(mertens)-harmonic)/2
        lower, upper = phi_lo+c, phi_hi+c
        if n == 1:
            assert lower == 0 and upper == 0
            classification = 'exact_zero'
        elif upper < -MARGIN:
            classification = 'negative'
        elif lower > MARGIN:
            classification = 'positive'
        else:
            classification = 'unresolved'
        records.append({'n': n, 'mu': int(mu[n]), 'mertens': mertens,
                        'mobius_harmonic': str(harmonic), 'mean_correction': str(c),
                        'phi_lo': str(phi_lo), 'phi_hi': str(phi_hi),
                        'flux_lo': str(lower), 'flux_hi': str(upper),
                        'classification': classification})
        if n in (31, 127, 512):
            aa, bb = interval_quadratic(n, lo, hi, mu)
            err = max(abs(aa-phi_lo), abs(bb-phi_hi))
            assert err < LD('1e-10'), (n, str(err))
            recurrence_controls.append({'n': n, 'max_discrepancy': str(err)})
    reference = (LD(math.pi)**2-8)/32
    two = records[1]
    assert LD(two['flux_lo'])-MARGIN <= reference <= LD(two['flux_hi'])+MARGIN
    for item in direct:
        record = records[item['n']-1]
        overlap = max(LD(item['lo']), LD(record['flux_lo'])) <= min(LD(item['hi']), LD(record['flux_hi']))+MARGIN
        assert overlap, (item, record)
        item['kernel_interval_overlap'] = bool(overlap)
    counts = {key: sum(r['classification'] == key for r in records)
              for key in ('exact_zero', 'positive', 'negative', 'unresolved')}
    result = {'parameters': {'NMAX': NMAX, 'BLOCKS': BLOCKS, 'WORKERS': WORKERS,
                             'DIRECT_T': DIRECT_T, 'floating_sensitivity_margin': str(MARGIN)},
              'environment': {'python': platform.python_version(), 'numpy': np.__version__,
                              'longdouble_mantissa_bits': np.finfo(LD).nmant},
              'counts': counts, 'prediction': 'REVERSED' if counts['negative'] else
                  ('SURVIVES_FINITE_TEST' if not counts['unresolved'] else 'UNRESOLVED'),
              'first_negative': next((r for r in records if r['classification'] == 'negative'), None),
              'minimum_upper': min(records[1:], key=lambda r: LD(r['flux_hi'])),
              'maximum_lower': max(records, key=lambda r: LD(r['flux_lo'])),
              'maximum_interval_width': str(max(LD(r['flux_hi'])-LD(r['flux_lo']) for r in records)),
              'controls': {'n2_formula_value': str(reference), 'direct_time_flux': direct,
                           'recurrence': recurrence_controls}, 'cutoffs': records,
              'wall_seconds': time.monotonic()-started}
    np.savez_compressed('kernel_bounds.npz', lower=lo, upper=hi, mu=mu)
    Path('results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('counts', 'prediction', 'first_negative',
          'minimum_upper', 'maximum_lower', 'maximum_interval_width', 'wall_seconds')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
