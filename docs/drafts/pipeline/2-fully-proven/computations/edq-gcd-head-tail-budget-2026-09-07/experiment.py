#!/usr/bin/env python3
"""Frozen head/tail budget diagnostic; numerical guidance, never a Lean premise."""
import os
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[name] = '1'
import concurrent.futures
import hashlib
import json
import platform
import time
from pathlib import Path
import numpy as np

LD = np.longdouble
MARGIN = LD('1e-7')


def mobius(n):
    # Same sieve as the archived full-source experiment.
    mu = np.ones(n+1, dtype=np.int64)
    prime = np.ones(n+1, dtype=bool)
    prime[:2] = False
    for p in range(2, n+1):
        if prime[p]:
            mu[p::p] *= -1
            mu[p*p::p*p] = 0
            prime[p*p::p] = False
    mu[0] = 0
    return mu


def abs_bounds(lo, hi):
    assert lo <= hi
    return max(LD(0), lo, -hi), max(abs(lo), abs(hi))


def classify(lo, hi, diagonal):
    if hi + MARGIN <= 4*diagonal:
        return 'PASS_FINITE'
    if lo - MARGIN > 4*diagonal:
        return 'FAIL_FINITE'
    return 'UNRESOLVED_NUMERICAL'


def case_job(previous):
    started = time.monotonic()
    n, x = previous['M'], previous['X']
    mu = mobius(n)
    co = mu.astype(LD)
    d = np.arange(1, n+1, dtype=np.int64)
    k = np.arange(1, x+1, dtype=np.int64)
    if previous['source'] == 'averaged':
        co[1:] *= np.log(LD(n)/np.maximum(LD(x), d.astype(LD)))/np.log(LD(4))
    residue = co[1:, None]*(k[None, :] % d[:, None]).astype(LD)/d[:, None]
    w = 1/(k.astype(LD)*(k+1))
    channels = np.zeros(n+1, dtype=LD)
    harmonic_channels = np.zeros(n+1, dtype=LD)
    for q in range(1, n+1):
        f = np.sum(residue[q-1::q], axis=0, dtype=LD)
        channels[q] = np.sum(f*f*w, dtype=LD)
        harmonic_channels[q] = np.sum(co[q::q]/d[q-1::q], dtype=LD)
    heads = np.zeros(n+1, dtype=LD)
    harmonic_groups = np.zeros(n+1, dtype=LD)
    for r in range(1, n+1):
        c = mu[1:n//r+1]
        heads[r] = np.sum(c*channels[r::r], dtype=LD)
        harmonic_groups[r] = np.sum(c*harmonic_channels[r::r]**2, dtype=LD)
    head_mass = np.sum(k.astype(LD)/(k+1), dtype=LD)
    polynomials = harmonic_groups*head_mass
    f = np.sum(residue, axis=0, dtype=LD)
    literal_error = np.max(abs(f-(k*harmonic_channels[1]-1)))
    energy_error = abs(np.sum(heads, dtype=LD)-np.sum(f*f*w, dtype=LD))
    harmonic_error = abs(np.sum(harmonic_groups, dtype=LD)-harmonic_channels[1]**2)
    assert max(literal_error, energy_error, harmonic_error) < LD('1e-12')
    gcd_error = LD(0)
    if n == 64:
        gram = (residue*w) @ residue.T
        gcds = np.gcd(d[:, None], d[None, :])
        for r in range(1, n+1):
            direct = np.sum(gram[gcds == r], dtype=LD)
            gcd_error = max(gcd_error, abs(direct-heads[r]))
        assert gcd_error < LD('1e-12')
    groups = []
    tail_abs_lo = tail_abs_hi = LD(0)
    assert len(previous['groups']) == n
    for item in previous['groups']:
        r = item['r']
        tail_lo, tail_hi = LD(item['lower'])-heads[r], LD(item['upper'])-heads[r]
        a, b = abs_bounds(tail_lo, tail_hi)
        tail_abs_lo += a
        tail_abs_hi += b
        groups.append({'r': r, 'head': float(heads[r]),
                       'harmonic_coefficient': float(harmonic_groups[r]),
                       'polynomial': float(polynomials[r]),
                       'corrected_head': float(heads[r]-polynomials[r]),
                       'tail_lower': float(tail_lo), 'tail_upper': float(tail_hi),
                       'complete_lower': item['lower'], 'complete_upper': item['upper']})
    head_abs = np.sum(abs(heads), dtype=LD)
    polynomial_abs = np.sum(abs(polynomials), dtype=LD)
    corrected_abs = np.sum(abs(heads-polynomials), dtype=LD)
    diagonal = LD(previous['diagonal'])
    a_lo, a_hi = head_abs+tail_abs_lo, head_abs+tail_abs_hi
    b_lo, b_hi = polynomial_abs+corrected_abs+tail_abs_lo, polynomial_abs+corrected_abs+tail_abs_hi
    return {'M': n, 'X': x, 'source': previous['source'], 'seconds': time.monotonic()-started,
            'diagonal': float(diagonal), 'head_signed_sum': float(np.sum(heads, dtype=LD)),
            'head_abs_sum': float(head_abs), 'polynomial_abs_sum': float(polynomial_abs),
            'corrected_head_abs_sum': float(corrected_abs),
            'tail_abs_sum_lower': float(tail_abs_lo), 'tail_abs_sum_upper': float(tail_abs_hi),
            'test_A': {'classification': classify(a_lo, a_hi, diagonal),
                       'lower_over_D': float(a_lo/diagonal), 'upper_over_D': float(a_hi/diagonal)},
            'test_B': {'classification': classify(b_lo, b_hi, diagonal),
                       'lower_over_D': float(b_lo/diagonal), 'upper_over_D': float(b_hi/diagonal)},
            'controls': {'literal_source_error': float(literal_error),
                         'head_energy_error': float(energy_error),
                         'harmonic_reconstruction_error': float(harmonic_error),
                         'direct_gcd_error_M64': float(gcd_error) if n == 64 else None},
            'groups': groups}


if __name__ == '__main__':
    started = time.monotonic()
    source = Path('full_source_results.json')
    previous = json.loads(source.read_text())
    assert sorted((c['M'], c['source']) for c in previous['results']) == [
        (n, s) for n in (64, 128, 256, 512) for s in ('averaged', 'raw')]
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        cases = list(pool.map(case_job, previous['results']))
    output = {'protocol': 'head/tail and quadratic budget, eight frozen existing sources',
              'input_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'python': platform.python_version(), 'numpy': np.__version__,
              'longdouble_mantissa_bits': np.finfo(LD).nmant, 'workers': 8,
              'floating_sensitivity_margin': float(MARGIN),
              'elapsed_seconds': time.monotonic()-started, 'results': cases}
    Path('results.json').write_text(json.dumps(output, indent=2)+'\n')
    for c in cases:
        print(c['M'], c['source'], 'A', c['test_A'], 'B', c['test_B'], flush=True)
    print('Elapsed seconds:', output['elapsed_seconds'], flush=True)
