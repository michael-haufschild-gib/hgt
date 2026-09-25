#!/usr/bin/env python3
"""Frozen reduced-denominator attribution of EDQ ratio bands."""
import os
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[name] = '1'
import concurrent.futures
import json
import math
import time
from pathlib import Path
import numpy as np
from experiment import LD, MARGIN, CUTOFFS, inputs, lifted_kernel, mobius, record_interval, signed_sum

BCUTS = (2, 4, 8, 16, 32)
BANDS = ((16, 32), (32, 64))


def ray_band(n, left, right, bmax, lo, hi, mu):
    lower, upper = LD(0), LD(0)
    for b in range(2, min(n, bmax)+1):
        if mu[b] == 0:
            continue
        for a in range(left*b+1, right*b+1):
            if mu[a] == 0 or math.gcd(a, b) != 1:
                continue
            r = np.arange(n//a+1, n//b+1, dtype=np.int64)
            mask = np.gcd(r, a*b) == 1
            mass = np.sum((mu[r]**2*mask).astype(LD)/r.astype(LD), dtype=LD)
            kl, ku = lifted_kernel(np.array([a], dtype=np.int64), b, lo, hi)
            weight = -LD(mu[a]*mu[b])*mass
            lower += weight*(kl[0] if weight >= 0 else ku[0])
            upper += weight*(ku[0] if weight >= 0 else kl[0])
    return lower-MARGIN, upper+MARGIN


def literal_band(n, left, right, lo, hi, mu):
    lower, upper = LD(0), LD(0)
    for e in range(1, n+1):
        d = np.arange(max(n, left*e)+1, right*e+1, dtype=np.int64)
        kl, ku = lifted_kernel(d, e, lo, hi)
        a, b = signed_sum(-mu[d]*mu[e], kl, ku)
        lower += a
        upper += b
    return lower-MARGIN, upper+MARGIN


def one_cutoff(n):
    lo, hi, _, _ = inputs()
    data = json.loads(Path('results.json').read_text())
    base = next(x for x in data['cutoffs'] if x['n'] == n)
    mu = mobius(64*max(n, 32))
    bands = []
    for left, right in BANDS:
        row = next(x for x in base['ratios'] if x['ratio'] == right)
        target = row['band']
        tlo, thi = LD(target['lower']), LD(target['upper'])
        minabs, maxabs = max(tlo, -thi, LD(0)), max(abs(tlo), abs(thi))
        assert minabs > 0
        cuts = []
        for bmax in BCUTS:
            lower, upper = ray_band(n, left, right, bmax, lo, hi, mu)
            elo, ehi = tlo-upper, thi-lower
            lowabs, highabs = max(elo, -ehi, LD(0)), max(abs(elo), abs(ehi))
            cuts.append({'bmax': bmax, 'selected': record_interval(lower, upper),
                         'full_remainder': record_interval(elo, ehi),
                         'relative_error': record_interval(lowabs/maxabs, highabs/minabs)})
        control = None
        if n in (32, 96):
            rlo, rhi = ray_band(n, left, right, n, lo, hi, mu)
            llo, lhi = literal_band(n, left, right, lo, hi, mu)
            assert max(tlo, rlo, llo) <= min(thi, rhi, lhi)+MARGIN
            control = {'all_rays': record_interval(rlo, rhi),
                       'literal': record_interval(llo, lhi)}
        bands.append({'left': left, 'right': right, 'full_band': target,
                      'cuts': cuts, 'control': control})
    return {'n': n, 'bands': bands}


def validate():
    lo, hi, _, _ = inputs()
    mu = mobius(1024)
    count = 0
    for a in range(1, 65):
        for b in range(1, 17):
            if math.gcd(a, b) != 1:
                continue
            ka, kb = lifted_kernel(np.array([a], dtype=np.int64), b, lo, hi)
            for r in range(1, 17):
                left = int(mu[r*a]*mu[r*b])
                right = int(mu[a]*mu[b]*mu[r]**2)*(math.gcd(r, a*b) == 1)
                assert left == right
                ra, rb = lifted_kernel(np.array([r*a], dtype=np.int64), r*b, lo, hi)
                assert max(ra[0], ka[0]/r) <= min(rb[0], kb[0]/r)+MARGIN
                count += 1
    return count


def main():
    started = time.monotonic()
    count = validate()
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        records = list(pool.map(one_cutoff, CUTOFFS))
    primary = [band['cuts'][1]['relative_error'] for row in records for band in row['bands']]
    survived = all(LD(x['upper']) <= LD(1)/4 for x in primary)
    failed = any(LD(x['lower']) > LD(1)/4 for x in primary)
    result = {'parameters': {'cutoffs': CUTOFFS, 'bmax_values': BCUTS, 'bands': BANDS,
                             'workers': 8, 'floating_margin': str(MARGIN)},
              'prediction': 'REVERSED' if failed else ('SURVIVES_FINITE_TEST' if survived else 'UNRESOLVED'),
              'homothety_checks': count, 'cutoffs': records,
              'wall_seconds': time.monotonic()-started}
    Path('ray_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('prediction', 'homothety_checks', 'wall_seconds')}, indent=2), flush=True)
    for row in records:
        print(json.dumps({'n': row['n'], 'primary': [b['cuts'][1] for b in row['bands']]}), flush=True)


if __name__ == '__main__':
    main()
