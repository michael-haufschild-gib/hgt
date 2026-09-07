#!/usr/bin/env python3
"""Frozen complete-row variation and parameter-free Bernoulli-mean diagnostic."""
import os
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[name] = '1'
import concurrent.futures
import json
import platform
import time
from pathlib import Path
import numpy as np

LD = np.longdouble
MARGIN = LD('1e-8')
CUTOFFS = (32, 48, 64, 96, 128, 192, 256, 384, 512)
WORKERS = 8


def interval(lo, hi):
    assert lo <= hi
    return {'lower': str(lo), 'upper': str(hi)}


def abs_bounds(lo, hi):
    return np.maximum(np.maximum(lo, -hi), 0), np.maximum(np.abs(lo), np.abs(hi))


def cutoff(n):
    data = np.load('baseline_kernel_bounds.npz')
    baseline = json.loads(Path('baseline_results.json').read_text())['cutoffs'][n-1]
    mu = data['mu'][1:n+1].astype(np.int64)
    d = np.arange(1, n+1, dtype=np.int64)
    lower, upper = data['lower'][1:n+1, 1:n+1], data['upper'][1:n+1, 1:n+1]
    assert lower.dtype == LD and upper.dtype == LD
    hlo = np.sum(np.where(mu[:, None] >= 0, mu[:, None]*lower, mu[:, None]*upper), axis=0, dtype=LD)
    hhi = np.sum(np.where(mu[:, None] >= 0, mu[:, None]*upper, mu[:, None]*lower), axis=0, dtype=LD)
    primitive_one = -(d.astype(LD)-1)/(2*d.astype(LD))
    tlo, thi = primitive_one-hhi, primitive_one-hlo
    sign = -mu
    xlo = np.where(sign >= 0, sign*tlo, sign*thi)
    xhi = np.where(sign >= 0, sign*thi, sign*tlo)
    assert xlo[0] == 0 and xhi[0] == 0
    assert np.all(xlo[mu == 0] == 0) and np.all(xhi[mu == 0] == 0)
    active = (mu != 0) & (d != 1)
    xlo -= MARGIN*active
    xhi += MARGIN*active
    rlo, rhi = np.sum(xlo, dtype=LD), np.sum(xhi, dtype=LD)
    blo, bhi = LD(baseline['flux_lo'])-MARGIN, LD(baseline['flux_hi'])+MARGIN
    assert max(rlo, blo) <= min(rhi, bhi), (n, 'full flux reconstruction')
    assert 0 < rlo
    pi = np.arccos(LD(-1))
    e2 = -LD(1)/4 + pi*pi/32*np.sum(mu[d % 2 == 1]/d[d % 2 == 1].astype(LD)**2, dtype=LD)
    assert xlo[1] <= e2 <= xhi[1], (n, 'modulus two row')
    t2 = 6/(pi*pi)-np.sum(mu/d.astype(LD)**2, dtype=LD)
    mean = pi*pi/72 * mu*d.astype(LD)*t2
    vl, vu = abs_bounds(xlo, xhi)
    vlow, vhigh = np.sum(vl, dtype=LD), np.sum(vu, dtype=LD)
    dl, du = abs_bounds(xlo-mean-MARGIN, xhi-mean+MARGIN)
    dlow, dhigh = np.sum(dl, dtype=LD), np.sum(du, dtype=LD)
    assert vlow > 0
    test_a = 'REVERSED' if vlow > 4*rhi else ('SURVIVES_FINITE_TEST' if vhigh <= 4*rlo else 'UNRESOLVED')
    test_b = 'REVERSED' if dlow > vhigh/4 else ('SURVIVES_FINITE_TEST' if dhigh <= vlow/4 else 'UNRESOLVED')
    rows = [{'e': int(e), 'mu': int(mu[i]), 'actual': interval(xlo[i], xhi[i]),
             'bernoulli_mean': str(mean[i]), 'residual_absolute': interval(dl[i], du[i])}
            for i, e in enumerate(d)]
    return {'n': n, 'flux': interval(rlo, rhi), 'archived_flux': interval(blo, bhi),
            'variation': interval(vlow, vhigh), 'variation_over_flux': interval(vlow/rhi, vhigh/rlo),
            'positive_mass': interval(np.sum(np.maximum(xlo, 0), dtype=LD), np.sum(np.maximum(xhi, 0), dtype=LD)),
            'negative_mass': interval(np.sum(np.maximum(-xhi, 0), dtype=LD), np.sum(np.maximum(-xlo, 0), dtype=LD)),
            'inverse_square_mobius_tail': str(t2), 'bernoulli_mean_total': str(np.sum(mean, dtype=LD)),
            'mean_residual_variation': interval(dlow, dhigh),
            'mean_residual_over_variation': interval(dlow/vhigh, dhigh/vlow),
            'test_A': test_a, 'test_B': test_b,
            'controls': {'full_flux_overlap': True, 'unit_and_zero_mobius_rows': True, 'e2_formula': str(e2)},
            'rows': rows}


def main():
    started = time.monotonic()
    with concurrent.futures.ProcessPoolExecutor(max_workers=WORKERS) as pool:
        records = list(pool.map(cutoff, CUTOFFS))
    result = {'parameters': {'cutoffs': CUTOFFS, 'workers': WORKERS, 'margin': str(MARGIN)},
              'environment': {'python': platform.python_version(), 'numpy': np.__version__,
                              'longdouble_mantissa_bits': np.finfo(LD).nmant},
              'test_counts': {test: {status: sum(r[test] == status for r in records)
                                    for status in ('REVERSED', 'SURVIVES_FINITE_TEST', 'UNRESOLVED')}
                              for test in ('test_A', 'test_B')},
              'cutoffs': records, 'wall_seconds': time.monotonic()-started}
    Path('results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'test_counts': result['test_counts'], 'wall_seconds': result['wall_seconds'],
                      'cutoffs': [{k: v for k, v in r.items() if k != 'rows'} for r in records]}, indent=2), flush=True)


if __name__ == '__main__':
    main()
