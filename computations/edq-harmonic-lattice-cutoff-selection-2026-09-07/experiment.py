#!/usr/bin/env python3
"""Frozen same-cutoff test of scalar versus complete harmonic-gcd selection."""
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
ETA = LD('0.005')
MARGIN = LD('1e-7')
BANDS = ((64, 127), (128, 255), (256, 511), (512, 1023))
CHUNK = 131072


def mobius(n):
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


def scan_cutoffs():
    nmax = BANDS[-1][1]
    mu = mobius(nmax)
    b = np.zeros(nmax+1, dtype=LD)
    b[1:] = mu[1:]/np.arange(1, nmax+1, dtype=LD)
    K = np.zeros(nmax+1, dtype=LD)
    harmonic = head_mass = LD(0)
    rows = []
    max_reconstruction_error = LD(0)
    for n in range(1, nmax+1):
        if b[n]:
            gcds = np.gcd(np.arange(1, n, dtype=np.int64), n)
            np.add.at(K, gcds, 2*b[n]*b[1:n])
            K[n] += b[n]**2
        harmonic += b[n]
        head_mass += LD(n)/(n+1)
        error = abs(np.sum(K, dtype=LD)-harmonic**2)
        max_reconstruction_error = max(error, max_reconstruction_error)
        variation = np.sum(abs(K), dtype=LD)
        rows.append({'N': n, 'harmonic': float(harmonic), 'head_mass': float(head_mass),
                     'harmonic_gcd_variation': float(variation),
                     'scalar_score': float(n*harmonic**2),
                     'gcd_score': float(head_mass*variation)})
    assert max_reconstruction_error < LD('1e-14')
    selections = []
    for lo, hi in BANDS:
        rows_in_band = rows[lo-1:hi]
        chosen = {'band': [lo, hi]}
        for kind in ('scalar', 'gcd'):
            ordered = sorted(rows_in_band, key=lambda row: (row[kind+'_score'], row['N']))
            chosen[kind] = dict(ordered[0])
            chosen[kind+'_runner_up_gap'] = ordered[1][kind+'_score']-ordered[0][kind+'_score']
        selections.append(chosen)
    return rows, selections, float(max_reconstruction_error)


def complete_energy(n):
    started = time.monotonic()
    mu = mobius(n)
    d = np.arange(1, n+1, dtype=np.int64)
    b = np.zeros(n+1, dtype=LD)
    b[1:] = mu[1:]/d.astype(LD)
    harmonic = np.sum(b, dtype=LD)
    radius = np.sum(abs(mu[1:])*(1-1/d.astype(LD)), dtype=LD)/2
    mean = np.sum(mu[1:]*(1-1/d.astype(LD)), dtype=LD)/2
    bound = radius+abs(mean)
    terminal = max(n+1, int(np.ceil(bound**2/ETA)))
    assert terminal <= 30000000, ('prefix resource ceiling', n, terminal)
    assert terminal*n < 2**62
    # Exact integer divisor increments and cumulative sum; only final harmonic
    # subtraction and weighted energy are floating point.
    cumulative = np.zeros(terminal+1, dtype=np.int64)
    for q in range(1, n+1):
        if mu[q]:
            cumulative[q::q] += mu[q]
    np.cumsum(cumulative, dtype=np.int64, out=cumulative)
    energy = head = LD(0)
    for lo in range(1, terminal+1, CHUNK):
        hi = min(terminal+1, lo+CHUNK)
        k = np.arange(lo, hi, dtype=LD)
        f = k*harmonic-cumulative[lo:hi]
        terms = f*f/(k*(k+1))
        energy += np.sum(terms, dtype=LD)
        if lo <= n:
            head += np.sum(terms[:min(hi, n+1)-lo], dtype=LD)
    tail_bound = bound**2/(terminal+1)
    assert tail_bound <= ETA
    accumulation_error = LD(0)
    for k in sorted(set((1, n, n+1, 2*n, 3*n, terminal//2, terminal))):
        if k <= terminal:
            direct = np.sum(mu[1:]*(k % d).astype(LD)/d, dtype=LD)
            error = abs(k*harmonic-cumulative[k]-direct)
            accumulation_error = max(accumulation_error, error)
            assert abs(direct) <= bound+LD('1e-12')
    assert accumulation_error < LD('5e-10')
    khead = np.arange(1, n+1, dtype=LD)
    head_mass = np.sum(khead/(khead+1), dtype=LD)
    closed_head = harmonic**2*head_mass-2*harmonic*np.sum(1/(khead+1), dtype=LD)+1-LD(1)/(n+1)
    assert abs(head-closed_head) < LD('1e-13')
    # Independent full divisor inversion of the retained harmonic coefficients.
    J = np.zeros(n+1, dtype=LD)
    for q in range(1, n+1):
        J[q] = np.sum(b[q::q], dtype=LD)
    K = np.zeros(n+1, dtype=LD)
    for r in range(1, n+1):
        K[r] = np.sum(mu[1:n//r+1]*J[r::r]**2, dtype=LD)
    harmonic_variation = np.sum(abs(K), dtype=LD)
    assert abs(np.sum(K, dtype=LD)-harmonic**2) < LD('1e-14')
    return {'N': n, 'seconds': time.monotonic()-started, 'prefix_terminal': terminal,
            'harmonic': float(harmonic), 'head_mass': float(head_mass),
            'harmonic_gcd_variation': float(harmonic_variation),
            'gcd_score': float(head_mass*harmonic_variation),
            'head_energy': float(head), 'complete_energy_lower': float(energy),
            'complete_energy_upper': float(energy+tail_bound),
            'later_tail_lower': float(energy-head), 'later_tail_upper': float(energy-head+tail_bound),
            'analytic_tail_bound': float(tail_bound), 'uniform_residue_bound': float(bound),
            'accumulation_max_error': float(accumulation_error),
            'head_closed_form_error': float(abs(head-closed_head)),
            'harmonic_groups': [{'r': r, 'K': float(K[r]), 'J': float(J[r])} for r in range(1, n+1)]}


def compare(scalar, gcd):
    if scalar['N'] == gcd['N']:
        return 'SAME_CUTOFF'
    if gcd['complete_energy_lower']-float(MARGIN) > scalar['complete_energy_upper']+float(MARGIN):
        return 'PREDICTION_REVERSED'
    if gcd['complete_energy_upper']+float(MARGIN) < scalar['complete_energy_lower']-float(MARGIN):
        return 'PREDICTION_SUPPORTED_FINITE'
    return 'UNRESOLVED_INTERVAL_OVERLAP'


if __name__ == '__main__':
    started = time.monotonic()
    scan, selections, reconstruction = scan_cutoffs()
    cutoffs = sorted(set(s[k]['N'] for s in selections for k in ('scalar', 'gcd')))
    print('Selected cutoffs:', cutoffs, flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        cases = list(pool.map(complete_energy, cutoffs))
    by_cutoff = {case['N']: case for case in cases}
    for selected in selections:
        scalar = by_cutoff[selected['scalar']['N']]
        gcd = by_cutoff[selected['gcd']['N']]
        selected['classification'] = compare(scalar, gcd)
        for kind in ('scalar', 'gcd'):
            case = by_cutoff[selected[kind]['N']]
            assert abs(case['gcd_score']-selected[kind]['gcd_score']) < 1e-12
            selected[kind+'_complete_energy'] = [case['complete_energy_lower'], case['complete_energy_upper']]
            selected[kind+'_head_energy'] = case['head_energy']
            selected[kind+'_later_tail'] = [case['later_tail_lower'], case['later_tail_upper']]
        print(selected, flush=True)
    output = {'protocol': 'same-cutoff scalar versus full harmonic-gcd minimization',
              'python': platform.python_version(), 'numpy': np.__version__,
              'longdouble_mantissa_bits': np.finfo(LD).nmant, 'workers': 8,
              'tail_allowance': float(ETA), 'floating_sensitivity_margin': float(MARGIN),
              'scan_max_reconstruction_error': reconstruction,
              'elapsed_seconds': time.monotonic()-started, 'selections': selections,
              'scan': scan, 'results': cases}
    Path('results.json').write_text(json.dumps(output, indent=2)+'\n')
    print('Elapsed seconds:', output['elapsed_seconds'], flush=True)
