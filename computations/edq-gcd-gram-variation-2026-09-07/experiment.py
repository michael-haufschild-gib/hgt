#!/usr/bin/env python3
"""Full-source gcd-group variation; numerical guidance, never a Lean premise."""
import os
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[name] = '1'
import concurrent.futures
import json
import math
import platform
import time
import numpy as np
from scipy.special import zeta

LD = np.longdouble
ORDER = 20
START = 16
ETA = LD('0.05')
CHUNK = 65536


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


def moments_coeff(q):
    x = np.arange(q, dtype=LD)/q
    y = x+LD(1)/q
    out = np.zeros((3, ORDER), dtype=LD)
    poly = np.ones(q, dtype=LD)
    xp = np.ones(q, dtype=LD)
    for j in range(ORDER):
        if j:
            xp *= x
            poly = y*poly+xp
        for l in range(3):
            out[l, j] = np.sum(x**l*poly, dtype=LD)/(LD(q)*q)
    return out


def small_moments(q, t):
    i = np.arange(q, dtype=LD)
    k = LD(q)*t+i
    use = k > 0
    x = i[use]/q
    w = 1/(k[use]*(k[use]+1))
    return np.array([np.sum(x**l*w, dtype=LD) for l in range(3)], dtype=LD)


def series_moments(q, t, coeff):
    z = -1/t
    out = []
    for l in range(3):
        v = np.full(t.shape, coeff[l, -1], dtype=LD)
        for j in range(ORDER-2, -1, -1):
            v = v*z+coeff[l, j]
        out.append(v/(t*t))
    return out


def channel_energy(q, co, blocks, coeff):
    # A(t)=t*H - sum_j co[j]*floor(t/j), formed by an O(B log m) divisor sieve.
    h = np.zeros(blocks, dtype=LD)
    harmonic = LD(0)
    for j in range(1, len(co)):
        if co[j]:
            h[j::j] += co[j]
            harmonic += co[j]/j
    np.cumsum(h, dtype=LD, out=h)
    total = LD(0)
    for lo in range(0, blocks, CHUNK):
        hi = min(blocks, lo+CHUNK)
        t = np.arange(lo, hi, dtype=LD)
        A = t*harmonic-h[lo:hi]
        if q == 1:
            use = t > 0
            total += np.sum(A[use]**2/(t[use]*(t[use]+1)), dtype=LD)
            continue
        early = t < START
        if np.any(early):
            for pos in np.nonzero(early)[0]:
                W = small_moments(q, int(t[pos]))
                total += A[pos]**2*W[0]+2*A[pos]*harmonic*W[1]+harmonic**2*W[2]
        late = ~early
        if np.any(late):
            W = series_moments(q, t[late], coeff)
            Av = A[late]
            terms = Av**2*W[0]+2*Av*harmonic*W[1]+harmonic**2*W[2]
            assert np.min(terms) > -LD('1e-15'), ('negative block', q, float(np.min(terms)))
            total += np.sum(terms, dtype=LD)
    # Independent point evaluation checks accumulation at widely separated blocks.
    error = LD(0)
    for t in sorted(set((0, min(7, blocks-1), blocks//2, blocks-1))):
        direct = sum((co[j]*LD(t % j)/j for j in range(1, len(co))), LD(0))
        error = max(error, abs(LD(t)*harmonic-h[t]-direct))
    assert error < LD('2e-8'), ('accumulation', q, blocks, float(error))
    return total, error


def diagonal_entry(q, coeff):
    if q == 1:
        return LD(0)
    result = sum((small_moments(q, t)[2] for t in range(START)), LD(0))
    for j in range(ORDER):
        result += (-1 if j % 2 else 1)*coeff[2, j]*LD(zeta(j+2, START))
    return result


def controls():
    moment_error = LD(0)
    for q in (2, 3, 7, 31):
        cf = moments_coeff(q)
        for t in (16, 47, 513):
            approx = np.array([w[0] for w in series_moments(q, np.array([t], dtype=LD), cf)])
            exact = small_moments(q, t)
            moment_error = max(moment_error, np.max(abs(approx-exact)/exact))
    assert moment_error < LD('2e-16'), ('moments', float(moment_error))
    mu = mobius(12).astype(LD)
    direct_error = LD(0)
    for q in (1, 2, 3, 5):
        co = np.concatenate((np.zeros(1, dtype=LD), mu[q::q]))
        blocks = 53
        approx, _ = channel_energy(q, co, blocks, moments_coeff(q))
        k = np.arange(1, q*blocks, dtype=np.int64)
        f = np.zeros(len(k), dtype=LD)
        for j in range(1, len(co)):
            f += co[j]*(k % (q*j)).astype(LD)/(q*j)
        exact = np.sum(f*f/(k.astype(LD)*(k+1)), dtype=LD)
        direct_error = max(direct_error, abs(exact-approx))
    assert direct_error < LD('2e-14'), ('direct energy', float(direct_error))
    d2 = diagonal_entry(2, moments_coeff(2))
    assert abs(d2-np.log(LD(2))/4) < LD('2e-16')
    return {'moments_max_relative_error': float(moment_error),
            'direct_energy_max_absolute_error': float(direct_error),
            'diagonal_two_error': float(abs(d2-np.log(LD(2))/4))}


def case_job(spec):
    n, averaged = spec
    started = time.monotonic()
    mu = mobius(n)
    coeff = mu.astype(LD)
    if averaged:
        d = np.arange(1, n+1, dtype=LD)
        coeff[1:] *= np.log(LD(n)/np.maximum(LD(n//4), d))/np.log(LD(4))
    tau = np.zeros(n+1, dtype=np.int64)
    mass = np.zeros(n+1, dtype=LD)
    for q in range(1, n+1):
        tau[q::q] += 1
        mass[q] = np.sum(abs(coeff[q::q]), dtype=LD)
    mass[1] -= abs(coeff[1])  # The unit residue is identically zero.
    aq = tau.astype(LD)*mass**2/np.maximum(np.arange(n+1, dtype=LD), 1)
    allocation = np.sqrt(aq)
    scale = np.sum(allocation, dtype=LD)/ETA
    blocks = np.ceil(scale*allocation).astype(np.int64)
    E = np.zeros(n+1, dtype=LD)
    tail = np.zeros(n+1, dtype=LD)
    diag = LD(0)
    max_accum = LD(0)
    for q in range(1, n+1):
        cf = moments_coeff(q)
        diag += coeff[q]**2*diagonal_entry(q, cf)
        if mass[q] == 0:
            continue
        b = max(START+1, int(blocks[q]))
        co = np.concatenate((np.zeros(1, dtype=LD), coeff[q::q]))
        E[q], err = channel_energy(q, co, b, cf)
        max_accum = max(max_accum, err)
        tail[q] = mass[q]**2/(LD(q)*b)
    assert np.sum(tau*tail, dtype=LD) <= ETA*(1+LD('1e-12'))
    C = np.zeros(n+1, dtype=LD)
    low = C.copy()
    high = C.copy()
    for r in range(1, n+1):
        m = mu[1:n//r+1]
        C[r] = np.sum(m*E[r::r], dtype=LD)
        low[r] = C[r]+np.sum(np.minimum(m, 0)*tail[r::r], dtype=LD)
        high[r] = C[r]+np.sum(np.maximum(m, 0)*tail[r::r], dtype=LD)
    reconstruction = abs(np.sum(C, dtype=LD)-E[1])
    assert reconstruction < LD('1e-12')
    # This allowance is a numerical sensitivity margin, not an interval-arithmetic proof.
    round_margin = LD('1e-7')
    lower_V = np.sum(np.maximum(0, np.maximum(low, -high)), dtype=LD)-round_margin
    upper_V = np.sum(np.maximum(abs(low), abs(high)), dtype=LD)+round_margin
    label = ('GROUPWISE_CANDIDATE' if upper_V < 4*diag-round_margin else
             'JOINT_NEEDED_AT_TESTED_BOUND' if lower_V > 4*diag+round_margin else 'INCONCLUSIVE')
    return {'M': n, 'X': n//4 if averaged else n, 'source': 'averaged' if averaged else 'raw',
            'seconds': time.monotonic()-started, 'classification': label,
            'diagonal': float(diag), 'signed_norm_lower': float(E[1]),
            'signed_norm_upper': float(E[1]+tail[1]),
            'variation_estimate': float(np.sum(abs(C), dtype=LD)),
            'variation_lower': float(lower_V), 'variation_upper': float(upper_V),
            'variation_over_diagonal_lower': float(lower_V/diag),
            'variation_over_diagonal_upper': float(upper_V/diag),
            'sum_weighted_tail_bounds': float(np.sum(tau*tail, dtype=LD)),
            'total_blocks': int(np.sum(blocks)), 'max_accumulation_error': float(max_accum),
            'reconstruction_error': float(reconstruction),
            'groups': [{'r': r, 'value': float(C[r]), 'lower': float(low[r]), 'upper': float(high[r])}
                       for r in range(1, n+1)]}


def main():
    started = time.monotonic()
    control = controls()
    specs = [(n, a) for n in (64, 128, 256, 512) for a in (False, True)]
    results = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        for result in pool.map(case_job, specs):
            results.append(result)
            print(json.dumps({k:v for k,v in result.items() if k != 'groups'}), flush=True)
    output = {'protocol': 'frozen before execution; full-source analytic tail bounds; no Lean input',
              'python': platform.python_version(), 'numpy': np.__version__,
              'longdouble_mantissa_bits': np.finfo(LD).nmant, 'workers': 8,
              'series_order': ORDER, 'series_start': START, 'tail_budget': float(ETA),
              'controls': control, 'elapsed_seconds': time.monotonic()-started, 'results': results}
    with open('results.json', 'w') as f:
        json.dump(output, f, indent=2)
    print('COMPLETE', output['elapsed_seconds'], flush=True)

if __name__ == '__main__':
    main()
