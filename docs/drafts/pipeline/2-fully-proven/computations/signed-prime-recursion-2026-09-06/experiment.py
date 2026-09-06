"""Run remotely. Signed arithmetic diagnostics; no proof certificates."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import argparse
import json
import math
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import numpy as np


def primes_to(n):
    mask = np.ones(n + 1, dtype=bool)
    mask[:2] = False
    for p in range(2, math.isqrt(n) + 1):
        if mask[p]:
            mask[p*p::p] = False
    return np.flatnonzero(mask)


def run_case(args):
    name, seed, top_power = args
    start = time.monotonic()
    nmax = 2**top_power
    primes = primes_to(nmax)
    rng = np.random.default_rng(seed)
    signs = (-np.ones(len(primes), dtype=np.int8) if name == 'liouville'
             else np.ones(len(primes), dtype=np.int8) if name == 'ones'
             else rng.choice(np.array([-1, 1], dtype=np.int8), len(primes)))
    f = np.ones(nmax + 1, dtype=np.int8)
    f[0] = 0
    for pp, sign in zip(primes, signs):
        if sign == 1:
            continue
        p = int(pp)
        pk = p
        while pk <= nmax:
            f[pk::pk] *= -1
            pk *= p
    # Independent short-prefix smallest-prime-factor reconstruction.
    lim = min(10000, nmax)
    spf = np.arange(lim + 1)
    for p in primes[primes <= math.isqrt(lim)]:
        target = spf[p*p::p]
        ix = np.arange(p*p, lim + 1, p)
        target[target == ix] = p
    check = np.ones(lim + 1, dtype=np.int8)
    for n in range(2, lim + 1):
        check[n] = f[spf[n]] * check[n // spf[n]]
    if not np.array_equal(check[1:], f[1:lim+1]):
        raise RuntimeError('independent multiplicativity check failed')
    sums = np.cumsum(f, dtype=np.int64)
    logs = np.log(np.arange(1, nmax+1, dtype=np.float64))
    weighted = np.concatenate(([0.0], np.cumsum(f[1:] * logs)))
    prime_logs = np.log(primes)
    powers, power_weights, parity = [], [], []
    for pp, sign in zip(primes[primes <= math.isqrt(nmax)], signs):
        p, k = int(pp), 2
        pk = p*p
        while pk <= nmax:
            powers.append(pk)
            power_weights.append(math.log(p) * int(sign)**k)
            parity.append(k % 2)
            pk *= p
            k += 1
    powers = np.array(powers, dtype=np.int64)
    power_weights = np.array(power_weights)
    parity = np.array(parity)
    cutoffs = sorted(set([int(2**k * frac) for k in range(12, top_power)
                          for frac in (1, 1.25, 1.5, 1.75)] + [nmax]))
    rows = []
    for n in cutoffs:
        ix = np.searchsorted(primes, n, side='right')
        prime = float(np.sum(prime_logs[:ix] * signs[:ix] * sums[n // primes[:ix]]))
        vals = power_weights * sums[n // powers]
        even = float(np.sum(vals[parity == 0]))
        odd = float(np.sum(vals[parity == 1]))
        elog = float(sums[n] * math.log(n) - weighted[n])
        residual = float(weighted[n] - prime - even - odd)
        scale = 1 + abs(float(weighted[n])) + abs(prime) + abs(even) + abs(odd)
        if abs(residual) > 1e-9 * scale:
            raise RuntimeError(('recursion check failed', name, n, residual, scale))
        defect = elog + even + odd
        rows.append(dict(n=n, S=int(sums[n]), Elog=elog, Eeven=even, Eodd=odd,
                         P=prime, defect=defect, identity_residual=residual,
                         retained_fraction=abs(defect)/(abs(elog)+abs(even+odd)+1e-300)))
    return dict(name=name, seed=seed, seconds=time.monotonic()-start, rows=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--power', type=int, default=21)
    parser.add_argument('--output', default='results.json')
    args = parser.parse_args()
    start = time.monotonic()
    jobs = [('liouville', 0, args.power), ('ones', 0, args.power)] + [
        ('random_%d' % j, 94001+j, args.power) for j in range(7)]
    with ProcessPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run_case, jobs))
    out = dict(top_power=args.power, seconds=time.monotonic()-start,
               numpy=np.__version__, results=results)
    Path(args.output).write_text(json.dumps(out, indent=2))
    for case in results:
        row=case['rows'][-1]
        root=math.sqrt(row['n'])
        print(case['name'], 'S/root=%.5f'% (row['S']/root),
              'Elog/root=%.5f'%(row['Elog']/root),
              'Epp/root=%.5f'%((row['Eeven']+row['Eodd'])/root),
              'retained=%.5f'%row['retained_fraction'], flush=True)
    print('elapsed', out['seconds'], flush=True)
