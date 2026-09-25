"""RunPod-only diagnostic; finite energies, never a proof certificate."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[key] = '1'
import concurrent.futures as cf
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import platform
import time
import numpy as np

MU = HARM = MERTENS = None


def source(maximum):
    mu = np.ones(maximum + 1, dtype=np.int8)
    mu[0] = 0
    prime = np.ones(maximum + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, maximum + 1):
        if prime[p]:
            prime[p*p::p] = False
            mu[p::p] *= -1
            mu[p*p::p*p] = 0
    harmonic = np.zeros(maximum + 1, dtype=np.longdouble)
    harmonic[1:] = np.cumsum(mu[1:].astype(np.longdouble) /
                            np.arange(1, maximum + 1, dtype=np.longdouble))
    return mu, harmonic, np.cumsum(mu, dtype=np.int64)


def energy(cumulative, h, lo, hi):
    raw = err = np.longdouble(0)
    for start in range(lo, hi + 1, 262144):
        stop = min(start + 262144, hi + 1)
        n = np.arange(start, stop, dtype=np.longdouble)
        f = cumulative[start:stop].astype(np.longdouble) - n*h
        w = 1/(n*(n+1))
        raw += np.sum(f*f*w, dtype=np.longdouble)
        err += np.sum((1-f)*(1-f)*w, dtype=np.longdouble)
    return {'lo': lo, 'hi': hi, 'raw_energy': float(raw), 'error_energy': float(err)}


def work(n):
    started = time.monotonic()
    terminal = 128*n
    cumulative = np.zeros(terminal + 1, dtype=np.int64)
    for d in range(1, n + 1):
        if MU[d]:
            cumulative[d::d] += int(MU[d])
    np.cumsum(cumulative, out=cumulative)
    assert np.all(cumulative[1:n+1] == 1)
    # On N < k <= 2N, omitted floors equal one exactly.
    assert np.array_equal(1 - cumulative[n+1:2*n+1],
                          MERTENS[n+1:2*n+1] - MERTENS[n])
    moduli = np.arange(1, n + 1, dtype=np.int64)
    direct_checks = {}
    for k in sorted({1, n, n+1, 2*n, 3*n+7, terminal}):
        direct = int(np.sum(MU[1:n+1].astype(np.int64)*(k//moduli), dtype=np.int64))
        assert direct == int(cumulative[k])
        direct_checks[str(k)] = direct
    h = HARM[n]
    compensated = math.fsum(int(MU[d])/d for d in range(1, n+1))
    discrepancy = abs(float(h)-compensated)
    assert discrepancy < 1e-14
    blocks = [energy(cumulative, h, 1, n)]
    for j in range(7):
        blocks.append(energy(cumulative, h, (2**j)*n+1, (2**(j+1))*n))
    exact_head = h*h*np.sum(np.arange(1, n+1, dtype=np.longdouble) /
                           np.arange(2, n+2, dtype=np.longdouble), dtype=np.longdouble)
    head_error = abs(blocks[0]['error_energy']-float(exact_head))
    assert head_error < 1e-12*(1+float(exact_head))
    return {'N': n, 'H': float(h), 'sqrt_N_H': float(np.sqrt(np.longdouble(n))*h),
            'initial_scalar_predictor': float(n*h*h), 'blocks': blocks,
            'finite_raw_energy': sum(b['raw_energy'] for b in blocks),
            'finite_error_energy': sum(b['error_energy'] for b in blocks),
            'tail_error_energy': sum(b['error_energy'] for b in blocks[1:]),
            'omitted_raw_upper': n*n/(terminal+1),
            'omitted_error_upper': (n+1)**2/(terminal+1),
            'validation': {'direct_floor_sums': direct_checks,
                           'first_block_integer_identity_all_coordinates': True,
                           'compensated_H_difference': discrepancy,
                           'head_energy_identity_difference': head_error},
            'seconds': time.monotonic()-started}


def main():
    global MU, HARM, MERTENS
    started = time.monotonic()
    MU, HARM, MERTENS = source(2**18)
    design = []
    for k in range(10, 17):
        lo, hi = 2**k, 2**(k+1)
        size = np.arange(lo, hi, dtype=np.longdouble)
        score = np.sqrt(size)*np.abs(HARM[lo:hi])
        crossing = np.flatnonzero(HARM[lo-1:hi-1]*HARM[lo:hi] <= 0)+lo
        design.append({'k': k, 'minimum': lo+int(np.argmin(score)),
                       'maximum': lo+int(np.argmax(score)), 'midpoint': 3*2**(k-1),
                       'harmonic_crossings': crossing.tolist()})
    cutoffs = sorted({item[key] for item in design for key in ('minimum', 'maximum', 'midpoint')})
    Path('design.json').write_text(json.dumps(design, indent=2)+'\n')
    rows = []
    with cf.ProcessPoolExecutor(max_workers=8, mp_context=mp.get_context('fork')) as pool:
        for row in pool.map(work, cutoffs):
            rows.append(row)
            print(json.dumps({'finished_N': row['N'], 'seconds': row['seconds']}), flush=True)
    by_n = {row['N']: row for row in rows}
    comparisons = []
    for item in design:
        near = by_n[item['minimum']]
        middle = by_n[item['midpoint']]
        comparisons.append({'k': item['k'], 'minimum_N': near['N'], 'midpoint_N': middle['N'],
                            'tail_ratio': near['tail_error_energy']/middle['tail_error_energy'],
                            'initial_predictor_ratio': near['initial_scalar_predictor']/middle['initial_scalar_predictor']})
    ratios = [row['tail_ratio'] for row in comparisons]
    classification = ('consistent finite suppression' if all(r < 0.1 for r in ratios) else
                      'persistent complementary tail' if sum(r > 0.5 for r in ratios) >= 4 else 'mixed')
    metadata = {'seconds': time.monotonic()-started, 'workers': 8, 'cpus': os.cpu_count(),
                'python': platform.python_version(), 'numpy': np.__version__,
                'longdouble_bits': np.finfo(np.longdouble).bits,
                'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'classification': classification}
    Path('results.json').write_text(json.dumps({'metadata': metadata, 'design': design,
                                               'comparisons': comparisons, 'rows': rows}, indent=2)+'\n')
    print(json.dumps(metadata), flush=True)


if __name__ == '__main__':
    main()
