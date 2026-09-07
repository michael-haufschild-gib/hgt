"""RunPod-only diagnostic of the fixed-reserve middle-prime field; never Lean input."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import csv
import json
import math
import multiprocessing as mp
from pathlib import Path
import time
import numpy as np

LIMIT = 2**20
CUTOFFS = sorted({2**k for k in range(10, 21)} | {5*2**k//4 for k in range(10, 20)})
GAMMA = np.longdouble('0.577215664901532860606512090082402431')
OUT = Path(__file__).resolve().parent


def prepare():
    global MU, PRIMES, ISPRIME, DEFECT, PREFIX
    tau = np.zeros(LIMIT+1, dtype=np.int32)
    for d in range(1, LIMIT+1):
        tau[d::d] += 1
    sieve = np.ones(LIMIT+1, dtype=bool)
    sieve[:2] = False
    for p in range(2, math.isqrt(LIMIT)+1):
        if sieve[p]:
            sieve[p*p::p] = False
    PRIMES = np.flatnonzero(sieve)
    ISPRIME = sieve
    MU = np.ones(LIMIT+1, dtype=np.int8)
    MU[0] = 0
    for p in PRIMES:
        MU[p::p] *= -1
        if p*p <= LIMIT:
            MU[p*p::p*p] = 0
    n = np.arange(1, LIMIT+1, dtype=np.longdouble)
    DEFECT = np.zeros(LIMIT+1, dtype=np.longdouble)
    DEFECT[1:] = np.cumsum(np.log(n)) - np.cumsum(tau[1:], dtype=np.int64) + 2*GAMMA*n
    PREFIX = np.zeros(LIMIT+2, dtype=np.longdouble)
    PREFIX[2:] = np.cumsum(DEFECT[1:] / (np.sqrt(n+1)+np.sqrt(n)))


def run_cutoff(M):
    started = time.monotonic()
    d = np.arange(1, M, dtype=np.int64)
    d = d[MU[1:M] != 0]
    q = M//d
    values = np.sqrt(d.astype(np.longdouble))*PREFIX[q] + (
        np.sqrt(np.longdouble(M))-np.sqrt((d*q).astype(np.longdouble)))*DEFECT[q]
    # Oriented coefficients v_R=(-1)^|R| F(R); squared energies unchanged.
    v = np.zeros(M, dtype=np.longdouble)
    v[d] = values
    active = d
    E0 = np.sum(values*values)
    stages = []
    reserve_sq = np.longdouble(0)
    reserve_pos = np.longdouble(0)
    reserve_neg = np.longdouble(0)
    previous = None
    max_pair_error = np.longdouble(0)
    largest_step = None
    for p in PRIMES[PRIMES <= math.isqrt(M-1)]:
        old_v = np.sum(v[active[active != 1]]**2)
        keep = active[active % p != 0]
        paired = keep[keep*p < M]
        # All surviving active labels are squarefree and have processed primes removed.
        overlap_nonempty = np.sum(v[paired[paired != 1]]*v[p*paired[paired != 1]])
        singleton = v[p]
        predicted_delta = -2*overlap_nonempty-singleton**2
        witness = None
        if p > 7 and (largest_step is None or predicted_delta > largest_step['gain']):
            labels = paired[paired != 1]
            contributions = -2*v[labels]*v[p*labels]
            take = min(12, len(labels))
            top = np.argsort(contributions)[-take:][::-1] if take else []
            witness = [dict(label=int(labels[j]), parent=float(v[labels[j]]),
                            partner=float(v[p*labels[j]]), contribution=float(contributions[j]))
                       for j in top]
        v[paired] -= v[p*paired]
        removed = active[active % p == 0]
        v[removed] = 0
        active = keep
        head = v[1]
        nonempty = np.sum(v[active[active != 1]]**2)
        error = abs((nonempty-old_v)-predicted_delta)
        max_pair_error = max(max_pair_error, error)
        if p == 7:
            rp = PRIMES[(PRIMES < M) & (8*PRIMES > M)]
            # Prime labels have odd parity: signed singleton is -v[p].
            signed = -v[rp]
            reserve_sq = np.sum(signed**2)
            reserve_pos = np.sum(signed[signed > 0])
            reserve_neg = np.sum(-signed[signed < 0])
        if p >= 7:
            remainder = nonempty-reserve_sq
            row = dict(M=M, p=int(p), head=float(head), nonempty=float(nonempty),
                       remainder=float(remainder), remainder_over_initial=float(remainder/E0),
                       nonscalar=float(np.sum(v[active[(active > 1) & ~ISPRIME[active]]]**2)),
                       remainder_over_M2=float(remainder/(M*M)),
                       delta_nonempty=float(nonempty-old_v),
                       mixed_nonempty=float(overlap_nonempty),
                       singleton_oriented=float(singleton),
                       reserve_square=float(reserve_sq),
                       reserve_positive_mass=float(reserve_pos),reserve_negative_mass=float(reserve_neg))
            if previous is not None:
                gain = remainder-previous
                row['delta_remainder'] = float(gain)
                if largest_step is None or gain > largest_step['gain']:
                    largest_step = dict(gain=float(gain), p=int(p), before=float(previous),
                                        after=float(remainder), leading_mixed_pairs=witness)
            else:
                row['delta_remainder'] = None
            previous = remainder
            stages.append(row)
    summary = dict(M=M, initial=float(E0), initial_over_M2=float(E0/(M*M)),
                   maximum_remainder_over_initial=max(r['remainder_over_initial'] for r in stages),
                   maximum_remainder_over_M2=max(r['remainder_over_M2'] for r in stages),
                   core_remainder=stages[0]['remainder'], terminal_remainder=stages[-1]['remainder'],
                   largest_step=largest_step, growing_middle_steps=sum(r['delta_remainder'] is not None and r['delta_remainder'] > 1e-12*max(1, float(E0)) for r in stages),
                   maximum_nonscalar_over_M2=max(r['nonscalar']/(M*M) for r in stages),
                   max_energy_identity_error=float(max_pair_error),
                   seconds=time.monotonic()-started)
    return summary, stages


if __name__ == '__main__':
    started = time.monotonic()
    prepare()
    workers = min(8, os.cpu_count() or 1, len(CUTOFFS))
    with mp.get_context('fork').Pool(workers) as pool:
        result = list(pool.imap_unordered(run_cutoff, CUTOFFS))
    result.sort(key=lambda x: x[0]['M'])
    rows = [row for _, stages in result for row in stages]
    with (OUT/'stages.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    summary = dict(question='Fixed-isolated-reserve projection under increasing middle-prime processing',
                   cutoff_list=CUTOFFS, workers=workers, numpy=np.__version__,
                   precision='numpy.longdouble', seconds=time.monotonic()-started,
                   results=[s for s, _ in result])
    (OUT/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    lines = ['# Middle-prime fixed-reserve diagnostic', '',
             f'Workers: {workers}; runtime: {summary["seconds"]:.3f} seconds; precision: long double.', '',
             '| M | max residual / initial | max residual / M² | max nonscalar / M² | growing steps |',
             '|---:|---:|---:|---:|---:|']
    for r in summary['results']:
        lines.append(f'| {r["M"]} | {r["maximum_remainder_over_initial"]:.10g} | {r["maximum_remainder_over_M2"]:.10g} | {r["maximum_nonscalar_over_M2"]:.10g} | {r["growing_middle_steps"]} |')
    lines += ['', 'Every stage was retained in stages.csv. Leading signed pair contributions are in summary.json.',
              'Finite floating-point evidence only; no all-cutoff theorem or Lean premise.']
    (OUT/'report.md').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines), flush=True)
