"""Frozen finite-profile diagnostic. RunPod only; no output is a Lean premise."""
import os
for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import csv
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import signal
import time
import numpy as np
from scipy.optimize import linprog
import mpmath as mm

ROOT = Path(__file__).resolve().parent
EXPECTED = 'a8c93dfaec636b6f993f1e676e1e9ea744b699273cd66b0644afca4ffee8393d'


def deadline(signum, frame):
    raise TimeoutError('Frozen 50-second deadline reached')


def reconstruct(cutoff):
    mm.mp.dps = 80
    tau = [0] * (cutoff + 1)
    mu = [1] * (cutoff + 1)
    prime = [True] * (cutoff + 1)
    prime[:2] = [False, False]
    for divisor in range(1, cutoff + 1):
        for multiple in range(divisor, cutoff + 1, divisor):
            tau[multiple] += 1
    for p in range(2, cutoff + 1):
        if prime[p]:
            for multiple in range(p, cutoff + 1, p):
                mu[multiple] *= -1
            for multiple in range(p * p, cutoff + 1, p * p):
                mu[multiple] = 0
            for multiple in range(p * p, cutoff + 1, p):
                prime[multiple] = False
    defect = [mm.mpf(0)] * (cutoff + 1)
    abel = [mm.mpf(0)] * (cutoff + 2)
    log_sum, tau_sum = mm.mpf(0), 0
    for n in range(1, cutoff + 1):
        log_sum += mm.log(n)
        tau_sum += tau[n]
        defect[n] = log_sum - tau_sum + 2 * mm.euler * n
        abel[n + 1] = abel[n] + defect[n] / (mm.sqrt(n + 1) + mm.sqrt(n))
    odd, even = mm.mpf(0), mm.mpf(0)
    for divisor in range(1, cutoff):
        q = cutoff // divisor
        value = mu[divisor] * (mm.sqrt(divisor) * abel[q]
            + (mm.sqrt(cutoff) - mm.sqrt(q * divisor)) * defect[q])
        if divisor % 2:
            odd += value
        else:
            even += value
    return dict(K=cutoff, head=str(odd), two=str(even),
                u=[str(odd / mm.sqrt(cutoff)), str(even / mm.sqrt(cutoff))])


def main():
    started = time.monotonic()
    signal.signal(signal.SIGALRM, deadline)
    signal.alarm(50)
    source = ROOT / 'profiles.csv'
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    assert digest == EXPECTED, digest
    with source.open() as handle:
        rows = list(csv.DictReader(handle))
    assert [int(row['K']) for row in rows] == list(range(2, 513))
    points = np.array([[float(row['head']), float(row['two'])] for row in rows])
    points /= np.sqrt(np.arange(2, 513))[:, None]
    objective = 2 * points[:, 0] * points[:, 1]
    equalities = np.vstack([np.ones(len(rows)), points.T])
    result = linprog(-objective, A_eq=equalities, b_eq=[1, 0, 0],
                     bounds=(0, None), method='highs',
                     options={'time_limit': 20, 'threads': 1})
    summary = dict(input_sha256=digest, cutoffs=[2, 512],
                   status=int(result.status), message=result.message,
                   success=bool(result.success), workers=min(8, os.cpu_count() or 1),
                   numpy=np.__version__)
    if result.success:
        support = np.flatnonzero(result.x > 1e-9)
        summary.update(optimum=float(-result.fun),
            nonzero_weights=[dict(K=i + 2, weight=float(w)) for i, w in enumerate(result.x) if w != 0],
            support=[int(i + 2) for i in support],
            equality_residual=(equalities @ result.x - np.array([1, 0, 0])).tolist(),
            minimization_dual=result.eqlin.marginals.tolist(),
            minimum_reduced_cost=float(np.min(result.lower.marginals)))
        with mp.get_context('fork').Pool(min(summary['workers'], len(support))) as pool:
            exact_rows = pool.map(reconstruct, [int(i + 2) for i in support])
        summary['independent_80_digit_profiles'] = exact_rows
        mm.mp.dps = 80
        if len(exact_rows) == 3:
            vectors = [[mm.mpf(x) for x in row['u']] for row in exact_rows]
            def cross(a, b):
                return a[0] * b[1] - a[1] * b[0]
            weights = [cross(vectors[1], vectors[2]), cross(vectors[2], vectors[0]),
                       cross(vectors[0], vectors[1])]
            total = sum(weights)
            if total != 0:
                weights = [weight / total for weight in weights]
                margin = sum(2 * weight * v[0] * v[1] for weight, v in zip(weights, vectors))
                residuals = [sum(weight * v[j] for weight, v in zip(weights, vectors)) for j in range(2)]
                summary['independent_circuit'] = dict(weights=[str(w) for w in weights],
                    balance_residuals=[str(x) for x in residuals], quadratic_margin=str(margin),
                    all_weights_positive=bool(min(weights) > 0),
                    near_degenerate=bool(min(abs(total), abs(margin), *(abs(w) for w in weights)) <= mm.mpf('1e-60')))
            else:
                summary['independent_circuit'] = dict(degenerate=True)
        else:
            summary['independent_circuit'] = dict(degenerate_support=True)
    summary['elapsed_seconds'] = time.monotonic() - started
    signal.alarm(0)
    (ROOT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
