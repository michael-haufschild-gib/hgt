"""Frozen exhaustive charge-safe path screen. Execute only on supplied RunPod."""
import hashlib
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import signal
import time

for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name] = '1'
import numpy as np
from source_screen import source


def cutoff(M):
    started = time.monotonic()
    primes, factors, coeff = source(M)
    n, size = len(primes), 1 << len(primes)
    bits = {p: 1 << j for j, p in enumerate(primes)}
    labels = [sum(bits[p] for p in factors[d]) for d, c in coeff]
    values = np.array([c for d, c in coeff])
    masks = np.arange(size, dtype=np.int64)
    kernel = np.zeros((n+1, size))
    for a, ca in zip(labels, values):
        for b, cb in zip(labels, values):
            delta, common = a ^ b, a & b
            kernel[0, delta] += ca*cb
            while common:
                bit = common & -common
                kernel[bit.bit_length(), delta] += ca*cb
                common ^= bit
    for j in range(n):
        step = 1 << j
        blocks = kernel.reshape(n+1, -1, 2*step)
        blocks[:, :, step:] += blocks[:, :, :step]
    Q, W = kernel[0], kernel[1:]
    unused = np.array([(masks & (1 << j)) == 0 for j in range(n)], dtype=bool).reshape(n, size)
    D = np.sum(np.where(unused, W, 0), axis=0)
    Q0, D0 = float(Q[0]), float(D[0])
    tol = 1e-10*max(1, Q0, D0)

    # Independent literal regrouping at EVERY subset, with no pair kernel.
    row = np.full(size, -1, dtype=np.int64)
    row[labels] = np.arange(len(labels))
    F = np.zeros((len(labels), size))
    for label, value in zip(labels, values):
        residual = label & ~masks
        assert np.all(row[residual] >= 0)
        F[row[residual], masks] += value
    squares = F*F
    directQ = np.sum(squares, axis=0)
    incidence = np.array([[(r & (1 << j)) != 0 for r in labels]
                          for j in range(n)], dtype=float).reshape(n, len(labels))
    directW = incidence @ squares
    directD = np.sum(directW, axis=0)
    max_error = max(float(np.max(np.abs(Q-directQ))),
                    float(np.max(np.abs(D-directD))),
                    float(np.max(np.abs(np.where(unused, W, 0)-directW))) if n else 0.0)
    assert max_error < tol
    assert abs(Q[-1]-math.fsum(values)**2) < tol
    assert abs(D[-1]) < tol

    cost = np.full(size, np.inf)
    predecessor = np.full(size, -1, dtype=np.int16)
    cost[0] = 0
    for P in range(1, size):
        if Q[P] > Q0+tol:
            continue
        todo = P
        best, chosen = math.inf, -1
        while todo:
            bit = todo & -todo
            j, prev = bit.bit_length()-1, P ^ bit
            proposed = cost[prev]+W[j, prev]
            if proposed < best:
                best, chosen = proposed, j
            todo ^= bit
        if math.isfinite(best) and D[P]+best <= D0+tol:
            cost[P], predecessor[P] = best, chosen
    feasible = bool(np.isfinite(cost[-1]))
    steps = []
    if feasible:
        P, order = size-1, []
        while P:
            j = int(predecessor[P])
            assert j >= 0
            order.append(j)
            P ^= 1 << j
        P, cumulativeW = 0, 0.0
        for j in reversed(order):
            nxt = P | (1 << j)
            w = float(W[j, P])
            cumulativeW += w
            steps.append(dict(P=P, prime=primes[j], W=w,
                J=float(D[nxt]-D[P]+w), Q=float(Q[nxt]), D=float(D[nxt]),
                cumulative_W=cumulativeW,
                cumulative_J=float(D[nxt]-D0+cumulativeW)))
            P = nxt
        assert P == size-1
    out = dict(M=M, primes=primes, subsets=size, feasible=feasible,
               Q0=Q0, D0=D0, tolerance=tol, kernel_check_max_error=max_error,
               Q_rejected=int(np.count_nonzero(Q > Q0+tol)),
               reachable=int(np.count_nonzero(np.isfinite(cost))),
               Q_safe_unreachable=int(np.count_nonzero((Q <= Q0+tol)&~np.isfinite(cost))),
               final_cost=float(cost[-1]) if feasible else None,
               steps=steps, seconds=time.monotonic()-started)
    np.savez_compressed(f'cutoff_{M}.npz', Q=Q, D=D, W=W, cost=cost,
                        predecessor=predecessor, primes=np.array(primes))
    Path(f'cutoff_{M}.json').write_text(json.dumps(out, indent=2))
    return out


def deadline(*_):
    raise TimeoutError('Frozen90seconddeadline')


def worker_init():
    signal.signal(signal.SIGALRM, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    started, results, failure = time.monotonic(), [], None
    try:
        with mp.Pool(4, initializer=worker_init) as pool:
            for result in pool.imap_unordered(cutoff, range(2,49)):
                results.append(result)
    except Exception as exc:
        failure = repr(exc)
    out = dict(workers=4, seconds=time.monotonic()-started, failure=failure,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(Path('source_screen.py').read_bytes()).hexdigest(),
        results=sorted(results, key=lambda r:r['M']))
    Path('summary.json').write_text(json.dumps(out, indent=2))
    signal.alarm(0)
    print(json.dumps({k:v for k,v in out.items() if k!='results'}))
    print(json.dumps([dict(M=r['M'], feasible=r['feasible'], subsets=r['subsets'],
                           reachable=r['reachable']) for r in out['results']]))
