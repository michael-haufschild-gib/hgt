"""Frozen positive exact-gcd budget experiment. Execute only on supplied RunPod."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
os.environ['MKL_NUM_THREADS'] = '1'
import hashlib
import json
import math
import multiprocessing as multiprocessing
from pathlib import Path
import signal
import time
import mpmath as mp
import numpy as np

LD = np.longdouble
CUTOFFS = list(range(101, 257)) + [2**j for j in range(9, 18)]
MU = None
DEFECT = None


def source_table(N):
    prime = np.ones(N, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(N - 1) + 1):
        if prime[p]:
            prime[p*p::p] = False
    mu = np.ones(N, dtype=np.int8)
    mu[0] = 0
    for p in np.flatnonzero(prime):
        mu[p::p] *= -1
        if p*p < N:
            mu[p*p::p*p] = 0
    tau = np.zeros(N, dtype=np.int64)
    for d in range(1, N):
        tau[d::d] += 1
    mp.mp.dps = 90
    gamma = LD(mp.nstr(mp.euler, 88))
    q = np.arange(1, N, dtype=LD)
    defect = np.zeros(N, dtype=LD)
    defect[1:] = np.cumsum(np.log(q), dtype=LD) - np.cumsum(tau[1:]) + 2*gamma*q
    return mu, defect


def channels(M):
    C = np.zeros(M, dtype=LD)
    for d in range(1, M):
        if MU[d] == 0:
            continue
        q = np.arange(1, (M-1)//d + 1, dtype=np.int64)
        low = (d*q).astype(LD)
        high = np.minimum(M, d*(q+1)).astype(LD)
        weight = (high-low)/(np.sqrt(high)+np.sqrt(low))
        C[d] = int(MU[d])*np.sum(weight*DEFECT[q], dtype=LD)
    return C


def cutoff(M):
    C = channels(M)
    diagonal = np.sum(C*C, dtype=LD)
    head = np.sum(C, dtype=LD)
    B = np.zeros(M, dtype=LD)
    G = np.zeros(M, dtype=LD)
    for r in range(1, M):
        if MU[r] == 0:
            continue
        row = C[r::r]
        total = np.sum(row, dtype=LD)
        B[r] = total*total - np.sum(row*row, dtype=LD)
    for r in range(M-1, 0, -1):
        if MU[r] != 0:
            G[r] = B[r] - np.sum(G[2*r::r], dtype=LD)
    scale = max(LD(1), diagonal)
    error = abs(np.sum(G, dtype=LD) - (head*head-diagonal))
    assert error <= LD('1e-12')*scale, (M, error, diagonal)
    direct_pair_error = None
    direct_channel_error = None
    if M <= 112:
        exact_groups = np.zeros(M, dtype=LD)
        for d in range(1, M):
            for e in range(d+1, M):
                exact_groups[math.gcd(d, e)] += 2*C[d]*C[e]
        direct_pair_error = np.max(np.abs(exact_groups-G))
        assert direct_pair_error <= LD('1e-12')*scale
    if M <= 104:
        direct = np.zeros(M, dtype=LD)
        for d in range(1, M):
            k = np.arange(d, M, dtype=np.int64)
            weight = 1/(np.sqrt((k+1).astype(LD))+np.sqrt(k.astype(LD)))
            direct[d] = int(MU[d])*np.sum(weight*DEFECT[k//d], dtype=LD)
        direct_channel_error = np.max(np.abs(direct-C))
        assert direct_channel_error <= LD('1e-12')*max(LD(1), np.sqrt(diagonal))
    positive = np.sum(np.maximum(G, LD(0)), dtype=LD)
    negative = np.sum(np.maximum(-G, LD(0)), dtype=LD)
    tol = LD('1e-10')*scale
    positives = [{'r': int(r), 'value': str(G[r])} for r in range(1, M) if G[r] > tol]
    row = dict(M=M, diagonal=str(diagonal), head=str(head), positive=str(positive),
               negative=str(negative), absolute=str(positive+negative),
               positive_over_diagonal=float(positive/diagonal),
               positive_over_M_sq=float(positive/(LD(M)*M)),
               absolute_over_M_sq=float((positive+negative)/(LD(M)*M)),
               primitive=str(G[1]), violation=bool(positive-diagonal > tol),
               reconstruction_error=str(error),
               direct_pair_error=None if direct_pair_error is None else str(direct_pair_error),
               direct_channel_error=None if direct_channel_error is None else str(direct_channel_error),
               positive_groups=positives)
    np.savez_compressed('cutoff_{}.npz'.format(M), C=C, G=G, B=B)
    Path('cutoff_{}.json'.format(M)).write_text(json.dumps(row, indent=2))
    return {k: v for k, v in row.items() if k != 'positive_groups'}


def deadline(*_):
    raise TimeoutError('Frozen90seconddeadline')


def worker_init():
    signal.signal(signal.SIGALRM, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    start = time.monotonic()
    MU, DEFECT = source_table(max(CUTOFFS))
    np.savez_compressed('source.npz', mu=MU, defect=DEFECT)
    with multiprocessing.get_context('fork').Pool(4, initializer=worker_init) as pool:
        rows = pool.map(cutoff, CUTOFFS, chunksize=1)
    failures = [r for r in rows if r['violation']]
    selected = failures[0] if failures else max(
        (r for r in rows if r['M'] <= 1024), key=lambda r: r['positive_over_diagonal'])
    report = dict(workers=4, seconds=time.monotonic()-start,
                  dtype=str(np.finfo(LD)), cutoffs=CUTOFFS, rows=rows,
                  failures=[r['M'] for r in failures], selected_audit_M=selected['M'],
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('summary.json').write_text(json.dumps(report, indent=2))
    signal.alarm(0)
    print(json.dumps(dict(seconds=report['seconds'], cutoffs=len(rows),
                         failures=report['failures'], selected_audit_M=selected['M'],
                         maximum=max(rows, key=lambda r: r['positive_over_diagonal']),
                         dyadic_rows=[r for r in rows if r['M'] >= 512])), flush=True)
