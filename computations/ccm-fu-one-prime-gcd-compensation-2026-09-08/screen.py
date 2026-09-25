"""Frozen arithmetic gcd transport diagnostic. Execute only on supplied RunPod."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
os.environ['MKL_NUM_THREADS'] = '1'
from collections import deque
import hashlib
import json
import math
import multiprocessing as multiprocessing
from pathlib import Path
import signal
import sys
import time
import numpy as np

CUTOFFS = list(range(101, 257)) + [512, 1024, 2048, 4096, 8192]
EPS = 1e-15
sys.setrecursionlimit(20000)


def graph_edges(G):
    M = len(G)
    prime = np.ones(M, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(M-1)+1):
        if prime[p]:
            prime[p*p::p] = False
    edges = []
    for p in np.flatnonzero(prime):
        p = int(p)
        for r in range(1, (M-1)//p+1):
            s = r*p
            if G[r] > 0 and G[s] < 0:
                edges.append((r, s))
            elif G[s] > 0 and G[r] < 0:
                edges.append((s, r))
    return sorted(edges)


def build_network(G, pairs):
    positives = [r for r in range(1, len(G)) if G[r] > 0]
    negatives = [r for r in range(1, len(G)) if G[r] < 0]
    pnode = {r: i+1 for i, r in enumerate(positives)}
    nnode = {r: i+1+len(positives) for i, r in enumerate(negatives)}
    sink = len(positives)+len(negatives)+1
    adj = [[] for _ in range(sink+1)]
    zero = G[0]*0
    def add(a, b, cap):
        i, j = len(adj[a]), len(adj[b])
        adj[a].append([b, j, cap])
        adj[b].append([a, i, zero])
        return (a, i)
    for r in positives:
        add(0, pnode[r], G[r])
    for r in negatives:
        add(nnode[r], sink, -G[r])
    big = sum(G[r] for r in positives)+1
    refs = [(r, s, add(pnode[r], nnode[s], big)) for r, s in pairs]
    return adj, sink, pnode, nnode, refs


def dinic(adj, sink):
    total = 0.0
    while True:
        level = [-1]*len(adj)
        level[0] = 0
        queue = deque([0])
        while queue:
            v = queue.popleft()
            for w, _, cap in adj[v]:
                if cap > EPS and level[w] < 0:
                    level[w] = level[v]+1
                    queue.append(w)
        if level[sink] < 0:
            return total, {v for v, d in enumerate(level) if d >= 0}
        pos = [0]*len(adj)
        def push(v, amount):
            if v == sink:
                return amount
            while pos[v] < len(adj[v]):
                edge = adj[v][pos[v]]
                w, rev, cap = edge
                if cap > EPS and level[w] == level[v]+1:
                    sent = push(w, min(amount, cap))
                    if sent > EPS:
                        edge[2] -= sent
                        adj[w][rev][2] += sent
                        return sent
                pos[v] += 1
            return 0.0
        while True:
            sent = push(0, float('inf'))
            if sent <= EPS:
                break
            total += sent


def cutoff(M):
    source = Path('inputs/cutoff_{}.npz'.format(M))
    with np.load(source) as data:
        C = data['C']
        original = data['G']
    D = np.sum(C*C, dtype=np.longdouble)
    G = [float(g/D) for g in original]
    pairs = graph_edges(G)
    if M <= 112:
        def adjacent(r, s):
            a, b = sorted((r, s))
            q, rem = divmod(b, a)
            return rem == 0 and q >= 2 and all(q % d for d in range(2, math.isqrt(q)+1))
        independent = {(r, s) for r in range(1, M) if G[r] > 0
                       for s in range(1, M) if G[s] < 0 and adjacent(r, s)}
        assert independent == set(pairs)
    adj, sink, pnode, nnode, refs = build_network(G, pairs)
    total, reachable = dinic(adj, sink)
    assert sink not in reachable
    flows = []
    used_p = {r: 0.0 for r in pnode}
    used_n = {r: 0.0 for r in nnode}
    for r, s, (v, j) in refs:
        w, rev, _ = adj[v][j]
        amount = adj[w][rev][2]
        assert amount >= -1e-12
        used_p[r] += amount
        used_n[s] += amount
        flows.append(dict(r=r, s=s, flow_over_D=amount))
    residuals = [dict(r=r, residual_over_D=G[r]-used_p[r]) for r in pnode]
    capacity_error = max([0.0] + [used_p[r]-G[r] for r in pnode]
                         + [used_n[s]+G[s] for s in nnode])
    A = [r for r in pnode if pnode[r] in reachable]
    aset = set(A)
    neighbors = sorted({s for r, s in pairs if r in aset})
    cut = math.fsum(G[r] for r in A)+math.fsum(G[s] for s in neighbors)
    P = math.fsum(G[r] for r in pnode)
    U = math.fsum(item['residual_over_D'] for item in residuals)
    reconstruction_error = abs(float(np.sum(original, dtype=np.longdouble)/D)
                               - float(np.sum(C, dtype=np.longdouble)**2/D-1))
    errors = dict(capacity=capacity_error, flow_cut=abs(U-cut),
                  total_flow=abs(math.fsum(f['flow_over_D'] for f in flows)-total),
                  mass=abs(U-(P-total)), source_reconstruction=reconstruction_error)
    assert max(errors.values()) <= 1e-10, (M, errors)
    incident = {r for r, _ in pairs}
    isolated = [r for r in pnode if r not in incident]
    significant = [item for item in residuals if item['residual_over_D'] > 1e-10]
    row = dict(M=M, diagonal=str(D), U_over_D=U, cut_over_D=cut,
               positive_over_D=P, flow_over_D=total,
               isolated_over_D=math.fsum(G[r] for r in isolated),
               isolated_labels=isolated, cut_positive=A, cut_negative_neighbors=neighbors,
               cut_min_positive=None if not A else min(A),
               residual_min_positive=None if not significant else min(item['r'] for item in significant),
               positive_count=len(pnode), negative_count=len(nnode), edges=len(pairs),
               errors=errors, failure=bool(U-1 > 1e-9), residuals=residuals,
               flows=flows, input_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
    Path('flow_{}.json'.format(M)).write_text(json.dumps(row, indent=2))
    return {k: v for k, v in row.items() if k not in
            ('flows', 'residuals', 'isolated_labels', 'cut_positive', 'cut_negative_neighbors')}


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
    with multiprocessing.get_context('fork').Pool(4, initializer=worker_init) as pool:
        rows = pool.map(cutoff, CUTOFFS, chunksize=1)
    failures = [r for r in rows if r['failure']]
    selected = failures[0] if failures else max((r for r in rows if r['M'] <= 256),
                                              key=lambda r: r['U_over_D'])
    report = dict(workers=4, seconds=time.monotonic()-start, cutoffs=CUTOFFS,
                  rows=rows, failures=[r['M'] for r in failures],
                  selected_audit_M=selected['M'],
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('summary.json').write_text(json.dumps(report, indent=2))
    signal.alarm(0)
    print(json.dumps(dict(seconds=report['seconds'], cutoffs=len(rows),
                         failures=report['failures'], selected_audit_M=selected['M'],
                         maximum=max(rows, key=lambda r: r['U_over_D']),
                         dyadic_rows=[r for r in rows if r['M'] >= 512])), flush=True)
