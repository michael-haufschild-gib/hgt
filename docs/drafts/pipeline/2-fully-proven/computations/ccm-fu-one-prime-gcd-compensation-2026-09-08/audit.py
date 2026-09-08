"""Independent source and 80-digit Edmonds-Karp audit. Supplied RunPod only."""
from collections import deque
import hashlib
import json
import math
import multiprocessing as multiprocessing
from pathlib import Path
import signal
import time
import mpmath as mp
import numpy as np
from screen import build_network, worker_init

mp.mp.dps = 80
M = int(json.loads(Path('summary.json').read_text())['selected_audit_M'])
MU = None
DEFECT = None
STEP = None
CHANNEL = None


def channel_chunk(indices):
    if M <= 256:
        return [(d, MU[d]*mp.fsum(STEP[k]*DEFECT[k//d] for k in range(d, M)))
                for d in indices]
    return [(d, MU[d]*mp.fsum((mp.sqrt(min(M, d*(q+1)))-mp.sqrt(d*q))*DEFECT[q]
                             for q in range(1, (M-1)//d+1))) for d in indices]


def group_chunk(indices):
    groups = [mp.mpf(0)]*M
    for d in indices:
        for e in range(d+1, M):
            groups[math.gcd(d, e)] += 2*CHANNEL[d]*CHANNEL[e]
    return groups


def edmonds_karp(adj, sink):
    total = mp.mpf(0)
    epsilon = mp.mpf('1e-65')
    while True:
        parent = {0: None}
        queue = deque([0])
        while queue and sink not in parent:
            v = queue.popleft()
            for i, (w, _, cap) in enumerate(adj[v]):
                if cap > epsilon and w not in parent:
                    parent[w] = (v, i)
                    queue.append(w)
        if sink not in parent:
            return total, set(parent)
        path = []
        w = sink
        while w:
            v, i = parent[w]
            path.append((v, i))
            w = v
        amount = min(adj[v][i][2] for v, i in path)
        for v, i in path:
            w, j, _ = adj[v][i]
            adj[v][i][2] -= amount
            adj[w][j][2] += amount
        total += amount


def deadline(*_):
    raise TimeoutError('Frozen90secondauditdeadline')


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    start = time.monotonic()
    primes = {p for p in range(2, M) if all(p % d for d in range(2, math.isqrt(p)+1))}
    MU = [0]+[1]*(M-1)
    for p in primes:
        for n in range(p, M, p):
            MU[n] *= -1
        for n in range(p*p, M, p*p):
            MU[n] = 0
    DEFECT = [mp.mpf(0)]+[mp.log(mp.factorial(q))-sum(q//d for d in range(1, q+1))
                          +2*mp.euler*q for q in range(1, M)]
    STEP = [mp.sqrt(k+1)-mp.sqrt(k) for k in range(M)]
    chunks = [list(range(i, M, 16)) for i in range(1, 17)]
    with multiprocessing.get_context('fork').Pool(4, initializer=worker_init) as pool:
        parts = pool.map(channel_chunk, chunks, chunksize=1)
    CHANNEL = [mp.mpf(0)]*M
    for part in parts:
        for d, value in part:
            CHANNEL[d] = value
    if M <= 256:
        with multiprocessing.get_context('fork').Pool(4, initializer=worker_init) as pool:
            parts = pool.map(group_chunk, chunks, chunksize=1)
        G = [mp.fsum(part[r] for part in parts) for r in range(M)]
    else:
        G = [mp.mpf(0)]*M
        for r in range(M-1, 0, -1):
            cs = CHANNEL[r::r]
            G[r] = mp.fsum(cs)**2-mp.fsum(c*c for c in cs)-mp.fsum(G[2*r::r])
    D = mp.fsum(c*c for c in CHANNEL)
    head = mp.fsum(CHANNEL)
    source_reconstruction = abs(mp.fsum(G)-(head*head-D))
    assert source_reconstruction < mp.mpf('1e-60')*D
    with np.load('inputs/cutoff_{}.npz'.format(M)) as data:
        g_error = max(abs(G[r]-mp.mpf(str(data['G'][r]))) for r in range(M))
        c_error = max(abs(CHANNEL[r]-mp.mpf(str(data['C'][r]))) for r in range(M))
    assert max(g_error, c_error) < mp.mpf('1e-10')*D
    normalized = [g/D for g in G]
    positives = [r for r in range(1, M) if G[r] > 0]
    negatives = [s for s in range(1, M) if G[s] < 0]
    pairs = []
    for r in positives:
        for s in negatives:
            a, b = sorted((r, s))
            q, rem = divmod(b, a)
            if rem == 0 and q in primes:
                pairs.append((r, s))
    screen = json.loads(Path('flow_{}.json'.format(M)).read_text())
    screen_pairs = {(f['r'], f['s']) for f in screen['flows']}
    significant_pairs = {(r, s) for r, s in pairs
                         if min(abs(G[r]), abs(G[s])) > mp.mpf('1e-10')*D}
    assert significant_pairs <= screen_pairs
    adj, sink, pnode, nnode, refs = build_network(normalized, pairs)
    flow, reachable = edmonds_karp(adj, sink)
    A = [r for r in positives if pnode[r] in reachable]
    aset = set(A)
    neighbors = sorted({s for r, s in pairs if r in aset})
    cut = mp.fsum(normalized[r] for r in A)+mp.fsum(normalized[s] for s in neighbors)
    P = mp.fsum(normalized[r] for r in positives)
    U = P-flow
    assert abs(U-cut) < mp.mpf('1e-60')
    assert abs(U-screen['U_over_D']) < mp.mpf('1e-10')
    used_p = {r: mp.mpf(0) for r in positives}
    used_n = {s: mp.mpf(0) for s in negatives}
    flows = []
    nstr = lambda x: mp.nstr(x, 75)
    for r, s, (v, i) in refs:
        w, j, _ = adj[v][i]
        amount = adj[w][j][2]
        used_p[r] += amount
        used_n[s] += amount
        flows.append(dict(r=r, s=s, flow_over_D=nstr(amount)))
    assert max([mp.mpf(0)]+[used_p[r]-normalized[r] for r in positives]
               +[used_n[s]+normalized[s] for s in negatives]) < mp.mpf('1e-60')
    result = dict(M=M, digits=80, workers=4, seconds=time.monotonic()-start,
                  diagonal=nstr(D), head=nstr(head), U_over_D=nstr(U),
                  U=nstr(U*D), positive_over_D=nstr(P), cut_over_D=nstr(cut),
                  cut_positive=A, cut_negative_neighbors=neighbors,
                  isolated_positive=[r for r in positives if not any(a == r for a, _ in pairs)],
                  source_reconstruction_error=nstr(source_reconstruction),
                  max_G_source_error=nstr(g_error), max_C_source_error=nstr(c_error),
                  flow_cut_error=nstr(abs(U-cut)), screen_U_error=nstr(abs(U-screen['U_over_D'])),
                  channels=[dict(d=d, C=nstr(CHANNEL[d])) for d in range(1, M)],
                  groups=[dict(r=r, G=nstr(G[r])) for r in range(1, M)], flows=flows,
                  residuals=[dict(r=r, residual_over_D=nstr(normalized[r]-used_p[r]))
                             for r in positives],
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('audit.json').write_text(json.dumps(result, indent=2))
    signal.alarm(0)
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('channels', 'groups', 'flows', 'residuals')}), flush=True)
