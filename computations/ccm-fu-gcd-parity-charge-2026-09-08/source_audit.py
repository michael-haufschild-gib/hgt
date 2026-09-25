"""Independent 80-digit, defining-time-sum audit; supplied RunPod only."""
import hashlib
import json
import math
import multiprocessing as multiprocessing
from pathlib import Path
import signal
import time
import mpmath as mp

mp.mp.dps = 80
M = int(json.loads(Path('summary.json').read_text())['selected_audit_M'])
MU = None
DEFECT = None
STEP = None
CHANNEL = None


def channel_chunk(indices):
    return [(d, int(MU[d])*mp.fsum(STEP[k]*DEFECT[k//d] for k in range(d, M)))
            for d in indices]


def group_chunk(indices):
    values = [mp.mpf(0)]*M
    for d in indices:
        for e in range(d+1, M):
            values[math.gcd(d, e)] += 2*CHANNEL[d]*CHANNEL[e]
    return values


def deadline(*_):
    raise TimeoutError('Frozen90secondauditdeadline')


def worker_init():
    signal.signal(signal.SIGALRM, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    start = time.monotonic()
    MU = [0]+[1]*(M-1)
    for p in range(2, M):
        if all(p % d for d in range(2, math.isqrt(p)+1)):
            for n in range(p, M, p):
                MU[n] *= -1
            for n in range(p*p, M, p*p):
                MU[n] = 0
    DEFECT = [mp.mpf(0)]+[
        mp.log(mp.factorial(q))-sum(q//d for d in range(1, q+1))+2*mp.euler*q
        for q in range(1, M)]
    STEP = [mp.sqrt(k+1)-mp.sqrt(k) for k in range(M)]
    chunks = [list(range(i, M, 16)) for i in range(1, 17)]
    with multiprocessing.get_context('fork').Pool(4, initializer=worker_init) as pool:
        parts = pool.map(channel_chunk, chunks, chunksize=1)
    CHANNEL = [mp.mpf(0)]*M
    for part in parts:
        for d, value in part:
            CHANNEL[d] = value
    with multiprocessing.get_context('fork').Pool(4, initializer=worker_init) as pool:
        parts = pool.map(group_chunk, chunks, chunksize=1)
    G = [mp.fsum(part[r] for part in parts) for r in range(M)]
    diagonal = mp.fsum(c*c for c in CHANNEL)
    head = mp.fsum(CHANNEL)
    positive = mp.fsum(max(g, 0) for g in G)
    negative = mp.fsum(max(-g, 0) for g in G)
    error = abs(mp.fsum(G)-(head*head-diagonal))
    assert error < mp.mpf('1e-65')*max(1, diagonal)
    long_double = json.loads(Path('cutoff_{}.json'.format(M)).read_text())
    source_errors = {
        name: abs(value-mp.mpf(long_double[name]))
        for name, value in [('diagonal', diagonal), ('head', head),
                            ('positive', positive), ('negative', negative)]}
    assert max(source_errors.values()) < mp.mpf('1e-11')*max(1, diagonal)
    nstr = lambda x: mp.nstr(x, 75)
    result = dict(M=M, digits=80, workers=4, seconds=time.monotonic()-start,
                  diagonal=nstr(diagonal), head=nstr(head), head_square=nstr(head*head),
                  positive=nstr(positive), negative=nstr(negative),
                  excess=nstr(positive-diagonal),
                  positive_over_diagonal=nstr(positive/diagonal),
                  reconstruction_error=nstr(error),
                  source_errors={k:nstr(v) for k,v in source_errors.items()},
                  channels=[{'d':d,'C':nstr(CHANNEL[d])} for d in range(1, M)],
                  groups=[{'r':r,'G':nstr(G[r])} for r in range(1, M)],
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('audit.json').write_text(json.dumps(result, indent=2))
    signal.alarm(0)
    print(json.dumps({k:v for k,v in result.items() if k not in ('channels','groups')}))
