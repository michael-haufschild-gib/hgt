"""Frozen arity-charge replay. Run only on the supplied RunPod."""
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import signal
import time
import numpy as np
from source_screen import source


def successor(F, q):
    G = F.copy()
    child = np.arange(q, len(F), q)
    G[child//q] += F[child]
    G[child] = 0
    return G


def replay(M, primes, factors, coeff, path):
    F = np.zeros(M)
    for d, c in coeff:
        F[d] = c
    degree = np.asarray([len(v) for v in factors])
    D0 = float(degree @ (F*F))
    Jsum, Wsum = 0.0, 0.0
    out = []
    first_D = first_J = first_interacting = None
    for index, old in enumerate(path['steps']):
        q = old['prime']
        assert abs(float(F @ F)-old['Q_before']) <= 1e-8*max(1, path['Q0'])
        D = float(degree @ (F*F))
        child = np.arange(q, M, q)
        parent = child//q
        W = float(F[child] @ F[child])
        J = float(2*np.dot(degree[parent]*F[parent], F[child]))
        interacting = int(np.count_nonzero(F[child][degree[child] > 1]))
        after = successor(F, q)
        nextD = float(degree @ (after*after))
        Jsum += J
        Wsum += W
        assert abs(nextD-D-J+W) <= 1e-8*max(1, D0)
        assert abs(nextD-D0-Jsum+Wsum) <= 1e-8*max(1, D0)
        assert abs(float(after @ after)-old['Q_after']) <= 1e-8*max(1, path['Q0'])
        if first_D is None and nextD > D+1e-10*max(1, D0):
            first_D = index
        if first_J is None and Jsum > 1e-10*max(1, D0):
            first_J = index
        if first_interacting is None and interacting:
            first_interacting = index
        out.append(dict(index=index, prime=q, D_before=D, D_after=nextD,
                        W=W, J=J, cumulative_W=Wsum, cumulative_J=Jsum,
                        interacting_children=interacting))
        F = after
    assert nextD == 0
    return dict(D0=D0, first_positive_D=first_D, first_positive_cumulative_J=first_J,
                first_interacting=first_interacting, peak_D_ratio=max([D0]+[r['D_after'] for r in out])/D0,
                max_cumulative_J_ratio=max(r['cumulative_J'] for r in out)/D0,
                final_W_ratio=Wsum/D0, positive_D_steps=sum(r['D_after']>r['D_before']+1e-10*max(1,D0) for r in out),
                steps=out)


def cutoff(old):
    start = time.monotonic()
    M = old['M']
    primes, factors, coeff = source(M)
    out = dict(M=M, increasing=replay(M, primes, factors, coeff, old['increasing']),
               decreasing=replay(M, primes, factors, coeff, old['decreasing']),
               seconds=time.monotonic()-start)
    Path(f'cutoff_{M}.json').write_text(json.dumps(out, indent=2))
    return out


def deadline(*_):
    raise TimeoutError('Frozen90seconddeadline')


def init():
    signal.signal(signal.SIGALRM, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(90)
    started = time.monotonic()
    raw = Path('paths.json').read_bytes()
    paths = json.loads(raw)
    assert [r['M'] for r in paths['results']] == [512, 2048, 8192, 32768]
    failure = None
    try:
        with mp.get_context('fork').Pool(4, initializer=init) as pool:
            results = pool.map(cutoff, paths['results'])
    except Exception as exc:
        failure = repr(exc)
        results = [json.loads(p.read_text()) for p in sorted(Path('.').glob('cutoff_*.json'))]
    signal.alarm(0)
    out = dict(workers=4, seconds=time.monotonic()-started, failure=failure,
               paths_sha256=hashlib.sha256(raw).hexdigest(),
               script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               source_sha256=hashlib.sha256(Path('source_screen.py').read_bytes()).hexdigest(), results=results)
    Path('summary.json').write_text(json.dumps(out, indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='results'}))
    print(json.dumps([dict(M=r['M'], policy=mode, **{k:v for k,v in r[mode].items() if k!='steps'})
                      for r in results for mode in ['increasing','decreasing']]))
    if failure:
        raise SystemExit(2)
