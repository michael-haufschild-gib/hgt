"""Frozen all-weight interval graph experiment. Execute on RunPod only."""
import os
os.environ.update(OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
import csv
from fractions import Fraction as F
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import signal
import time


UNIT = [(F(0), F(1))]


def union(parts):
    out = []
    for lo, hi in sorted(parts):
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], hi))
        else:
            out.append((lo, hi))
    return out


def meet(a, b):
    return union([(max(x, z), min(y, w)) for x, y in a for z, w in b
                  if max(x, z) <= min(y, w)])


def affine_interval(dv, dh, rhs):
    if dh == 0:
        return UNIT if dv <= rhs else []
    cut = (rhs-dv)/dh
    if dh > 0:
        return [(F(0), min(F(1), cut))] if cut >= 0 else []
    return [(max(F(0), cut), F(1))] if cut <= 1 else []


def show(parts):
    return [dict(lo=float(a), hi=float(b), exact_lo=str(a), exact_hi=str(b)) for a, b in parts]


def graph(M, q, h2, rhs):
    size = len(q)
    count = (size-1).bit_length()
    v = [q[i]-h2[i] for i in range(size)]
    paths = [[] for _ in range(size)]
    paths[0] = UNIT
    local = UNIT
    reducers = []
    local_empty_states = []
    for mask in range(size):
        choices = []
        if mask:
            incoming = []
            for i in range(count):
                if mask & (1 << i):
                    prev = mask ^ (1 << i)
                    edge = affine_interval(v[mask]-v[prev], h2[mask]-h2[prev], rhs)
                    incoming.extend(meet(paths[prev], edge))
            paths[mask] = union(incoming)
        if mask == size-1:
            continue
        for i in range(count):
            if not mask & (1 << i):
                nxt = mask | (1 << i)
                choices.extend(affine_interval(v[nxt]-v[mask], h2[nxt]-h2[mask], rhs))
        choices = union(choices)
        if not choices:
            local_empty_states.append(mask)
        narrowed = meet(local, choices)
        if narrowed != local:
            reducers.append(dict(mask=mask, choices=show(choices), cumulative=show(narrowed)))
        local = narrowed
    return dict(path=paths[-1], local=local, reducers=reducers,
                local_empty_states=local_empty_states,
                unreachable_masks=[i for i, p in enumerate(paths) if not p])


def primes_below(M):
    return [p for p in range(2, M) if all(p % d for d in range(2, math.isqrt(p)+1))]


def inspect(job):
    M, energies = job
    primes = primes_below(M)
    size = 1 << len(primes)
    assert set(energies) == set(range(size))
    e = [energies[m] for m in range(size)]
    tau = 1e-12*max(1., e[0])
    late = [(i, p) for i, p in enumerate(primes) if 2*p > M]
    heads, spread = [], 0.
    for mask in range(size):
        if not late:
            assert size == 1
            heads.append(math.sqrt(e[mask]))
            continue
        anchors = []
        for i, p in late:
            bit = 1 << i
            c = -(math.sqrt(M)-math.sqrt(p))*(2*0.5772156649015328606065120900824-1)
            anchors.append((e[mask]-e[mask ^ bit])/(2*c)+c if mask & bit
                           else (e[mask | bit]-e[mask])/(2*c))
        spread = max(spread, max(anchors)-min(anchors))
        heads.append(anchors[-1])
    assert spread < tau
    q = list(map(F, e))
    h2 = [F(h*h) for h in heads]
    return dict(M=M, states=size, max_head_anchor_spread=spread,
                relaxed=graph(M, q, h2, F(tau)), tightened=graph(M, q, h2, -F(tau)))


def accumulate(results, version, claim):
    current, reducers, first_empty = UNIT, [], None
    for r in results:
        narrowed = meet(current, r[version][claim])
        if narrowed != current:
            reducers.append(dict(M=r['M'], cumulative=show(narrowed)))
        if current and not narrowed and first_empty is None:
            first_empty = r['M']
        current = narrowed
    return dict(feasible=show(current), first_empty=first_empty, reducers=reducers)


def audit(M):
    import mpmath as m
    m.mp.dps = 80
    primes = primes_below(M)
    size = 1 << len(primes)
    defect = [m.mpf(0)]+[m.fsum(m.log(j) for j in range(1, k+1))
              -sum(k//d for d in range(1, k+1))+2*m.euler*k for k in range(1, M)]
    coeff = []
    for d in range(1, M):
        if any(d % (p*p) == 0 for p in primes):
            continue
        mask = sum(1 << i for i, p in enumerate(primes) if d % p == 0)
        c = (-1)**bin(mask).count('1')*m.fsum(
            (m.sqrt(k+1)-m.sqrt(k))*defect[k//d] for k in range(d, M))
        coeff.append((d, mask, c))
    q, h2, heads, fields = [], [], [], []
    for mask in range(size):
        bins = {}
        for _, support, c in coeff:
            bins.setdefault(support & ~mask, []).append(c)
        field = {r: m.fsum(xs) for r, xs in bins.items()}
        h = field.get(0, m.mpf(0))
        q.append(F(m.nstr(m.fsum(c*c for c in field.values()), 75)))
        h2.append(F(m.nstr(h*h, 75)))
        heads.append(m.nstr(h, 70))
        fields.append({str(r): m.nstr(c, 70) for r, c in sorted(field.items())})
    result = graph(M, q, h2, F('1e-60')*max(F(1), q[0]))
    witnesses = sorted(set(result['local_empty_states']+[r['mask'] for r in result['reducers']]))
    return dict(M=M, path=result['path'], local=result['local'], reducers=result['reducers'],
        local_empty_states=result['local_empty_states'], unreachable_masks=result['unreachable_masks'],
        witnesses=[dict(mask=mask, P=[p for i, p in enumerate(primes) if mask & (1 << i)],
            energy=str(q[mask]), head=heads[mask], fields=fields[mask],
            choices=[dict(p=p, dv=str(q[mask | (1 << i)]-h2[mask | (1 << i)]-q[mask]+h2[mask]),
                          dh2=str(h2[mask | (1 << i)]-h2[mask]))
                     for i, p in enumerate(primes) if not mask & (1 << i)]) for mask in witnesses],
        coefficients=[dict(d=d, mask=mask, value=m.nstr(c, 70)) for d, mask, c in coeff])


def deadline(_sig, _frame):
    raise TimeoutError('Frozen fifty-second deadline')


def initialize():
    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    signal.signal(signal.SIGALRM, signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM, deadline)
    signal.signal(signal.SIGTERM, deadline)
    signal.alarm(50)
    start = time.monotonic()
    source = Path('subset-states.csv')
    rows = {}
    with source.open() as handle:
        for r in csv.DictReader(handle):
            rows.setdefault(int(r['M']), {})[int(r['mask'])] = float(r['energy'])
    assert sorted(rows) == list(range(1, 33))
    workers = min(8, os.cpu_count() or 1)
    with mp.Pool(workers, initializer=initialize) as pool:
        results = pool.map(inspect, sorted(rows.items()))
    cumulative = {version: {claim: accumulate(results, version, claim) for claim in ('path', 'local')}
                  for version in ('relaxed', 'tightened')}
    targets = sorted({r['M'] for claim in ('path', 'local')
                      for r in cumulative['relaxed'][claim]['reducers']})
    with mp.Pool(workers, initializer=initialize) as pool:
        audits = pool.map(audit, targets)
    audited = {claim: accumulate([dict(M=r['M'], direct=r) for r in audits], 'direct', claim)
               for claim in ('path', 'local')}
    for r in results:
        for version in ('relaxed', 'tightened'):
            for claim in ('path', 'local'):
                r[version][claim] = show(r[version][claim])
    for r in audits:
        for claim in ('path', 'local'):
            r[claim] = show(r[claim])
    out = dict(question='Fixed positive head weight permits complete monotone paths, or universal local descent.',
        workers=workers, elapsed_seconds=time.monotonic()-start, states=sum(r['states'] for r in results),
        input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        cumulative=cumulative, audit_targets=targets, audited=audited, results=results, audits=audits)
    Path('summary.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k: v for k, v in out.items() if k not in ('results', 'audits')}, indent=2))
    signal.alarm(0)
