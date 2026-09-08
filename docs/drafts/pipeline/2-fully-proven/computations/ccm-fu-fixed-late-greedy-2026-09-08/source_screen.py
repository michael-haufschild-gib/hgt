"""Frozen source-side transverse-front experiment. Run only on supplied RunPod."""
import collections
import hashlib
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import random
import signal
import time


def source(M):
    factors = [[] for _ in range(M)]
    divisors = [0]*M
    primes = []
    for p in range(2, M):
        if not factors[p]:
            primes.append(p)
            for n in range(p, M, p): factors[n].append(p)
    for d in range(1, M):
        for n in range(d, M, d): divisors[n] += 1
    summatory, logfac = 0, 0.0
    defect = [0.0]*M
    gamma = 0.577215664901532860606512090082402431
    for n in range(1, M):
        summatory += divisors[n]
        logfac += math.log(n)
        defect[n] = logfac-summatory+2*gamma*n
    coeff = []
    for d in range(1, M):
        if any(d % (p*p) == 0 for p in factors[d]): continue
        terms = [(math.sqrt(min(M, d*(k+1)))-math.sqrt(d*k))*defect[k]
                 for k in range(1, (M-1)//d+1)]
        coeff.append((d, (-1)**len(factors[d])*math.fsum(terms)))
    return primes, factors, coeff


def cutoff(M):
    primes, factors, coeff = source(M)
    extra = [p for p in primes if 19 <= p <= M//15]
    rng = random.Random(9081700+M)
    cores = [[], extra, extra[::2], extra[1::2]]
    cores += [extra[:len(extra)*k//12] for k in range(1, 12)]
    while len(cores) < 64:
        density = (0.25,0.5,0.75)[len(cores)%3]
        cores.append([p for p in extra if rng.random() < density])
    diagonal = math.fsum(c*c for _, c in coeff)
    states = []
    for i, core in enumerate(cores):
        P = set(core) | {3,5,7,11,13}
        vals = collections.defaultdict(list)
        for d, c in coeff:
            r = d
            for p in factors[d]:
                if p in P: r //= p
            vals[r].append(c)
        F = {r: math.fsum(v) for r,v in vals.items()}
        contributions = []
        for r, b in F.items():
            if r % 17: continue
            s = r//17
            a = F.get(s,0.0)
            change = -b*b if s in (1,2) else 2*a*b
            contributions.append(dict(label=r,partner=s,partner_value=a,value=b,change=change))
        gain = math.fsum(x['change'] for x in contributions)
        after = collections.defaultdict(list)
        for r,v in F.items(): after[r//17 if r%17==0 else r].append(v)
        G = {r:math.fsum(v) for r,v in after.items()}
        beforeT = math.fsum(v*v for r,v in F.items() if r not in (1,2))
        afterT = math.fsum(v*v for r,v in G.items() if r not in (1,2))
        assert abs((afterT-beforeT)-gain) <= 1e-10*max(1,diagonal)
        states.append(dict(index=i,P=sorted(P),gain=gain,normalized_gain=gain/diagonal,
            violation=gain>1e-10*max(1,diagonal),transverse=beforeT,
            energy=math.fsum(v*v for v in F.values()),head=F.get(1,0),two=F.get(2,0),
            contributions=contributions))
    return dict(M=M,diagonal=diagonal,states=states,
                violations=sum(s['violation'] for s in states))


def deadline(*_): raise TimeoutError('Frozen90seconddeadline')
def worker_init():
    signal.signal(signal.SIGALRM,signal.SIG_DFL)
    signal.signal(signal.SIGTERM,signal.SIG_DFL)


if __name__=='__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(90)
    start=time.monotonic()
    with mp.Pool(4,initializer=worker_init) as pool:
        results=pool.map(cutoff,[512,2048,8192,32768])
    out=dict(question='Nonpositive transverse gain when advancing smallest remaining prime17',
        workers=4,seconds=time.monotonic()-start,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),results=results)
    Path('summary.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='results'}))
    print(json.dumps([dict(M=r['M'],states=len(r['states']),violations=r['violations'],
        min_gain=min(s['normalized_gain'] for s in r['states']),
        max_gain=max(s['normalized_gain'] for s in r['states'])) for r in results]))
