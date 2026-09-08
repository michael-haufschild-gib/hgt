"""Complete literal raw-energy two-prime diagnostic. Execute only on RunPod."""
import hashlib
import itertools
import json
import math
import multiprocessing as mp
from pathlib import Path
import signal
import time

import numpy as np
from scipy.sparse import csr_matrix
from source_screen import source


def successor(F, q):
    G = F.copy()
    child = np.arange(q, len(F), q)
    base = child // q
    G[base] += F[child]
    G[child] = 0
    return G


def incidences(M, primes, factors, coeff):
    index = {p:i for i,p in enumerate(primes)}
    edges, pairs = [], []
    for n,_ in coeff:
        for p in factors[n]:
            edges.append((index[p], n//p, n))
        for p,q in itertools.combinations(factors[n],2):
            pairs.append((index[p],index[q],n//(p*q),n))
    return np.asarray(edges,dtype=np.int64).T, np.asarray(pairs,dtype=np.int64).T


def features(F, rem, edge, nprimes):
    i,r,n = edge
    v = F[n]
    nz = v != 0
    A = csr_matrix((v[nz],(i[nz],r[nz])),shape=(nprimes,len(F)))[rem,:]
    return A, 2*np.asarray(A@F).ravel()


def pair_terms(F,p,q):
    out=[]
    for r in range(1,(len(F)-1)//min(p,q)+1):
        if r%p==0 or r%q==0: continue
        h=float(F[r])
        a=float(F[p*r]) if p*r<len(F) else 0.0
        b=float(F[q*r]) if q*r<len(F) else 0.0
        c=float(F[p*q*r]) if p*q*r<len(F) else 0.0
        if a==0 and b==0 and c==0: continue
        out.append(dict(r=r,h=h,a=a,b=b,c=c,
            orientation=(h-c)*(a-b),symmetric=(h+c)*(a+b),mixed=2*(h*c+a*b)))
    d=[x['orientation'] for x in out]
    return out, math.fsum(abs(x) for x in d)-abs(math.fsum(d))


def path(M,primes,F0,edge,pairs,mode):
    F=F0.copy()
    Q0=float(F@F)
    rem=list(range(len(primes)))
    P=[]
    steps=[]
    batches=[]
    first_cross=None
    while rem:
        Q=float(F@F)
        A,g=features(F,rem,edge,len(primes))
        greedy=int(np.argmin(g))
        if mode=='greedy' or len(rem)==1:
            chosen=[rem[greedy]]
            batch=None
        else:
            cross=(A@A.T).toarray()
            pos=np.full(len(primes),-1,dtype=np.int64)
            pos[rem]=np.arange(len(rem))
            i,j,r,n=pairs
            ii,jj=pos[i],pos[j]
            ok=(ii>=0)&(jj>=0)&(F[n]!=0)&(F[r]!=0)
            joint=np.zeros((len(rem),len(rem)))
            np.add.at(joint,(ii[ok],jj[ok]),F[n[ok]]*F[r[ok]])
            joint+=joint.T.copy()
            u,v=np.triu_indices(len(rem),1)
            end=Q+g[u]+g[v]+2*(cross[u,v]+joint[u,v])
            first=Q+np.minimum(g[u],g[v])
            peak=np.maximum(first,end)
            cand=np.flatnonzero(peak==np.min(peak))
            cand=cand[end[cand]==np.min(end[cand])]
            cand=cand[first[cand]==np.min(first[cand])]
            best=int(cand[0])  # upper-triangle indices preserve increasing prime-pair order
            a,b=int(u[best]),int(v[best])
            if g[b]<g[a]: a,b=b,a
            chosen=[rem[a],rem[b]]
            p,q=[primes[i] for i in chosen]
            terms,conflict=pair_terms(F,p,q)
            assert abs((Q+math.fsum(t['symmetric'] for t in terms)-
                abs(math.fsum(t['orientation'] for t in terms)))-first[best]) <= 1e-8*max(1,Q0)
            batch=dict(index=len(batches),P=P.copy(),pair=[p,q],Q_before=Q,
                predicted_first=float(first[best]),predicted_end=float(end[best]),
                predicted_internal_peak=float(peak[best]),greedy_prime=primes[rem[greedy]],
                greedy_next=Q+float(g[greedy]),abandons_greedy=(rem[a]!=rem[greedy]),
                min_pair_score=float(np.min(peak)),
                next_score_margin=float(np.partition(peak,1)[1]-peak[best]) if len(peak)>1 else None,
                cross_child=2*float(cross[a,b]),joint_child=2*float(joint[a,b]),
                order_conflict=conflict,cofactors=terms,
                positive_first_then_nonpositive_total=(first[best]>Q+1e-10*max(1,Q0)
                    and end[best]<=Q+1e-10*max(1,Q0)))
            batches.append(batch)
        for pi in chosen:
            p=primes[pi]
            before=float(F@F)
            F=successor(F,p)
            after=float(F@F)
            P.append(p)
            rem.remove(pi)
            s=dict(step=len(P),prime=p,Q_before=before,Q_after=after,ratio=after/Q0,
                head=float(F[1]),nonempty=after-float(F[1])**2)
            steps.append(s)
            if first_cross is None and after>Q0+1e-10*max(1,Q0):
                first_cross=dict(step=len(P),P=P.copy(),Q=after,
                    batch_index=None if batch is None else batch['index'])
        if batch is not None:
            assert abs(float(F@F)-batch['predicted_end'])<=1e-8*max(1,Q0)
            assert abs(steps[-2]['Q_after']-batch['predicted_first'])<=1e-8*max(1,Q0)
    total=math.fsum(float(v) for v in F0)
    assert abs(float(F[1])-total)<=1e-10*max(1,float(np.sum(np.abs(F0))))
    assert np.count_nonzero(F[2:])==0
    return dict(mode=mode,Q0=Q0,total=total,terminal=float(F@F),steps=steps,batches=batches,
        first_cross=first_cross,peak_ratio=max([1.0]+[s['ratio'] for s in steps]),
        abandons_greedy=sum(b['abandons_greedy'] for b in batches),
        recovering_positive_pairs=sum(b['positive_first_then_nonpositive_total'] for b in batches))


def cutoff(M):
    start=time.monotonic()
    primes,factors,coeff=source(M)
    F0=np.zeros(M)
    for d,c in coeff: F0[d]=c
    edge,pairs=incidences(M,primes,factors,coeff)
    result=dict(M=M,prime_count=len(primes),source_terms=len(coeff),
        greedy=path(M,primes,F0,edge,pairs,'greedy'),
        joint=path(M,primes,F0,edge,pairs,'joint'))
    result['seconds']=time.monotonic()-start
    Path(f'cutoff_{M}.json').write_text(json.dumps(result,indent=2))
    return result


def deadline(*_): raise TimeoutError('Frozen90seconddeadline')
def init():
    signal.signal(signal.SIGALRM,signal.SIG_DFL)
    signal.signal(signal.SIGTERM,signal.SIG_DFL)


if __name__=='__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(90)
    started=time.monotonic()
    failure=None
    try:
        with mp.get_context('fork').Pool(4,initializer=init) as pool:
            results=pool.map(cutoff,[512,1024,2048,8192])
    except Exception as exc:
        failure=repr(exc)
        results=[json.loads(p.read_text()) for p in sorted(Path('.').glob('cutoff_*.json'))]
    signal.alarm(0)
    out=dict(workers=4,seconds=time.monotonic()-started,failure=failure,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(Path('source_screen.py').read_bytes()).hexdigest(),results=results)
    Path('summary.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='results'}))
    print(json.dumps([dict(M=r['M'],seconds=r['seconds'],greedy_peak=r['greedy']['peak_ratio'],
        joint_peak=r['joint']['peak_ratio'],abandons_greedy=r['joint']['abandons_greedy'],
        recovering_positive_pairs=r['joint']['recovering_positive_pairs'],
        first_cross=r['joint']['first_cross']) for r in results]))
    if failure: raise SystemExit(2)
