"""Original time-sum and direct two-prime regrouping audit. Run only on RunPod."""
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import signal
import time
import mpmath as mf


def deadline(*_): raise TimeoutError('Frozen90secondauditdeadline')
def init():
    signal.signal(signal.SIGALRM,signal.SIG_DFL)
    signal.signal(signal.SIGTERM,signal.SIG_DFL)


def coefficient(d):
    n,p,factors=d,2,[]
    while p*p<=n:
        if n%p==0:
            n//=p
            factors.append(p)
            if n%p==0: return None
        p+=1
    if n>1: factors.append(n)
    return d,(-1)**len(factors)*mf.fsum(steps[k]*D[k//d] for k in range(d,M)),factors


def state(coeff,P):
    groups={}
    for d,c,factors in coeff:
        r=d
        for p in factors:
            if p in P: r//=p
        groups.setdefault(r,[]).append(c)
    return {r:mf.fsum(v) for r,v in groups.items()}


def successor(F,q):
    groups={}
    for r,c in F.items():
        label=r//q if r%q==0 else r
        groups.setdefault(label,[]).append(c)
    return {r:mf.fsum(v) for r,v in groups.items()}


def energy(F): return mf.fsum(v*v for v in F.values())
def show(x): return mf.nstr(x,70)


def row(i):
    p=remaining[i]
    out=[]
    for j in range(i+1,len(remaining)):
        q=remaining[j]
        endpoint=energy(successor(first_states[i],q))
        first=min(first_energies[i],first_energies[j])
        out.append((max(first,endpoint),endpoint,first,p,q))
    return out


if __name__=='__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(90)
    started=time.monotonic()
    mf.mp.dps=80
    raw=Path('summary.json').read_bytes()
    data=json.loads(raw)
    failures=[r for r in data['results'] if r['joint']['first_cross'] is not None]
    if failures:
        result=min(failures,key=lambda r:r['M'])
        index=result['joint']['first_cross']['batch_index']
        if index is None: index=len(result['joint']['batches'])-1
        selected=result['joint']['batches'][index]
        reason='first ceiling-crossing pair at smallest failing cutoff'
    else:
        changes=[r for r in data['results'] if any(b['abandons_greedy'] for b in r['joint']['batches'])]
        if changes:
            result=min(changes,key=lambda r:r['M'])
            selected=next(b for b in result['joint']['batches'] if b['abandons_greedy'])
            reason='first choice different from greedy at smallest such cutoff'
        else:
            result=min(data['results'],key=lambda r:r['M'])
            selected=result['joint']['batches'][0]
            reason='first pair at smallest cutoff; no failure or changed choice'
    M=result['M']
    P=set(selected['P'])
    D=[mf.mpf(0)]+[mf.loggamma(n+1)-sum(n//d for d in range(1,n+1))+2*mf.euler*n for n in range(1,M)]
    steps=[mf.sqrt(k+1)-mf.sqrt(k) for k in range(M)]
    with mp.get_context('fork').Pool(4,initializer=init) as pool:
        coeff=[v for v in pool.map(coefficient,range(1,M),chunksize=16) if v is not None]
    F=state(coeff,P)
    Q=energy(F)
    Q0=mf.fsum(c*c for d,c,f in coeff)
    remaining=[d for d,c,f in coeff if len(f)==1 and d not in P]
    first_states=[successor(F,p) for p in remaining]
    first_energies=[energy(G) for G in first_states]
    with mp.get_context('fork').Pool(4,initializer=init) as pool:
        candidates=[v for rows in pool.map(row,range(len(remaining)),chunksize=1) for v in rows]
    candidates.sort()
    best=candidates[0]
    p,q=selected['pair']
    chosen=next(v for v in candidates if (v[3],v[4])==tuple(sorted((p,q))))
    Qp=first_energies[remaining.index(p)]
    Qq=first_energies[remaining.index(q)]
    Qpq=energy(successor(successor(F,p),q))
    cofactors=[]
    for r in range(1,(M-1)//min(p,q)+1):
        if r%p==0 or r%q==0: continue
        h,a,b,c=[F.get(n,mf.mpf(0)) for n in (r,p*r,q*r,p*q*r)]
        if a==0 and b==0 and c==0: continue
        cofactors.append(dict(r=r,h=h,a=a,b=b,c=c,
            orientation=(h-c)*(a-b),symmetric=(h+c)*(a+b),mixed=2*(h*c+a*b)))
    ds=mf.fsum(t['orientation'] for t in cofactors)
    sy=mf.fsum(t['symmetric'] for t in cofactors)
    conflict=mf.fsum(abs(t['orientation']) for t in cofactors)-abs(ds)
    assert abs(min(Qp,Qq)-(Q+sy-abs(ds)))<mf.mpf('1e-65')
    assert abs(Qpq-Qp-Qq+Q-mf.fsum(t['mixed'] for t in cofactors))<mf.mpf('1e-65')
    assert abs(Qpq-mf.mpf(selected['predicted_end']))<mf.mpf('1e-8')*max(1,Q0)
    state_nonscalar=sum(1 for r,c in F.items() if r>1 and c and any(
        r%d==0 for d in range(2,math.isqrt(r)+1)))
    out=dict(M=M,P=sorted(P),reason=reason,pair=[p,q],digits=80,workers=4,
        seconds=time.monotonic()-started,remaining=len(remaining),pairs_checked=len(candidates),
        Q0=show(Q0),Q_before=show(Q),Q_first=show(Qp),Q_other_first=show(Qq),Q_end=show(Qpq),
        chosen_score=show(chosen[0]),minimum_score=show(best[0]),chosen_score_gap=show(chosen[0]-best[0]),
        minimum_pair=[best[3],best[4]],minimum_score_margin=show(candidates[1][0]-best[0]),
        order_conflict=show(conflict),local_first_floor=show(Q+sy-mf.fsum(abs(t['orientation']) for t in cofactors)),
        signed_orientation=show(ds),nonscalar_active_labels=state_nonscalar,
        cofactor_joint_nonzero=sum(t['c']!=0 for t in cofactors),
        cofactors=[{k:(v if k=='r' else show(v)) for k,v in t.items()} for t in cofactors],
        candidates=[dict(pair=[v[3],v[4]],score=show(v[0]),endpoint=show(v[1]),first=show(v[2])) for v in candidates],
        summary_sha256=hashlib.sha256(raw).hexdigest(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path('audit.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k not in ('cofactors','candidates')}))
