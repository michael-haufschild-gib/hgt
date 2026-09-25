"""Independent original-time-formula witness audit. Run only on supplied RunPod."""
import hashlib
import json
from pathlib import Path
import signal
import time
import mpmath as m


def deadline(*_): raise TimeoutError('Frozen90secondauditdeadline')
signal.signal(signal.SIGALRM,deadline)
signal.alarm(90)
start=time.monotonic()
m.mp.dps=80
raw=Path('summary.json').read_bytes()
data=json.loads(raw)
flagged=[(r,s) for r in data['results'] for s in r['states'] if s['violation']]
if not flagged: raise RuntimeError('No audit trigger')
r,s=min(flagged,key=lambda rs:(rs[0]['M'],rs[1]['index']))
M,P=r['M'],set(s['P'])
print('Auditing',M,sorted(P),flush=True)
D=[m.mpf(0)]+[m.loggamma(n+1)-sum(n//d for d in range(1,n+1))+2*m.euler*n for n in range(1,M)]
steps=[m.sqrt(k+1)-m.sqrt(k) for k in range(M)]
F={}
source=[]
for d in range(1,M):
    rem,trial,primes,squarefree=d,2,[],True
    while trial*trial<=rem:
        if rem%trial==0:
            rem//=trial
            primes.append(trial)
            if rem%trial==0:
                squarefree=False
                break
        trial+=1
    if not squarefree: continue
    if rem>1: primes.append(rem)
    v=(-1)**len(primes)*m.fsum(steps[k]*D[k//d] for k in range(d,M))
    label=d
    for p in primes:
        if p in P: label//=p
    F.setdefault(label,[]).append(v)
    source.append(v)
F={r:m.fsum(vs) for r,vs in F.items()}
G={}
for label,v in F.items(): G.setdefault(label//17 if label%17==0 else label,[]).append(v)
G={r:m.fsum(vs) for r,vs in G.items()}
T0=m.fsum(v*v for r,v in F.items() if r not in (1,2))
T1=m.fsum(v*v for r,v in G.items() if r not in (1,2))
gain=T1-T0
diagonal=m.fsum(v*v for v in source)
terms=[]
for label,b in F.items():
    if label%17: continue
    partner=label//17
    a=F.get(partner,m.mpf(0))
    change=-b*b if partner in (1,2) else 2*a*b
    terms.append((label,partner,a,b,change))
assert abs(m.fsum(t[4] for t in terms)-gain)<m.mpf('1e-65')
assert gain>m.mpf('1e-10')*max(1,diagonal)
assert abs(gain-m.mpf(s['gain']))<m.mpf('1e-10')*max(1,diagonal)
show=lambda v:m.nstr(v,70)
out=dict(M=M,P=sorted(P),digits=80,seconds=time.monotonic()-start,
    gain=show(gain),normalized_gain=show(gain/diagonal),
    diagonal=show(diagonal),transverse_before=show(T0),transverse_after=show(T1),
    screen_gain_error=show(abs(gain-m.mpf(s['gain']))),
    head=show(F.get(1,0)),two=show(F.get(2,0)),
    terms=[dict(label=t[0],partner=t[1],a=show(t[2]),b=show(t[3]),change=show(t[4]))
        for t in sorted(terms,key=lambda t:-abs(t[4]))],
    summary_sha256=hashlib.sha256(raw).hexdigest(),
    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('audit.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:v for k,v in out.items() if k!='terms'}))
print(json.dumps(out['terms'][:8]))
