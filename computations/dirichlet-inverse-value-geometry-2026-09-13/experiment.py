import common as c
from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed
CHARS={4:[0,1,0,-1],5:[0,1,-1,-1,1]}
Q=4

def L(s,n=0):
    budget();q=Q;v=mp.mpc(0);logq=mp.log(q)
    for r in range(1,q):
        if CHARS[q][r]:
            v+=CHARS[q][r]*sum(mp.binomial(n,j)*(-logq)**(n-j)*mp.zeta(s,mp.mpf(r)/q,derivative=j) for j in range(n+1))
    return mp.exp(-s*logq)*v

def starts(q):
    rr=next(z for z in json.loads(Path('carrier-controls.json').read_text()) if z['q']==q)
    return {int(k):mp.mpc('.5',v) for k,v in rr['located_roots'].items()}

def work(job):
    global Q
    q,label,kind=job;Q=q;c.zeta=L;mp.mp.dps=50;start=time.monotonic();zz=starts(q)
    # q4 odd has trivial roots -1,-3,...; q5 even has0,-2,... .
    tr={-m:mp.mpc(-(2*m-1) if q==4 else -2*(m-1)) for m in range(1,9)}
    ss=zz.get(label,tr.get(label));r=dict(q=q,label=label,kind=kind,dps=50)
    try:
        # Cached roots are independently corrected against the uncompleted L expression.
        for _ in range(3):ss-=L(ss)/L(ss,1)
        r['initial_residual']=str(abs(L(ss)))
        end,info=c.lift(ss,lambda u:target(kind,u),.018)
        candidates={str(n):s for n,s in zz.items()};candidates.update({'trivial_'+str(-n):s for n,s in tr.items()});candidates.update({'negative_'+str(n):mp.conj(s) for n,s in zz.items()})
        k=min(candidates,key=lambda k:abs(end-candidates[k]))
        r.update(status='ok',endpoint=enc(end),endpoint_label=[k,str(abs(end-candidates[k]))],**info)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('path-%d-%d-%s.json'%(q,label,kind),r)
    return {k:v for k,v in r.items() if k!='path'}
if __name__=='__main__':
    jobs=[(q,n,k) for q in [4,5] for n in list(range(1,6))+list(range(-1,-9,-1)) for k in ['circle','reverse','small','flat','tall']]
    rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilots=[jobs[0],jobs[65]];pilot=list(ex.map(work,pilots));rows.extend(pilot);save('pilot.json',dict(rows=pilot,seconds=time.monotonic()-start))
        for f in as_completed([ex.submit(work,j) for j in jobs if j not in pilots]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['q'],r['label'],r['kind'],r['status'],flush=True)
