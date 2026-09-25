import discovery as d
from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def hz(s,a,N,M):
    v=mp.fsum(mp.exp(-s*mp.log(n+a)) for n in range(N));x=N+a;logx=mp.log(x)
    v+=mp.exp((1-s)*logx)/(s-1)+mp.exp(-s*logx)/2;prod=mp.mpc(1)
    for j in range(1,2*M):
        prod*=s+j-1
        if j%2:v+=mp.bernoulli(j+1)/mp.factorial(j+1)*prod*mp.exp((-s-j)*logx)
    return v

def independent(s,q,N,M):
    return mp.exp(-s*mp.log(q))*sum(d.CHARS[q][r]*hz(s,mp.mpf(r)/q,N,M) for r in range(1,q) if d.CHARS[q][r])

def work(job):
    q,n,k,dps=job;d.Q=q;d.c.zeta=d.L;mp.mp.dps=dps;start=time.monotonic();r=dict(q=q,n=n,kind=k,dps=dps)
    try:
        s=d.starts(q)[n]
        for _ in range(6):s-=d.L(s)/d.L(s,1)
        end,info=d.c.lift(s,lambda u:target(k,u),.008)
        checks=[];mp.mp.dps=dps+50
        for ix in sorted(set(round(j*(len(info['path'])-1)/8) for j in range(9))):
            row=info['path'][ix];u=mp.mpf(row[0]);sp=mp.mpc(row[1],row[2]);N=max(96,int(abs(mp.im(sp)))+80)
            a=independent(sp,q,N,dps+25);bb=independent(sp,q,N+40,dps+45)
            checks.append(dict(u=str(u),truncation_disagreement=str(abs(a-bb)),target_residual=str(abs(bb-target(k,u))),native_disagreement=str(abs(bb-d.L(sp)))))
        mp.mp.dps=dps;r.update(status='ok',endpoint=enc(end),checks=checks,**info)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d-%s-%d.json'%(q,n,k,dps),r)
    return {k:v for k,v in r.items() if k!='path'}
if __name__=='__main__':
    jobs=[(q,n,k,dps) for q,n,k in [(4,1,'circle'),(5,1,'circle'),(4,5,'circle'),(5,5,'circle'),(5,4,'small')] for dps in [100,160]]
    rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['q'],r['n'],r['kind'],r['dps'],r['status'],flush=True)
