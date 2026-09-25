import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import mpmath as m
from arithmetic import task, ZERO_STR, encode

def em_zeta(s,N,M):
    value=m.mpc(0); deriv=m.mpc(0)
    for n in range(1,N):
        logn=m.log(n);term=m.exp(-s*logn)
        value+=term;deriv-=logn*term
    logn=m.log(N)
    term=m.exp((1-s)*logn)/(s-1)
    value+=term;deriv+=term*(-logn-1/(s-1))
    term=m.exp(-s*logn)/2
    value+=term;deriv-=logn*term
    rising=m.mpc(1); drising=m.mpc(0); previous=0
    for k in range(1,M+1):
        target=2*k-1
        for j in range(previous,target):
            drising=drising*(s+j)+rising
            rising*=s+j
        previous=target
        scale=m.bernoulli(2*k)/m.factorial(2*k)*m.exp((-s-2*k+1)*logn)
        value+=scale*rising
        deriv+=scale*(drising-logn*rising)
    return value,deriv

def independent(args):
    n,k=args;start=time.monotonic();m.mp.dps=185
    rho=m.mpc('.5',ZERO_STR[n])
    s=[m.mpf('2.5')*rho-1,rho/2,1-m.mpf('1.5')*rho][k]
    N=max(512,int(2*abs(s.imag))+512)
    a,da=em_zeta(s,N,150)
    b,db=em_zeta(s,N+64,166)
    reference=m.zeta(s);dref=m.zeta(s,derivative=1)
    return dict(n=n,factor=k,dps=185,N=N,M=150,zeta=encode(a),derivative=encode(da),
                relative_error=m.nstr(abs(a-reference)/abs(reference),30),
                derivative_relative_error=m.nstr(abs(da-dref)/max(1,abs(dref)),30),
                refined_difference=m.nstr(abs(a-b)/abs(b),30),
                refined_derivative_difference=m.nstr(abs(da-db)/max(1,abs(db)),30),
                seconds=time.monotonic()-start)

if __name__=='__main__':
    started=time.monotonic();count=0
    indices=list(range(1,129))+list(range(257,321))
    jobs=[(n,'.5',offset,dps) for n in indices for offset in ['-.25','0','.25'] for dps in [50,100,160]]
    with open('raw.jsonl','w',buffering=1) as out,mp.Pool(14) as pool:
        pilot=[j for j in jobs if j[0]==65]
        for batch in [pilot,[j for j in jobs if j[0]!=65]]:
            for row in pool.imap_unordered(task,batch):
                out.write(json.dumps(row)+'\n');count+=1
            print('arithmetic rows',count,'elapsed',time.monotonic()-started,flush=True)
        if time.monotonic()<float(os.environ['CAMPAIGN_DEADLINE'])-20:
            with open('independent.jsonl','w',buffering=1) as out2:
                for row in pool.imap_unordered(independent,[(n,k) for n in [10,49,52,54] for k in range(3)]):
                    out2.write(json.dumps(row)+'\n')
    Path('summary.json').write_text(json.dumps(dict(count=count,seconds=time.monotonic()-started),indent=2)+'\n')
