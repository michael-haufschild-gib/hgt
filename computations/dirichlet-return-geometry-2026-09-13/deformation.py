import json
import math
import multiprocessing as mp
import os
import time
from pathlib import Path
import mpmath as m

ZEROS={}
for line in Path('zeros.tsv').read_text().splitlines():
    if line.strip() and not line.startswith('#'):
        a,b=line.split()[:2];ZEROS[int(a)]=b

def xi_jets(t):
    s=m.mpf('.5')+m.j*t
    pref=s*(s-1)/2*m.exp(-s/2*m.log(m.pi)+m.loggamma(s/2))
    logd=1/s+1/(s-1)+(m.digamma(s/2)-m.log(m.pi))/2
    logdd=-1/s**2-1/(s-1)**2+m.polygamma(1,s/2)/4
    z=m.zeta(s);dz=m.zeta(s,derivative=1);ddz=m.zeta(s,derivative=2)
    return (m.re(pref*z),m.re(m.j*pref*(dz+logd*z)),
            m.re(-pref*(ddz+2*logd*dz+(logd**2+logdd)*z)))

def moments(freq):
    value,_,second=xi_jets(m.mpf(freq));return value,-second

def prepare(dps=70):
    m.mp.dps=dps
    def annihilator(freqs):
        col=[moments(k) for k in freqs]
        A=m.matrix([[col[j][i] for j in [0,1]] for i in [0,1]])
        rhs=m.matrix([-col[2][i] for i in [0,1]])
        x=m.lu_solve(A,rhs);v=[x[0],x[1],m.mpf(1)];norm=sum(abs(c) for c in v)
        return {k:c/norm for k,c in zip(freqs,v)}
    h1=annihilator([2,4,6]);h2=annihilator([3,5,7]);product={}
    for a,c in h1.items():
        for b,d in h2.items():
            for k in [a+b,abs(a-b)]:product[k]=product.get(k,0)+c*d/2
    residual=[sum(c*moments(k)[j] for k,c in product.items()) for j in [0,1]]
    A=m.matrix([[moments(k)[j] for k in [0,4]] for j in [0,1]])
    comp=m.lu_solve(A,m.matrix(residual))
    h12=dict(product)
    for k,c in zip([0,4],comp):h12[k]=h12.get(k,0)-c
    allh=[h1,h2,h12]
    residuals=[[m.nstr(sum(c*moments(k)[j] for k,c in h.items()),dps) for j in [0,1]] for h in allh]
    result=dict(dps=dps,h1={str(k):m.nstr(v,dps) for k,v in h1.items()},
                h2={str(k):m.nstr(v,dps) for k,v in h2.items()},
                h12={str(k):m.nstr(v,dps) for k,v in h12.items()},
                moment_residuals=residuals,h12_l1=m.nstr(sum(abs(c) for c in h12.values()),dps),
                compensation_matrix_condition=m.nstr(m.cond(A),20))
    return result

def task(args):
    n,direction,interaction,params=args;begin=time.monotonic();m.mp.dps=50
    h=[{int(k):m.mpf(v) for k,v in params[name].items()} for name in ['h1','h2','h12']]
    dx,dy=direction
    norm=m.sqrt(dx*dx+dy*dy);a=m.mpf(dx)/norm;b=m.mpf(dy)/norm
    lo=m.mpf(ZEROS[n]);hi=m.mpf(ZEROS[n+1]);t0=(lo+hi)/2
    cache={}
    def jets(t):
        if not 5<t<m.mpf(ZEROS[65])+10:raise ValueError('iterate left admitted search window')
        key=m.nstr(t,55)
        if key in cache:return cache[key]
        shifts={0}
        for hh in h:
            for k in hh:shifts.update([k,-k])
        X={k:xi_jets(t+k) for k in shifts}
        values=[X[0]]
        for hh in h:
            values.append(tuple(sum(c*(X[k][j]+X[-k][j])/2 for k,c in hh.items()) for j in range(3)))
        cache[key]=values
        return values
    def pieces(t,lam):
        X,U,V,W=jets(t)
        F=[X[j]+lam*(a*U[j]+b*V[j])+interaction*lam**2*a*b*W[j] for j in range(3)]
        Fl=[a*U[j]+b*V[j]+2*interaction*lam*a*b*W[j] for j in range(2)]
        scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875')
        logd=-m.pi/4+m.mpf('1.75')*t/(1+t*t)
        return F,Fl,scale,logd
    def fun(t,lam):
        F,_,scale,_=pieces(t,lam);return F[0]/scale,F[1]/scale
    def jac(t,lam):
        F,Fl,scale,ld=pieces(t,lam)
        return m.matrix([[(F[1]-ld*F[0])/scale,Fl[0]/scale],[(F[2]-ld*F[1])/scale,Fl[1]/scale]])
    try:
        X,U,V,W=jets(t0);linear=a*U[0]+b*V[0]
        initial=abs(X[0]/linear) if linear else m.mpf('.01')
        root=m.findroot(fun,(t0,initial),J=jac,tol=m.mpf('1e-30'),maxsteps=18,verify=True)
        tstar,lam=root;res=fun(tstar,lam)
        bound=abs(lam*a)+abs(lam*b)+interaction*abs(lam*lam*a*b)*m.mpf(params['h12_l1'])
        return dict(n=n,direction=direction,interaction=interaction,dps=50,t=m.nstr(tstar,50),
                    lam=m.nstr(lam,50),positive_lam=bool(lam>0),in_seed_gap=bool(lo<tstar<hi),
                    positivity_bound=m.nstr(bound,30),in_positive_source_region=bool(bound<1),
                    scaled_residual=[m.nstr(v,30) for v in res],seconds=time.monotonic()-begin)
    except Exception as exc:
        return dict(n=n,direction=direction,interaction=interaction,error=str(exc)[:220],seconds=time.monotonic()-begin)

if __name__=='__main__':
    start=time.monotonic();params=prepare()
    Path('parameters.json').write_text(json.dumps(params,indent=2)+'\n')
    directions=[(1,0),(-1,0),(0,1),(0,-1),(1,1),(1,-1),(-1,1),(-1,-1)]
    configurations=[(d,i) for d in directions for i in ([0,1] if d[0]*d[1] else [0])]
    count=0
    with open('raw.jsonl','w',buffering=1) as out,mp.Pool(14) as pool:
        for indices in [[1],range(2,65)]:
            begin=time.monotonic()
            jobs=[(n,d,i,params) for n in indices for d,i in configurations]
            seconds=[]
            for row in pool.imap_unordered(task,jobs):
                out.write(json.dumps(row)+'\n');count+=1;seconds.append(row['seconds'])
            print('rows',count,'elapsed',time.monotonic()-start,flush=True)
            if count==12:
                estimate=63*sum(seconds)/14
                remaining=float(os.environ['CAMPAIGN_DEADLINE'])-time.monotonic()
                if estimate>remaining:
                    print('pilot rejects full scan; estimate',estimate,'remaining',remaining,flush=True);break
    Path('summary.json').write_text(json.dumps(dict(count=count,seconds=time.monotonic()-start),indent=2)+'\n')
