import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import mpmath as m
import deformation as d

def pair(t):
    s=m.mpf('.5')+m.j*t
    pref=s*(s-1)/2*m.exp(-s/2*m.log(m.pi)+m.loggamma(s/2))
    ld=1/s+1/(s-1)+(m.digamma(s/2)-m.log(m.pi))/2
    z=m.zeta(s);dz=m.zeta(s,derivative=1)
    return m.re(pref*z),m.re(m.j*pref*(dz+ld*z))

def evaluator(params,direction,interaction):
    dx,dy=direction;norm=m.sqrt(dx*dx+dy*dy);a=m.mpf(dx)/norm;b=m.mpf(dy)/norm
    h=[{int(k):m.mpf(v) for k,v in params[name].items()} for name in ['h1','h2','h12']]
    cache={}
    def pieces(t):
        key=m.nstr(t,m.mp.dps+3)
        if key in cache:return cache[key]
        shifts={0}
        for hh in h:
            for k in hh:shifts.update([k,-k])
        vals={k:pair(t+k) for k in shifts}
        scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875')
        X=tuple(v/scale for v in vals[0])
        fields=[tuple(sum(c*(vals[k][j]+vals[-k][j])/2 for k,c in hh.items())/scale for j in [0,1]) for hh in h]
        D=tuple(a*fields[0][j]+b*fields[1][j] for j in [0,1])
        W=tuple(interaction*a*b*fields[2][j] for j in [0,1])
        cache[key]=(X,D,W);return X,D,W
    def discriminant(t):
        X,D,W=pieces(t);C=X[0]*D[1]-X[1]*D[0]
        if not interaction:return C
        A=X[0]*W[1]-X[1]*W[0];B=D[0]*W[1]-D[1]*W[0]
        return A*A-B*C
    def recover(t):
        X,D,W=pieces(t)
        if interaction:
            A=X[0]*W[1]-X[1]*W[0];B=D[0]*W[1]-D[1]*W[0];lam=-A/B
        else:lam=-X[0]/D[0]
        residual=[X[j]+lam*D[j]+lam*lam*W[j] for j in [0,1]]
        bound=abs(lam*a)+abs(lam*b)+interaction*abs(lam*lam*a*b)*m.mpf(params['h12_l1'])
        return lam,residual,bound
    return discriminant,recover

def scan(args):
    n,direction,interaction,params=args;begin=time.monotonic();m.mp.dps=50
    disc,recover=evaluator(params,direction,interaction)
    lo=m.mpf(d.ZEROS[n]);hi=m.mpf(d.ZEROS[n+1]);grid=[lo+(hi-lo)*j/32 for j in range(33)]
    values=[disc(t) for t in grid];roots=[];errors=[]
    for j in range(32):
        if values[j]*values[j+1]>=0:continue
        try:
            root=m.findroot(disc,(grid[j],grid[j+1]),solver='anderson',tol=m.mpf('1e-35'),maxsteps=60,verify=True)
            lam,res,bound=recover(root)
            if not grid[j]<=root<=grid[j+1]:raise ValueError('root left bracket')
            if max(abs(v) for v in res)>m.mpf('1e-25'):raise ValueError('original collision residual failed')
            roots.append(dict(t=m.nstr(root,50),lam=m.nstr(lam,50),positive_lam=bool(lam>0),
                              positivity_bound=m.nstr(bound,30),residual=[m.nstr(v,30) for v in res]))
        except Exception as e:errors.append(str(e)[:180])
    return dict(n=n,direction=direction,interaction=interaction,dps=50,roots=roots,errors=errors,seconds=time.monotonic()-begin)

def refine(args):
    item,dps,params=args;begin=time.monotonic();m.mp.dps=dps
    disc,recover=evaluator(params,item['direction'],item['interaction'])
    t=m.mpf(item['t'])
    root=m.findroot(disc,(t-m.mpf('1e-5'),t+m.mpf('1e-5')),tol=m.mpf(10)**(-dps+15),maxsteps=20,verify=True)
    lam,res,bound=recover(root)
    return dict(n=item['n'],direction=item['direction'],interaction=item['interaction'],dps=dps,
                t=m.nstr(root,dps),lam=m.nstr(lam,dps),positivity_bound=m.nstr(bound,dps),
                residual=[m.nstr(v,dps) for v in res],seconds=time.monotonic()-begin)

def source_check(args):
    item,params=args;begin=time.monotonic();m.mp.dps=190
    t=m.mpf(item['t']);lam=m.mpf(item['lam']);dx,dy=item['direction'];norm=m.sqrt(dx*dx+dy*dy)
    a=lam*dx/norm;b=lam*dy/norm
    h=[{int(k):m.mpf(v) for k,v in params[name].items()} for name in ['h1','h2','h12']]
    def source(x):
        ex=m.exp(x);v=m.mpf(0)
        for n in range(1,17):
            q=n*ex;q2=q*q
            v+=2*m.pi*(2*m.pi*q2*q2-3*q2)*m.exp(-m.pi*q2)
        return m.exp(x/2)*v
    def multiplier(x):
        hh=[sum(v*m.cos(k*x) for k,v in row.items()) for row in h]
        return 1+a*hh[0]+b*hh[1]+item['interaction']*a*b*hh[2]
    scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875')
    bounds=[0,m.mpf('.25'),m.mpf('.5'),m.mpf('.75'),1,m.mpf('1.5'),2,3]
    value=2*m.quad(lambda x:source(x)*multiplier(x)*m.cos(t*x),bounds)
    derivative=-2*m.quad(lambda x:x*source(x)*multiplier(x)*m.sin(t*x),bounds)
    _,recover=evaluator(params,item['direction'],item['interaction'])
    _,res,_=recover(t)
    # Compare at the supplied lambda, not the lambda re-inferred by recover.
    def shifted(hh,order):
        return sum(c*(pair(t+k)[order]+pair(t-k)[order])/2 for k,c in hh.items())
    expected=[pair(t)[j]+a*shifted(h[0],j)+b*shifted(h[1],j)+item['interaction']*a*b*shifted(h[2],j) for j in [0,1]]
    return dict(n=item['n'],direction=item['direction'],interaction=item['interaction'],dps=190,
                t=item['t'],lam=item['lam'],scaled_integral=[m.nstr(value/scale,80),m.nstr(derivative/scale,80)],
                relative_to_scale_errors=[m.nstr(abs(value-expected[0])/scale,50),m.nstr(abs(derivative-expected[1])/scale,50)],
                theta_terms=16,cutoff=3,seconds=time.monotonic()-begin)

if __name__=='__main__':
    start=time.monotonic();p50=d.prepare(70)
    jobs=[(n,v,i,p50) for n in [4,7,24] for v in [(1,1),(1,-1),(-1,1)] for i in [0,1]]
    allrows=[]
    with open('scan.jsonl','w',buffering=1) as out,mp.Pool(14) as pool:
        for row in pool.imap_unordered(scan,jobs):out.write(json.dumps(row)+'\n');allrows.append(row)
        print('discriminant cells',len(allrows),'elapsed',time.monotonic()-start,flush=True)
        selected=[]
        for row in allrows:
            for root in row['roots']:
                if root['positive_lam'] and m.mpf(root['positivity_bound'])<1:
                    selected.append(dict(n=row['n'],direction=row['direction'],interaction=row['interaction'],**root))
        p100=d.prepare(120);p160=d.prepare(180)
        Path('parameters.json').write_text(json.dumps({'70':p50,'120':p100,'180':p160},indent=2)+'\n')
        refined=[]
        with open('validation.jsonl','w',buffering=1) as out2:
            for row in pool.imap_unordered(refine,[(x,prec,p) for x in selected for prec,p in [(100,p100),(160,p160)]]):
                out2.write(json.dumps(row)+'\n');refined.append(row)
        print('refined roots',len(refined),'elapsed',time.monotonic()-start,flush=True)
        if time.monotonic()<float(os.environ['CAMPAIGN_DEADLINE'])-40:
            samples=[]
            for v in [(1,-1),(1,1),(-1,1)]:
                for interaction in [0,1]:
                    candidates=[x for x in refined if x['dps']==160 and tuple(x['direction'])==v and x['interaction']==interaction]
                    if candidates:samples.append(min(candidates,key=lambda x:float(x['lam'])))
            with open('source-validation.jsonl','w',buffering=1) as out3:
                for row in pool.imap_unordered(source_check,[(x,p160) for x in samples]):out3.write(json.dumps(row)+'\n')
    Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start),indent=2)+'\n')
