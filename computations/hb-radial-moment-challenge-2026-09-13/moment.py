import concurrent.futures as cf
import json
import os
import time
from pathlib import Path
import mpmath as mp

DEADLINE = float(os.environ['CAMPAIGN_DEADLINE'])

def budget():
    if time.monotonic() > DEADLINE - 5:
        raise TimeoutError('family compute deadline')

def cstr(z):
    return [mp.nstr(mp.re(z), mp.mp.dps), mp.nstr(mp.im(z), mp.mp.dps)]

def cc(z):
    return mp.mpc(*z)

def pars(rho, branch, side):
    s = rho-2 if branch else -rho-1
    w = -1-rho/2 if side else -2+rho/2
    c0 = (5*s*s+15*s+4)/4
    c1 = s*(s-1)*((s+2)*(2*s+3)-(w+1)*(w+2)/2)/4
    return w,s,c0,c1

def norm_ws(w,s):
    c0=(5*s*s+15*s+4)/4
    c1=s*(s-1)*((s+2)*(2*s+3)-(w+1)*(w+2)/2)/4
    return c0*mp.hyp2f1(-2*s,3,w+4,-1)+12*c1/((w+4)*(w+5))*mp.hyp2f1(-2*s,5,w+6,-1)

def value(rho,branch,side):
    budget()
    w,s,_,_=pars(rho,branch,side)
    return norm_ws(w,s)

def perimeter(lo,hi,n):
    corners=[mp.mpc('.01',lo),mp.mpc('.99',lo),mp.mpc('.99',hi),mp.mpc('.01',hi)]
    return [corners[j]+(corners[(j+1)%4]-corners[j])*mp.mpf(k)/n for j in range(4) for k in range(n)]

def contour(branch,side,lo,hi,n):
    z=perimeter(lo,hi,n)
    v=[value(x,branch,side) for x in z]
    increments=[mp.arg(v[(i+1)%len(v)]/v[i]) for i in range(len(v))]
    return dict(n=n,winding=mp.nstr(sum(increments)/(2*mp.pi),30),
                max_phase_step=mp.nstr(max(map(abs,increments)),30),
                minimum=mp.nstr(min(map(abs,v)),30),
                samples=[dict(rho=cstr(x),value=cstr(y)) for x,y in zip(z,v)])

def scan(job):
    start=time.monotonic()
    branch,side,lo,hi=job
    mp.mp.dps=50
    out=dict(kind='scan',job=job,contours=[],roots=[],failures=[])
    try:
        for n in [24,48]: out['contours'].append(contour(branch,side,lo,hi,n))
        last=out['contours'][-1]
        if float(last['winding']) > .5 or float(last['minimum']) < 1e-5:
            for frac in ['.1','.3','.5','.7','.9']:
                z=mp.mpc('.5',mp.mpf(lo)+(mp.mpf(hi)-mp.mpf(lo))*mp.mpf(frac))
                try:
                    root=mp.findroot(lambda r:value(r,branch,side),(z,z+mp.mpf('.01')),tol=mp.mpf('1e-42'),maxsteps=35)
                    residual=abs(value(root,branch,side))
                    if mp.mpf('.01') < root.real < mp.mpf('.99') and mp.mpf(lo)<root.imag<mp.mpf(hi) and residual<mp.mpf('1e-35'):
                        if not any(abs(root-cc(r['rho']))<mp.mpf('1e-20') for r in out['roots']):
                            out['roots'].append(dict(rho=cstr(root),residual=mp.nstr(residual,30)))
                except Exception as exc: out['failures'].append(str(exc)[:200])
    except Exception as exc: out['error']=str(exc)[:200]
    out['seconds']=time.monotonic()-start
    return out

def jacobi_series(n,w,s):
    term=mp.mpc(1); total=mp.mpc(0); small=0
    for k in range(6000):
        budget()
        rational=sum((-1)**j*mp.binomial(n,j)/(w+k+j+1) for j in range(n+1))
        add=term*rational
        total+=add
        if abs(add)<mp.eps*max(1,abs(total))/100: small+=1
        else: small=0
        if small>=12: return mp.power(2,2*s)*total,k+1
        term*=-(2*s-k)/(2*(k+1))
    raise ArithmeticError('series failed convergence criterion')

def validate(job):
    start=time.monotonic(); branch,side,seed=job
    out=dict(kind='validation',branch=branch,side=side,seed=seed,precision=[])
    try:
        for dps in [50,100,160]:
            mp.mp.dps=dps
            z=cc(seed)
            root=mp.findroot(lambda r:value(r,branch,side),(z,z+mp.mpf('.00001')),tol=mp.power(10,-dps+8),maxsteps=40)
            out['precision'].append(dict(dps=dps,rho=cstr(root),residual=mp.nstr(abs(value(root,branch,side)),dps)))
            seed=cstr(root)
        mp.mp.dps=190
        root=cc(seed); w,s,c0,c1=pars(root,branch,side)
        j2,k2=jacobi_series(2,w,s);j4,k4=jacobi_series(4,w,s);j0,k0=jacobi_series(0,w,s)
        independent=2*(c0*j2+c1*j4)/(2*mp.beta(3,w+1))
        d=2*s-w;e=w+2*s+2;E=e*(e+1)*(e+2)*(e+3)
        P=c0*(e+d*d)*(e+2)*(e+3)+c1*(d**4+(6*e+8)*d*d+3*e*(e+2))
        Q=d*(c0*(e+2)*(e+3)+c1*(d*d+5*e+8))
        out.update(independent_residual=cstr(independent),series_terms=[k0,k2,k4],
                   period_term=cstr(P*j0),boundary_term=cstr(Q),
                   decomposition_residual=cstr(E*2*(c0*j2+c1*j4)-2*(P*j0+Q)))
        # Nonzero nearby anchor protects against two methods sharing a false zero convention.
        anchor=root+mp.mpf('.001');wa,sa,ca,cb=pars(anchor,branch,side)
        ja,_=jacobi_series(2,wa,sa);jb,_=jacobi_series(4,wa,sa)
        other=(ca*ja+cb*jb)/mp.beta(3,wa+1)
        out['anchor']=dict(rho=cstr(anchor),value=cstr(other),discrepancy=cstr(other-value(anchor,branch,side)))
        circle=[root+mp.mpf('1e-5')*mp.exp(2j*mp.pi*k/32) for k in range(32)]
        vals=[value(z,branch,side) for z in circle]
        out['local_winding']=mp.nstr(sum(mp.arg(vals[(k+1)%32]/vals[k]) for k in range(32))/(2*mp.pi),50)
        out['derivative']=cstr(mp.diff(lambda z:value(z,branch,side),root))
    except Exception as exc: out['error']=str(exc)[:300]
    out['seconds']=time.monotonic()-start
    return out

def emit(out):
    with open('results.jsonl','a') as f: f.write(json.dumps(out)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['contours','precision']}),flush=True)

def main():
    start=time.monotonic();mp.mp.dps=50
    z=mp.mpc('.5',10)
    for b in [False,True]:
        for s in [False,True]: value(z,b,s)
    pilot=time.monotonic()-start
    estimate=pilot/4*20*4*72/14
    emit(dict(kind='pilot',seconds=pilot,estimated_parallel_contour_seconds=estimate))
    if estimate>300: raise RuntimeError('pilot admission rejected estimated contour budget')
    mp.mp.dps=60
    w=mp.mpc('-.3','.7');s=mp.mpc('-1.4','.2')
    c0=(5*s*s+15*s+4)/4;c1=s*(s-1)*((s+2)*(2*s+3)-(w+1)*(w+2)/2)/4
    def integrand(z):
        x=mp.sqrt(1-z)
        return mp.power(z,w)*x*mp.power(1+x,2*s-w)*(c0+c1*(1-z))
    direct=mp.quad(integrand,[0,mp.mpf('.1'),mp.mpf('.5'),1])/(2*mp.beta(3,w+1))
    err=abs(direct-norm_ws(w,s));emit(dict(kind='implementation_anchor',error=mp.nstr(err,60)))
    if err>mp.mpf('1e-35'): raise ArithmeticError('original source anchor failed')
    jobs=[(b,s,lo,hi) for b in [False,True] for s in [False,True] for lo,hi in [('.1','16'),('16','32'),('32','48'),('48','64'),('64','80')]]
    rows=[]
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        futures=[pool.submit(scan,job) for job in jobs]
        for future in cf.as_completed(futures):
            row=future.result()
            emit(row);rows.append(row)
        candidates=[]
        for row in sorted(rows,key=lambda r:jobs.index(tuple(r['job']))):
            for root in row['roots']: candidates.append((row['job'][0],row['job'][1],root['rho']))
        emit(dict(kind='candidate_count',count=len(candidates),validation_cap=8))
        futures=[pool.submit(validate,job) for job in candidates[:8]]
        for future in cf.as_completed(futures): emit(future.result())
    emit(dict(kind='complete',seconds=time.monotonic()-start))

if __name__=='__main__': main()
