import concurrent.futures as cf
import json,time
from pathlib import Path
import mpmath as mp
import sympy as sp
import moment as m

def polynomial():
    x=sp.Symbol('x')
    def step(P,j):return sp.expand(x*((2-x)*(2+3*x)*sp.diff(P,x)+(12*x-3*j*(2-x))*P))
    def poly(n,k):
        p=(1-x)**n
        for i in range(k):p=step(p,2*i)
        return p
    p=5*(2+3*x)**4*poly(2,2)-sp.Rational(5,2)*(2+3*x)**6*poly(2,1)-sp.Rational(3,2)*(2+3*x)**8*poly(2,0)+sp.Rational(15,2)*poly(4,4)-sp.Rational(81,4)*(2+3*x)**2*poly(4,3)+15*(2+3*x)**4*poly(4,2)-sp.Rational(9,4)*(2+3*x)**6*poly(4,1)
    p=sp.expand(p)
    assert p.subs(x,0)==-384 and p.subs(x,1)==268750
    return [str(c) for c in sp.Poly(step(p,8),x).all_coeffs()]

def check(job):
    start=time.monotonic();kind,root,extra=job
    row=dict(kind=kind,root=root,parameters=extra)
    try:
        if kind=='kernel':
            dps,k,offset=extra;mp.mp.dps=dps+30
            rho=m.cc(root)+mp.mpf(offset);w,s,_,_=m.pars(rho,True,True)
            coefficients=[mp.mpf(c) for c in json.loads(Path('polynomial.json').read_text())]
            def integrand(u):
                m.budget()
                if u==0:return mp.mpc(0)
                x=u**k
                return k*u**(k-1)*mp.power(x,w)*mp.power(2-x,-4*w)*mp.polyval(coefficients,x)/(2-x)**8/(2+3*x)**10
            defect=mp.quad(integrand,[0,mp.mpf('.125'),mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.75'),1])
            normalized=2*(mp.mpf(86)/625-defect)
            target=(w+1)*2*mp.beta(3,w+1)*m.value(rho,True,True)
            row.update(value=m.cstr(normalized),discrepancy=m.cstr(normalized-target))
        else:
            mp.mp.dps=190;b,s=extra;rho=m.cc(root);w,rate,c0,c1=m.pars(rho,b,s)
            j2,n2=m.jacobi_series(2,w,rate);j4,n4=m.jacobi_series(4,w,rate)
            value=(c0*j2+c1*j4)/mp.beta(3,w+1)
            row.update(value=m.cstr(value),discrepancy=m.cstr(value-m.value(rho,b,s)),terms=[n2,n4])
    except Exception as e:row['error']=str(e)[:250]
    row['seconds']=time.monotonic()-start
    return row

def main():
    start=time.monotonic();Path('polynomial.json').write_text(json.dumps(polynomial())+'\n')
    roots=json.loads(Path('roots.json').read_text())
    z=next(r['rho'] for r in roots if r['branch'])
    jobs=[('kernel',z,(d,k,o)) for d in [50,100,160] for k in [4,6] for o in ['0','.001']]
    jobs += [('channels',r['rho'],(b,s)) for r in roots for b in [False,True] for s in [False,True]]
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        futures=[pool.submit(check,j) for j in jobs]
        for f in cf.as_completed(futures):
            row=f.result()
            with open('results.jsonl','a') as out:out.write(json.dumps(row)+'\n')
            print(json.dumps({k:v for k,v in row.items() if k!='root'}),flush=True)
    print(json.dumps(dict(kind='complete',seconds=time.monotonic()-start)),flush=True)

if __name__=='__main__':main()
