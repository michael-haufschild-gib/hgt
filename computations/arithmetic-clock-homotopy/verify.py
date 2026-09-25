"""Runpod-only checks without a Hurwitz-zeta call."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[key]='1'
import concurrent.futures
import json
import mpmath as mp

def finite_cell(u,a,m,left,right):
    c=a+m
    def f(x):
        return (x**(1-u)/(1-u)+(2*c+1)*x**(-u)/u-c*(c+1)*x**(-u-1)/(u+1))/2
    return f(right)-f(left)

def verify_large(params):
    h_text,r_text=params
    mp.mp.dps=150
    h,r=mp.mpf(h_text),mp.mpf(r_text)
    a=1/h
    t=2*mp.pi*r/h
    u=mp.mpc(-1,-t)
    count=512
    x=a+count
    finite=mp.im(a*a**(-mp.j*t)*mp.fsum(finite_cell(u,a,m,a+m,a+m+1) for m in range(count)))
    mean=a/(12*t)*(1-mp.cos(t*mp.log(x/a)))
    approx=finite+mean
    # P(r)=r(1-r)(1-2r)/12, |P| <= 1/48 on [0,1].
    tail_bound=a*(1+abs(1-mp.j*t))/(48*x)
    return dict(h=h_text,ratio=r_text,k=1,dps=150,cells=count,
                finite_plus_mean=mp.nstr(approx,90),tail_bound=mp.nstr(tail_bound,40),
                lower=mp.nstr(approx-tail_bound,70),upper=mp.nstr(approx+tail_bound,70))

def verify_small(params):
    h_text,r_text=params
    mp.mp.dps=150
    h,r=mp.mpf(h_text),mp.mpf(r_text)
    a=1/h
    t=2*mp.pi*r/h
    u=mp.mpc(-1,-t)
    top=a*mp.exp(h/r)
    mmax=int(mp.floor(top-a))
    cells=[(m,a+m,min(a+m+1,top)) for m in range(mmax+1)]
    via_primitive=mp.im(a*a**(-mp.j*t)*mp.fsum(finite_cell(u,a,m,left,right) for m,left,right in cells))
    def f(x):
        y=x-a
        fract=y-mp.floor(y)
        return a*(fract*fract-fract)/2*mp.sin(t*mp.log(x/a))/x
    direct=mp.fsum(mp.quad(f,[left,right]) for m,left,right in cells)
    return dict(h=h_text,ratio=r_text,k=1,dps=150,finite=mp.nstr(via_primitive,90),
                quadrature=mp.nstr(direct,90),method_difference=mp.nstr(abs(direct-via_primitive),10))

if __name__=='__main__':
    with concurrent.futures.ProcessPoolExecutor(max_workers=6) as pool:
        large=list(pool.map(verify_large,[('16','0.99'),('64','0.5'),('1024','0.5')]))
        small=list(pool.map(verify_small,[('0.37','0.99'),('0.83','0.5'),('1','0.99')]))
    with open('verification.json','w') as out:
        json.dump(dict(large=large,small=small),out,indent=2)
    print(json.dumps(dict(large=large,small=small),indent=2),flush=True)
