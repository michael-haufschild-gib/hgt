import os,time,json
from pathlib import Path
import mpmath as mp
DEADLINE=float(os.environ.get('CAMPAIGN_DEADLINE',time.monotonic()+570))
def budget():
    if time.monotonic()>DEADLINE-5: raise TimeoutError('whole-experiment deadline')
def enc(z): return [mp.nstr(mp.re(z),mp.mp.dps),mp.nstr(mp.im(z),mp.mp.dps)]
def dec(z): return mp.mpc(*z)
def zeros():
    return {int(a):mp.mpc('.5',b) for a,b in (l.strip().split('\t') for l in Path('zeros.tsv').read_text().splitlines() if not l.startswith('#'))}
def zeta(s,n=0):
    budget();return mp.zeta(s,derivative=n)
def lift(s,path,step=.10,tol=None):
    tol=mp.mpf(tol or '1e-'+str(mp.mp.dps-15));u=mp.mpf(0);end=mp.mpf(1)
    h=mp.mpf(step);hist=[];mind=mp.inf;reject=0
    while u<end:
        budget();h=min(h,end-u);w0=path(u);w1=path(u+h)
        d=zeta(s,1);mind=min(mind,abs(d));pred=(w1-w0)/d
        if abs(pred)>.22: h/=2;reject+=1;continue
        p=s+pred;c=p;ok=False
        for k in range(9):
            v=zeta(c)-w1
            if abs(v)<tol:ok=True;break
            dc=v/zeta(c,1)
            if abs(dc)>.35:break
            c-=dc
        if not ok or abs(c-p)>.06 or abs(c-s)>.3:
            h/=2;reject+=1
            if h<mp.mpf('1e-8'):raise ArithmeticError('step floor at '+str(u))
            continue
        if not (-6<mp.re(c)<12) or abs(mp.im(c))>1500:raise ArithmeticError('domain escape')
        s=c;u+=h;hist.append([str(u),*enc(s),str(abs(zeta(s)-w1))])
        if abs(c-p)<.012:h=min(h*mp.mpf('1.35'),mp.mpf(step))
    return s,dict(path=hist,min_abs_derivative=str(mind),rejected_steps=reject)
def target(kind,u):
    theta=2*mp.pi*u
    if kind=='reverse':theta=-theta
    if kind=='small':return mp.mpf('.35')*(1-mp.exp(1j*theta))
    if kind=='flat':return 1-mp.cos(theta)-mp.mpf('.5')*1j*mp.sin(theta)
    if kind=='tall':return 1-mp.cos(theta)-mp.mpf('1.5')*1j*mp.sin(theta)
    return 1-mp.exp(1j*theta)
def closest(s):
    zz=zeros();n=min(zz,key=lambda n:abs(s-zz[n]));return n,str(abs(s-zz[n]))
def save(name,data):Path(name).write_text(json.dumps(data,indent=2)+'\n')
