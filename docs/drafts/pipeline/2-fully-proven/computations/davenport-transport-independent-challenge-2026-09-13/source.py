from common import *
from functools import lru_cache

def config(host):
    if host=='D':
        k=(mp.sqrt(5)/2-mp.sin(2*mp.pi/5))/mp.sin(4*mp.pi/5);return 5,1,[0,1,k,-k,-1]
    if host=='B4':return 4,1,[0,1,0,-1]
    if host=='L5':return 5,0,[0,1,-1,-1,1]
    raise ValueError(host)

def raw_jets(host,z,order=2,reflect=False):
    budget();sgn=-1 if reflect and mp.re(z)<0 else 1;z=sgn*z
    if abs(mp.im(z))>=mp.pi/4:raise ArithmeticError('source strip')
    if host=='R':q=1;gamma=mp.mpf('.5');coeff=None;parity=0;polys=[[0,-6,4]]
    else:q,parity,coeff=config(host);gamma=mp.mpf('.5')+parity;polys=[[1]]
    Q=mp.pi*mp.exp(2*z)/q;c=mp.re(Q)
    if c<=0:raise ArithmeticError('no Gaussian damping')
    N=int(mp.ceil(mp.sqrt((mp.mp.dps+70)*mp.log(10)/c)))+3
    if N>1500:raise ArithmeticError('source term cap')
    for k in range(order):
        p=polys[-1];a=[mp.mpf(0)]*(len(p)+1)
        for j,v in enumerate(p):a[j]+=(gamma+2*j)*v;a[j+1]-=2*v
        polys.append(a)
    out=[mp.mpc(0) for _ in polys];norm=mp.mpf(0)
    for n in range(1,N+1):
        co=1 if coeff is None else coeff[n%q]*n**parity
        if co==0:continue
        t=n*n*Q;e=co*mp.exp(-(t-Q))
        for j,p in enumerate(polys):
            v=e*mp.polyval(p[::-1],t);out[j]+=v
            if j==0:norm+=abs(v)
    factor=1 if host=='R' else 2
    return [factor*v*sgn**j for j,v in enumerate(out)],factor*norm,gamma*z-Q,N

def phi(host,z):
    v,n,e,N=raw_jets(host,z,0,False);return v[0]*mp.exp(e)

def completed(host,w):
    s=mp.mpf('.5')+1j*w
    if host=='R':return s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)/2
    q,a,c=config(host);L=mp.power(q,-s)*mp.fsum(c[r]*mp.zeta(s,mp.mpf(r)/q) for r in range(1,q))
    return mp.power(mp.mpf(q)/mp.pi,(s+a)/2)*mp.gamma((s+a)/2)*L

def poly(z,x):
    z=dec(z) if isinstance(z,list) else z
    if abs(mp.re(z))<mp.mpf('1e-40'):return 1+x*x/mp.im(z)**2
    return (1-x*x/z**2)*(1-x*x/mp.conj(z)**2)

class Transform:
    def __init__(self,host,remove=None,insert=None,hden=64,dps=60):
        mp.mp.dps=dps;self.host=host;self.remove=remove or [];self.insert=insert or [];self.h=mp.mpf(1)/hden;self.x=[];self.weights=[]
        for j in range(int(mp.mpf('3.5')*hden)+1):
            x=j*self.h;v=mp.re(phi(host,x))
            for z in self.remove:v/=mp.re(poly(z,x))
            for z in self.insert:v*=mp.re(poly(z,x))
            self.x.append(x);self.weights.append((1 if j==0 else 2)*self.h*v)
        self.mass=mp.fsum(self.weights);self.m2=mp.fsum(x*x*v for x,v in zip(self.x,self.weights))/self.mass;self.min_weight=min(self.weights)
        self.weights=[v/self.mass for v in self.weights]
    def val(self,w,jet=True):
        budget();c=mp.cos(w*self.h);s=mp.sin(w*self.h);cj=mp.mpc(1);sj=mp.mpc(0);F=mp.mpc(0);D=mp.mpc(0)
        for x,a in zip(self.x,self.weights):
            F+=a*cj
            if jet:D-=a*x*sj
            cj,sj=cj*c-sj*s,sj*c+cj*s
        return (F,D) if jet else F
    def root(self,w):
        w=mp.mpc(w)
        for k in range(42):
            f,d=self.val(w);step=f/d
            if abs(step)<mp.mpf('1e-22'):return w,dict(residual=str(abs(f)),correction=str(abs(step)),iterations=k)
            if abs(step)>3:step*=3/abs(step)
            w-=step
            if not(0<mp.re(w)<115 and abs(mp.im(w))<40):raise ArithmeticError('root domain escape')
        raise ArithmeticError('root iteration limit')

def controls(host):
    mp.mp.dps=60;T=Transform(host);checks=[]
    for w in [mp.mpf('0'),mp.mpf('9.5'),mp.mpc('30','.2'),mp.mpc('85','.3')]:
        v=T.val(w,False)*T.mass;ref=completed(host,w);err=abs(v-ref)/max(abs(ref),mp.mpf('1e-50'));checks.append(dict(w=enc(w),relative_error=str(err)));assert err<mp.mpf('1e-24'),(host,str(w),str(err))
    sym=[]
    for z in [mp.mpc('.3','.2'),mp.mpc('.8','.4')]:
        err=abs(phi(host,z)-phi(host,-z))/max(abs(phi(host,z)),mp.mpf('1e-50'));sym.append(str(err));assert err<mp.mpf('1e-48'),(host,'reflection',str(err))
    extra={}
    if host=='B4':
        z=mp.mpc('.2','.3');Q=mp.exp(-mp.pi*mp.exp(2*z));ref=mp.exp(3*z/2)*mp.jtheta(1,0,Q,derivative=1);extra['jacobi_relative_error']=str(abs(phi(host,z)-ref)/abs(ref))
    return dict(host=host,mass=str(T.mass),second_moment=str(T.m2),completion_checks=checks,reflection_checks=sym,**extra)
