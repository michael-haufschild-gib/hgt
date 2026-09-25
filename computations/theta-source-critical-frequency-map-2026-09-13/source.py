from common import *
import math
# P_(k+1)(q)=(1/2-2q)P_k(q)+2q P_k'(q); Phi^(k)=sum exp(z/2-q)P_k(q).
POLYS=[[0,-6,4]]
for k in range(3):
    p=POLYS[-1];a=[0]*(len(p)+1)
    for j,v in enumerate(p):a[j]+=(.5+2*j)*v;a[j+1]-=2*v
    POLYS.append(a)

def jets(z,order=2,extra=0,reflect=True):
    budget();sgn=-1 if reflect and mp.re(z)<0 else 1;zz=sgn*z;q1=mp.pi*mp.exp(2*zz);c=mp.re(q1)
    if c<=0 or abs(mp.im(z))>=mp.pi/4:raise ArithmeticError('outside source strip')
    N=int(mp.ceil(mp.sqrt(((mp.mp.dps+40)*mp.log(10))/c)))+6+extra
    if N>1000:raise ArithmeticError('term budget')
    vals=[mp.mpc(0) for k in range(order+1)];norm=mp.mpf(0)
    for n in range(1,N+1):
        q=n*n*q1;e=mp.exp(-(q-q1))
        for k in range(order+1):
            val=mp.polyval(list(reversed(POLYS[k])),q)*e;vals[k]+=val
            if k==0:norm+=abs(val)
    vals=[v*sgn**k for k,v in enumerate(vals)]
    return vals,norm,N,zz/2-q1

def solve(z,w=None):
    for it in range(45):
        budget();v,n,N,e=jets(z);h=v[0] if w is None else v[1]-1j*w*v[0];dh=v[1] if w is None else v[2]-1j*w*v[1]
        if abs(h)/n<mp.mpf('1e-34') and abs(h/dh)<mp.mpf('1e-30'):return z,dict(relative_residual=str(abs(h)/n),correction=str(abs(h/dh)),terms=N,iterations=it)
        ds=h/dh
        if abs(ds)>.13:ds*=mp.mpf('.13')/abs(ds)
        z-=ds
        if abs(mp.re(z))>3 or abs(mp.im(z))>=mp.mpf('.7849'):raise ArithmeticError('Newton domain escape')
    raise ArithmeticError('Newton iteration limit')
