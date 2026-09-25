from source import *

def phi_independent(host,z):
    budget();E=mp.exp(2*z)
    if host=='R':
        Q=mp.exp(-mp.pi*E)
        return mp.exp(z/2)*(mp.pi**2*E**2*mp.jtheta(3,0,Q,derivative=4)/8+3*mp.pi*E*mp.jtheta(3,0,Q,derivative=2)/4)
    q,a,c=config(host);Q=mp.exp(-mp.pi*E/q);total=mp.mpc(0)
    for r in range(q):
        cr=mp.fsum(c[b]*mp.exp(-2j*mp.pi*r*b/q) for b in range(q))/q
        value=mp.jtheta(3,mp.pi*r/q,Q,derivative=a)
        if a==0:value-=1  # sum_r C_r=c_0=0; remove cancelling constant exactly
        total+=cr*value/(2j)**a
    return mp.exp((mp.mpf('.5')+a)*z)*total

class Independent:
    def __init__(self,T,hden,shift):
        self.points=[];self.weights=[];h=mp.mpf(1)/hden;y=mp.mpf(shift)
        for j in range(int(mp.mpf('3.5')*hden)+1):
            budget();z=j*h+1j*y;v=phi_independent(T.host,z)
            for a in T.remove:v/=poly(a,z)
            for a in T.insert:v*=poly(a,z)
            v*=h/T.mass;self.points.append(z);self.weights.append(v)
            if j:self.points.append(-mp.conj(z));self.weights.append(mp.conj(v))
    def val(self,w):
        F=mp.mpc(0);D=mp.mpc(0)
        for z,a in zip(self.points,self.weights):
            v=a*mp.exp(1j*w*z);F+=v;D+=1j*z*v
        return F,D
