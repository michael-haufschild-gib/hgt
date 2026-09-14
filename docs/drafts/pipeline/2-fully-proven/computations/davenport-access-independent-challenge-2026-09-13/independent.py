from carrier import *
import carrier as ca

def hz(s,a,N,M):
    v=mp.mpc(0);dv=mp.mpc(0)
    for n in range(N):
        ell=mp.log(n+a);term=mp.exp(-s*ell);v+=term;dv-=ell*term
    x=N+a;ell=mp.log(x);term=mp.exp((1-s)*ell)/(s-1)
    v+=term;dv+=term*(-ell-1/(s-1));term=mp.exp(-s*ell)/2;v+=term;dv-=ell*term
    prod=mp.mpc(1);dp=mp.mpc(0)
    for j in range(1,2*M):
        dp=dp*(s+j-1)+prod;prod*=s+j-1
        if j%2:
            fac=mp.bernoulli(j+1)/mp.factorial(j+1)*mp.exp((-s-j)*ell)
            v+=fac*prod;dv+=fac*(dp-prod*ell)
    return v,dv

def independent(s,N,M):
    co=[0,1,ca.K,-ca.K,-1];v=mp.mpc(0);dv=mp.mpc(0)
    for j in range(1,5):
        a,da=hz(s,mp.mpf(j)/5,N,M);v+=co[j]*a;dv+=co[j]*da
    fac=mp.exp(-s*mp.log(5));return fac*v,fac*(dv-mp.log(5)*v)

def check(s,w,dps,derivative=False,relative=False):
    configure(dps+60);N=max(96,int(abs(mp.im(s)))+80)
    a,da=independent(s,N,dps+25);bb,db=independent(s,N+40,dps+45)
    scale=abs(1-w) if relative else mp.mpf(1)
    r=dict(truncation_disagreement=str(abs(a-bb)),target_residual=str(abs(bb-w)),scaled_target_residual=str(abs(bb-w)/scale),native_disagreement=str(abs(bb-D(s))))
    if derivative:r.update(independent_derivative=enc(db),derivative_residual=str(abs(db)),derivative_truncation_disagreement=str(abs(da-db)),derivative_native_disagreement=str(abs(db-D(s,1))))
    configure(dps);return r
