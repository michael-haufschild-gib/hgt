import numpy as np, math
pi=math.pi
def poleModelDiff_raw(i, K):
    inv=1.0/i
    la=np.arange(i+1,i+1+K,dtype=float); Sa=np.concatenate(([0.0],np.cumsum(1.0/la)))[:K+1]; ahead=inv+2*Sa
    A=np.sum(1.0/np.expm1(ahead))
    lb=np.arange(i-1,0,-1,dtype=float); Sb=np.concatenate(([0.0],np.cumsum(1.0/lb))); behind=inv+2*Sb[:i]
    B=np.sum(1.0/np.expm1(behind))
    return (A-B)/i, ahead
def tail_analytic(i,K):
    # sum_{k>=K} poleExcess(ahead_k); ahead_k ~ 2 ln((i+k)/i), poleExcess~ i^2/(k(k+2i)); exact partial-fraction tail
    # sum_{k=K}^inf i^2/(k(k+2i)) = (i/2)*(psi(K+2i)-psi(K)) ; use exact digamma
    from mpmath import psi, mpf
    return float((i/2.0)*(psi(0, mpf(K)+2*i) - psi(0, mpf(K))))
print("i,  corrected i*(1-pm)  [target pi^2/16=%.5f]"%(pi*pi/16))
for i in [40,80,160,320,640]:
    K=4000000
    pm,ah=poleModelDiff_raw(i,K)
    tail=tail_analytic(i,K)
    # i*(1-pm_true) = i*(1-pm_K) - i*(tail/i) = i*(1-pm_K) - tail
    print("i=%4d  raw=%.5f  tail=%.5f  corrected=%.5f"%(i, i*(1-pm), tail, i*(1-pm)-tail))
