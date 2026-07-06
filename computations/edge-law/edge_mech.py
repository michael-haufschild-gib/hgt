import numpy as np, math
pi=math.pi
# poleModelDiff(2,i) with infinite ahead (cutoff K); ahead_k=1/i+2*sum_{l=i+1}^{i+k}1/l, behind_k=1/i+2*sum_{l=i-k}^{i-1}1/l
def poleExcess(u): return 1.0/np.expm1(u)
def poleModelDiff(i, K=400000):
    inv=1.0/i
    # ahead: cumulative harmonic from i+1
    la=np.arange(i+1, i+1+K, dtype=float); Sa=np.concatenate(([0.0],np.cumsum(1.0/la)))[:K+1] # Sa[k]=sum_{l=i+1}^{i+k}
    ahead=inv+2.0*Sa
    A=np.sum(poleExcess(ahead))
    lb=np.arange(i-1, 0, -1, dtype=float); Sb=np.concatenate(([0.0],np.cumsum(1.0/lb))) # Sb[k]=sum_{l=i-k}^{i-1}
    behind=inv+2.0*Sb[:i]
    B=np.sum(poleExcess(behind))
    return (A-B)/i
print("i,  i*(1-poleModelDiff(2,i))  [target pi^2/16=%.5f]"%(pi*pi/16))
for i in [40,80,160,320,640]:
    pm=poleModelDiff(i); print("i=%4d  i*(1-pm)=%.5f   pm=%.6f"%(i,i*(1-pm),pm))

# local factor: |F'(m)| * delta_i / i  -> target pi^2 ; using near poles of the c=2 harmonic gap
def localfactor(i, K=200000):
    inv=1.0/i
    la=np.arange(i+1,i+1+K,dtype=float); Sa=np.concatenate(([0.0],np.cumsum(1.0/la)))[:K+1]; ahead=inv+2*Sa
    lb=np.arange(i-1,0,-1,dtype=float); Sb=np.concatenate(([0.0],np.cumsum(1.0/lb))); behind=inv+2*Sb[:i]
    # |F'(m)| = (1/2) sum csch^2(dist/2) over all poles (behind + ahead)
    Fp = 0.5*(np.sum(1.0/np.sinh(behind/2.0)**2) + np.sum(1.0/np.sinh(ahead/2.0)**2))
    delta=2.0/i
    return Fp*delta/i
print("\ni,  |F'(m)|*delta_i/i  [target pi^2=%.5f]"%(pi*pi))
for i in [40,80,160,320]:
    print("i=%4d  Fp*delta/i=%.5f"%(i,localfactor(i)))
