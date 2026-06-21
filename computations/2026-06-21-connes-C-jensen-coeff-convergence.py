# 03 (rng-picked) — COEFFICIENT CONVERGENCE of Jensen J_{d,n} to Hermite, vs n. Light order.
import mpmath as mp, numpy as np
mp.mp.dps=50; half=mp.mpf(1)/2
def Xi(t): s=half+1j*t; return mp.re(half*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s))
d=4; ns=[6,12,20,30]; mo=2*(max(ns)+d)+2
co=mp.taylor(Xi,0,mo); a=[((-1)**n)*co[2*n] for n in range(max(ns)+d+1)]
He=np.array([3,0,-6,0,1],float); He=He/np.linalg.norm(He)   # He_4(x)=x^4-6x^2+3
print("d=%d Hermite He_4 normalized coeffs |.|: %s"%(d,np.round(np.abs(He),4)))
prev=None
for n in ns:
    J=np.array([float(mp.binomial(d,j)*a[n+j]) for j in range(d+1)])
    L=float(a[n+1]/a[n])
    Jr=np.array([J[j]*((-L)**(d-j)) for j in range(d+1)]); Jr=Jr/np.linalg.norm(Jr)
    err=float(np.linalg.norm(np.abs(Jr)-np.abs(He)))
    rate="" if prev is None else "  ratio=%.3f"%(err/prev)
    print("n=%2d: renorm-coeff err to Hermite=%.6f%s"%(n,err,rate)); prev=err
