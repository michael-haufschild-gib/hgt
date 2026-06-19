import numpy as np
np.random.seed(1)
def pick(zs,t):
    N=len(zs);P=np.zeros((N,N),dtype=complex)
    def m(z): return 1/(t-z)+1/(np.conj(t)-z)
    for j in range(N):
        for k in range(N):
            P[j,k]=(m(zs[j])-np.conj(m(zs[k])))/(zs[j]-np.conj(zs[k]))
    return 0.5*(P+P.conj().T)

t=0.5+1.0j
print("Verify explicit factorization  P = ½(e+a)(e+a)* - ½(e-a)(e-a)*,  v=(e-a)/√2")
maxerr=0; minmin=1e9
for N in [2,3,5,8,13]:
    for tr in range(50):
        zs=np.random.uniform(-3,3,N)+1j*np.random.uniform(0.1,3,N)
        P=pick(zs,t)
        a=1/(t-zs); e=1/(np.conj(t)-zs)
        Prec=0.5*np.outer(e+a,(e+a).conj())-0.5*np.outer(e-a,(e-a).conj())
        err=np.abs(P-Prec).max(); maxerr=max(maxerr,err)
        v=(e-a)/np.sqrt(2)
        Pp=P+np.outer(v,v.conj())
        mn=np.linalg.eigvalsh(Pp).min(); minmin=min(minmin,mn)
print(f"  max |P - reconstruction|         = {maxerr:.3e}   (≈0 ⟹ identity holds)")
print(f"  min eigenvalue of P + v v*       = {minmin:.3e}   (≥0 ⟹ PSD ⟹ κ₋≤1)")
# and confirm rank-1 PSD target is exactly ½(e+a)(e+a)*
zs=np.random.uniform(-3,3,6)+1j*np.random.uniform(0.1,3,6)
P=pick(zs,t); a=1/(t-zs); e=1/(np.conj(t)-zs); v=(e-a)/np.sqrt(2)
Pp=P+np.outer(v,v.conj()); target=0.5*np.outer(e+a,(e+a).conj())
print(f"  max |P + v v* - ½(e+a)(e+a)*|    = {np.abs(Pp-target).max():.3e}")
print("  eigs of P+v v*:",np.round(np.linalg.eigvalsh(Pp),6),"(rank-1 PSD)")
