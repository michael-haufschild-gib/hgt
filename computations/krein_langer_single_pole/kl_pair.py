import numpy as np
np.random.seed(0)

def mpair(z, t): return 1.0/(t - z) + 1.0/(np.conj(t) - z)  # FE-symmetric conjugate pair

def pick(zs, t):
    N=len(zs); P=np.zeros((N,N),dtype=complex)
    for j in range(N):
        for k in range(N):
            P[j,k]=(mpair(zs[j],t)-np.conj(mpair(zs[k],t)))/(zs[j]-np.conj(zs[k]))
    return 0.5*(P+P.conj().T)

def sig(P,tol=1e-9):
    w=np.linalg.eigvalsh(P)
    return int((w>tol).sum()), int((w<-tol).sum()), int((np.abs(w)<=tol).sum()), w

t=0.5+1.0j
print("conjugate-pair carrier  m(z)=1/(t-z)+1/(tbar-z),  t=",t)
print("=== signature over random ℂ⁺ nodes ===")
for N in [2,3,4,6,8,12,16]:
    wn=None
    for _ in range(300):
        zs=np.random.uniform(-3,3,N)+1j*np.random.uniform(0.1,3,N)
        npos,nneg,nz,_=sig(pick(zs,t))
        if wn is None or nneg>wn[1]: wn=(npos,nneg,nz)
    print(f"N={N:2d}: worst-case (n+,n-,n0) = {wn}")

print("\n=== rank-1 v probe (does P + v v* become PSD?), N=8 ===")
N=8; zs=np.random.uniform(-3,3,N)+1j*np.random.uniform(0.1,3,N)
P=pick(zs,t); w,V=np.linalg.eigh(P)
print("eigs:",np.round(w,5))
idx=int(np.argmin(w)); lam=w[idx]; vstar=np.sqrt(-lam)*V[:,idx]
Pp=P+np.outer(vstar,vstar.conj()); 
print("min eig after +v v*:",round(np.linalg.eigvalsh(Pp).min(),9),"(>=0 ⟹ one rank-1 suffices ⟹ κ₋=1)")
def al(a,b): return abs(np.vdot(a,b))/(np.linalg.norm(a)*np.linalg.norm(b))
u=1/(t-zs); ub=1/(np.conj(t)-zs); bl=(zs-t)/(zs-np.conj(t))
cands={"u=1/(t-z)":u,"1/(tbar-z)":ub,"Blaschke (z-t)/(z-tbar)":bl,
       "u-ub":u-ub,"u+ub":u+ub,"u*bl":u*bl,"u/bl":u/bl,"u-ub over (z-tbar)?":(u-ub)}
print("phase-invariant alignment |cos| of v_neg:")
for n,c in cands.items(): print(f"  {al(vstar,c):.6f}  {n}")
