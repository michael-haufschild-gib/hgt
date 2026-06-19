import numpy as np
np.random.seed(0)

def m(z, t): return 1.0/(t - z)

def pick(zs, t):
    N = len(zs)
    P = np.zeros((N,N), dtype=complex)
    for j in range(N):
        for k in range(N):
            num = m(zs[j], t) - np.conj(m(zs[k], t))
            den = zs[j] - np.conj(zs[k])
            P[j,k] = num/den
    return P

def signature(P, tol=1e-9):
    w = np.linalg.eigvalsh(P)  # Hermitian
    npos = int(np.sum(w >  tol))
    nneg = int(np.sum(w < -tol))
    nzero= int(np.sum(np.abs(w) <= tol))
    return npos, nneg, nzero, w

t = 0.5 + 1.0j   # off-line pole, Im t = 1 > 0
print("t =", t, " Im t =", t.imag)
print("=== signature of single-off-line-pole Pick matrix, random ℂ⁺ nodes ===")
for N in [2,3,4,6,8,12]:
    worst = None
    for trial in range(200):
        zs = np.random.uniform(-3,3,N) + 1j*np.random.uniform(0.1,3,N)
        P = pick(zs, t)
        # Hermitize numerically
        P = 0.5*(P + P.conj().T)
        npos,nneg,nz,w = signature(P)
        if worst is None or nneg>worst[1]:
            worst=(npos,nneg,nz)
    print(f"N={N:2d}:  worst-case (n+,n-,n0) over 200 trials = {worst}")

print()
print("=== closed-form probe for the rank-1 v (P + v v* PSD), N=6 ===")
N=6
zs = np.random.uniform(-3,3,N) + 1j*np.random.uniform(0.1,3,N)
P = pick(zs,t); P=0.5*(P+P.conj().T)
w,V = np.linalg.eigh(P)
print("eigenvalues:", np.round(w,5))
# negative eigenvector
idx = int(np.argmin(w))
lam = w[idx]; vneg = V[:,idx]
print("most-negative eigenvalue:", round(lam,6))
vstar = np.sqrt(-lam)*vneg   # P + vstar vstar^H should kill the negative eig
Pp = P + np.outer(vstar, vstar.conj())
wp,_ = np.linalg.eigh(Pp)
print("after +v v*: min eig =", round(wp.min(),8), " (>=0 ⟹ PSD)")
# compare vstar to candidate closed forms (up to global phase/scale)
def align(a,b):
    # cosine-similarity magnitude (phase-invariant)
    return abs(np.vdot(a,b))/(np.linalg.norm(a)*np.linalg.norm(b))
u   = 1.0/(t - zs)          # Cauchy data at pole t
ubar= 1.0/(np.conj(t) - zs) # reflected
bl  = (zs - t)/(zs - np.conj(t))  # Blaschke factor values
cands = {
  "u=1/(t-z)": u,
  "1/(tbar-z)": ubar,
  "u*(z-tbar)/(z-t) [=1/(t-z)*1/Blaschke]": u/bl,
  "u*Blaschke": u*bl,
  "(z-t)/(z-tbar)=Blaschke": bl,
  "1/(t-z)/(t-z)": u*u,
}
print("phase-invariant alignment |cos| of v_neg with candidates:")
for name,c in cands.items():
    print(f"  {align(vstar,c):.6f}   {name}")
