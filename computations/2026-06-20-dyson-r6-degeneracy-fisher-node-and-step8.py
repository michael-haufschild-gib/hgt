import numpy as np, mpmath as mp
mp.mp.dps=40
# ---- STEP 6 (NODE): Neff-H0 degeneracy through a conserved observable. ----
# toy: early-universe acoustic combo C1 = H0*sqrt(1+0.13*Neff) (sets r_s/theta*); local probe C2=H0.
def C1(p): Neff,H0=p; return H0*np.sqrt(1+0.13*Neff)
def grad(C,p,h=1e-6):
    p=np.array(p,float); g=np.zeros(2)
    for i in range(2):
        e=np.zeros(2); e[i]=h; g[i]=(C(p+e)-C(p-e))/(2*h)
    return g
p0=[3.046,67.0]
g1=grad(C1,p0)
F1=np.outer(g1,g1)                         # Fisher from single observable: rank 1
w1=np.linalg.eigvalsh(F1)
print(f"single observable theta*: Fisher eigenvalues {w1[0]:.2e},{w1[1]:.2e} -> degeneracy (1 null dir)")
# degeneracy direction = null eigvec; move along it -> C1 ~ const
nulldir=np.linalg.eigh(F1)[1][:,0]
dC_along=C1(np.array(p0)+0.5*nulldir)-C1(p0); dC_perp=C1(np.array(p0)+0.5*g1/np.linalg.norm(g1))-C1(p0)
print(f"  move along null: dC1={dC_along:+.4f} (flat)   move along grad: dC1={dC_perp:+.4f} (steep)")
g2=grad(lambda p:p[1],p0)                  # C2 = H0 (independent gradient)
F=F1+np.outer(g2,g2); w=np.linalg.eigvalsh(F)
print(f"add independent observable H0: Fisher eigenvalues {w[0]:.2e},{w[1]:.2e} -> degeneracy {'BROKEN' if w[0]>1e-6 else 'remains'}")

# ---- STEP 8 (minimal edit, not-HT-blind): 'find the conserved combination / Fisher null' on HT VALUES.
# degeneracy <=> a value relation Sum c_k f(s+k)=0 with poly-in-s coeffs (shift-value matrix rank). ----
def relrank(f, sdeg=2, ord=2, npts=12, tol=1e-18):
    rows=[]
    for m in range(npts):
        s=mp.mpf('1.7')+mp.mpf('0.3')*m
        row=[]
        for k in range(ord+1):
            for d in range(sdeg+1):
                row.append(complex(s**d * f(s+k)))
        rows.append(row)
    A=np.array(rows)
    sv=np.linalg.svd(A,compute_uv=False)
    return sv.min()/sv.max()
for name,f in [("Gamma (DA)",mp.gamma),("zeta (HT)",mp.zeta),("control 1/(s+1) (rational)",lambda s:1/(s+1))]:
    print(f"  HT-transfer value-relation min/max sv  {name:26s}: {relrank(f):.2e}")
