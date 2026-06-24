import numpy as np, mpmath as mp
mp.mp.dps = 40
rng = np.random.default_rng(7)
Npts = 150
pts = [mp.mpc(1.5 + 2.0*rng.random(), -3 + 6*rng.random()) for _ in range(Npts)]

def vals(kind):
    f=[]; fp=[]
    for s in pts:
        if kind=='euler2':
            F = 1/(1-mp.e**(-s*mp.log(2))); Fp = mp.log(2)*(F-F**2)
        elif kind=='gamma':
            F = mp.gamma(s); Fp = F*mp.digamma(s)
        f.append(complex(F)); fp.append(complex(Fp))
    return np.array(f), np.array(fp), np.array([complex(s) for s in pts])

def basis(f,fp,s,A,D):
    cols=[]
    for a in range(A+1):
        for i in range(D+1):
            for j in range(D+1-i):
                cols.append((s**a)*(f**i)*(fp**j))
    M=np.array(cols).T
    norms=np.linalg.norm(M,axis=0); norms[norms==0]=1
    return M/norms

def probe(kind, configs):
    f,fp,s = vals(kind)
    nfit=90; idx=np.arange(len(s)); fit=idx[:nfit]; hold=idx[nfit:]
    print(f"--- {kind} ---")
    for (A,D) in configs:
        M=basis(f,fp,s,A,D); ncol=M.shape[1]
        sigma_in=np.linalg.svd(M,compute_uv=False)[-1]
        Mf=M[fit]; Mh=M[hold]
        Vh=np.linalg.svd(Mf)[2]; v=Vh[-1].conj()
        res_fit=np.linalg.norm(Mf@v)/np.linalg.norm(v)
        res_hold=np.linalg.norm(Mh@v)/np.linalg.norm(v)
        print(f"  A={A} D={D} ncol={ncol:3d} (fit rows={nfit}): in-sample sigma_min={sigma_in:.2e}  fit_res={res_fit:.2e}  HOLDOUT_res={res_hold:.2e}")

configs=[(0,2),(2,3),(4,4),(6,5),(8,6)]
probe('euler2', configs)
probe('gamma', configs)
print("\nVERDICT KEY: Euler-factor (DA) -> HOLDOUT_res ~ machine zero at every basis (real relation generalizes).")
print("Gamma (HT) -> fit_res collapses as ncol->fit rows (OVERFIT) but HOLDOUT_res stays bounded away from 0.")
