import mpmath as mp

# fixed point set (regenerate at each precision), A=2,D=3 basis (ncol=30), order-1 over C(s)
seed_pts = [(1.5+2.0*(((i*9301+49297)%233280)/233280.0),
            -3+6*(((i*4096+150889)%714025)/714025.0)) for i in range(90)]

def run(kind, dps):
    mp.mp.dps = dps
    pts = [mp.mpc(re,im) for (re,im) in seed_pts]
    f=[]; fp=[]
    for s in pts:
        if kind=='euler2':
            F=1/(1-mp.e**(-s*mp.log(2))); Fp=mp.log(2)*(F-F**2)
        else:
            F=mp.gamma(s); Fp=F*mp.digamma(s)
        f.append(F); fp.append(Fp)
    A,D=2,3
    cols=[]
    for a in range(A+1):
        for i in range(D+1):
            for j in range(D+1-i):
                cols.append([(pts[k]**a)*(f[k]**i)*(fp[k]**j) for k in range(len(pts))])
    ncol=len(cols)
    # column-normalize
    for c in range(ncol):
        nrm=mp.sqrt(sum(abs(cols[c][k])**2 for k in range(len(pts))))
        if nrm!=0:
            cols[c]=[x/nrm for x in cols[c]]
    nfit=60
    M=mp.matrix([[cols[c][k] for c in range(ncol)] for k in range(len(pts))])
    Mf=mp.matrix([[cols[c][k] for c in range(ncol)] for k in range(nfit)])
    Mh=mp.matrix([[cols[c][k] for c in range(ncol)] for k in range(nfit,len(pts))])
    U,S,V=mp.svd(Mf)
    smin=S[ncol-1]
    # right singular vector for smallest S = last row of V (try, validate)
    v=mp.matrix([mp.conj(V[ncol-1,c]) for c in range(ncol)])
    def resid(Mx):
        y=Mx*v; return mp.sqrt(sum(abs(y[k])**2 for k in range(Mx.rows)))/mp.sqrt(sum(abs(v[k])**2 for k in range(ncol)))
    rf=resid(Mf); rh=resid(Mh)
    if rf>10*smin and rf>1e-3:  # convention fallback
        v=mp.matrix([V[ncol-1,c] for c in range(ncol)]); rf=resid(Mf); rh=resid(Mh)
    print(f"  {kind:7s} dps={dps:3d}: sigma_min(fit)={mp.nstr(smin,3)}  fit_res={mp.nstr(rf,3)}  HOLDOUT_res={mp.nstr(rh,3)}")

for kind in ('euler2','gamma'):
    print(f"--- {kind} (basis ncol=30, fit=60, hold=30) ---")
    for dps in (16,30,50):
        run(kind,dps)
print("\nDA  -> HOLDOUT_res tracks 10^-dps (real relation, precision-limited).")
print("HT  -> HOLDOUT_res PLATEAUS at a positive value (no relation; float64 'zero' was conditioning).")
