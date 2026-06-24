import mpmath as mp
# De-confounded plateau: residual vs UN-NORMALIZED coefficient height.
# Confound = power-basis collinearity: a small normalized sigma_min corresponds to
# huge un-normalized coefficients. Transcendence content = does height blow up to reach residual eps?
seed_pts=[(1.5+2.0*(((i*9301+49297)%233280)/233280.0),
          -3+6*(((i*4096+150889)%714025)/714025.0)) for i in range(130)]

def jets(s,n):
    G=mp.gamma(s); psi=mp.digamma(s); out=[G]
    if n>=2: out.append(G*psi)
    if n>=3: out.append(G*(psi**2+mp.polygamma(1,s)))
    return out[:n]

def tuples(n,D):
    if n==1:
        for e in range(D+1): yield (e,)
    else:
        for e in range(D+1):
            for rest in tuples(n-1,D-e): yield (e,)+rest

def measure(n,D,A,dps):
    mp.mp.dps=dps
    pts=[mp.mpc(re,im) for (re,im) in seed_pts]
    jv=[jets(s,n) for s in pts]
    raw=[]   # un-normalized columns
    for a in range(A+1):
        for ex in tuples(n,D):
            raw.append([(pts[k]**a)*mp.fprod([jv[k][t]**ex[t] for t in range(n)]) for k in range(len(pts))])
    ncol=len(raw)
    nu=[mp.sqrt(sum(abs(raw[c][k])**2 for k in range(len(pts)))) for c in range(ncol)]
    M=mp.matrix([[raw[c][k]/nu[c] for c in range(ncol)] for k in range(90)])
    U,S,V=mp.svd(M)
    smin=S[ncol-1]
    v=[mp.conj(V[ncol-1,c]) for c in range(ncol)]   # normalized null vector, ||v||=1
    # un-normalized coefficients w_c = v_c / nu_c  (so that sum w_c * raw_c = sum v_c * normcol_c)
    w=[v[c]/nu[c] for c in range(ncol)]
    wn=mp.sqrt(sum(abs(w[c])**2 for c in range(ncol)))
    winf=max(abs(w[c]) for c in range(ncol))
    # residual at UNIT un-normalized height: scale w to ||w||=1 -> residual scales by 1/wn
    resid_unit_height = smin/wn
    return ncol, smin, wn, winf, resid_unit_height

print("config         ncol  sigma_min(norm)  ||w||_un    height(inf)   residual@unit-height")
for (n,D,A) in [(1,3,2),(1,5,2),(1,7,2),(2,3,2),(2,5,2)]:
    ncol,smin,wn,winf,r=measure(n,D,A,30)
    print(f"n={n} D={D} A={A}  {ncol:4d}  {mp.nstr(smin,3):>12}  {mp.nstr(wn,3):>9}  {mp.nstr(winf,3):>10}  {mp.nstr(r,3):>12}")
print("\nKEY: if residual@unit-height STAYS BOUNDED below as (n,D) grow, the defect is a real")
print("transcendence invariant (height must blow up to shrink residual). If it decays fast too,")
print("the box-plateau is soft even de-confounded -> pivot to global/pole-lattice norm.")
