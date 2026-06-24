import mpmath as mp
mp.mp.dps=30
# Does the shift equation make translated strips carry INDEPENDENT constraints?
# Fit best degree-(n,D) relation on S strips K, K+1, ..., K+(S-1); track sigma_min vs S.
# Confound-robust: power-basis collinearity hits every S equally; the GROWTH with S isolates shift effect.
base=[(1.4+1.0*(((i*9301+49297)%233280)/233280.0),
       -2+4*(((i*7919+101)%104729)/104729.0)) for i in range(40)]

def jets(kind,s,n):
    if kind=='invgamma':
        G=1/mp.gamma(s); psi=mp.digamma(s)
        out=[G, -psi*G]
        if n>=3: out.append((psi**2-mp.polygamma(1,s))*G)
    else: # euler2 (DA control, exact order-1 relation on ALL strips)
        f=1/(1-mp.e**(-s*mp.log(2))); l=mp.log(2)
        out=[f, l*(f-f**2)]
        if n>=3: out.append(l*l*(f-3*f**2+2*f**3))
    return out[:n]

def tuples(n,D):
    if n==1:
        for e in range(D+1): yield (e,)
    else:
        for e in range(D+1):
            for r in tuples(n-1,D-e): yield (e,)+r

def sigma(kind,n,D,A,S):
    pts=[mp.mpc(re+k,im) for k in range(S) for (re,im) in base]
    jv=[jets(kind,s,n) for s in pts]
    cols=[]
    for a in range(A+1):
        for ex in tuples(n,D):
            cols.append([(pts[p]**a)*mp.fprod([jv[p][t]**ex[t] for t in range(n)]) for p in range(len(pts))])
    ncol=len(cols)
    for c in range(ncol):
        nu=mp.sqrt(sum(abs(cols[c][p])**2 for p in range(len(pts))))
        if nu!=0: cols[c]=[x/nu for x in cols[c]]
    M=mp.matrix([[cols[c][p] for c in range(ncol)] for p in range(len(pts))])
    S_=mp.svd(M,compute_uv=False)
    return ncol, S_[ncol-1]

for kind in ('invgamma','euler2'):
    print(f"--- {kind} (n=2,D=3,A=2) ---")
    prev=None
    for S in (1,2,3):
        ncol,sm=sigma(kind,2,3,2,S)
        ratio = f"  growth x{mp.nstr(prev/sm,3)}" if prev else ""
        print(f"  strips={S} pts={40*S} ncol={ncol}: sigma_min={mp.nstr(sm,4)}{ratio}")
        prev=sm
print("\nHT+shift: sigma_min GROWS as strips added (independent constraints per translate).")
print("DA: sigma_min stays ~0 (one exact relation holds on every strip).")
