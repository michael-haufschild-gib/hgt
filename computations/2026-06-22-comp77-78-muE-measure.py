"""comp77 (gpt/43 #7) + comp78 (gpt/43 #8) — mu_E signed-measure reconstruction & F_E singularities.

Reuse comp63's e_n extraction: E = (H^0 - M_triv) in protector basis x=y+0.16, e_n = off-tridiagonal
Hankel symbol, e_n = mu_E[x^n].  Then:
 comp77: leading node x* = lim e_{n+1}/e_n  -> a_*+y_1 = 0.16 + 1/gamma_1^2 = 0.165 ?  signed Gaussian
         quadrature (Hankel pencil H1 v = x H0 v) for the top nodes/weights; inertia growth vs d
         (comp63 found (5,12) at d=18: does the negative count grow, or saturate?).
 comp78: F_E(z)=sum e_n z^n, Pade [k/k]; poles at z=1/x_alpha (support) ? natural boundary (poles on a circle) ?"""
import mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
y0=mp.mpf('-0.16')
def shiftS(d):
    S=mp.zeros(d+1,d+1)
    for i in range(d+1):
        for j in range(i+1): S[j,i]=mp.binomial(i,j)*mp.power(-y0,i-j)
    return S
def get_e(d):
    mp.mp.dps=int(7*d)+130
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d); RP=A-B
    S=shiftS(d); RPx=S.T*RP*S
    e={}
    for n in range(2,2*d-1):
        vals=[(i,RPx[i,n-i]) for i in range(max(0,n-d),min(d,n)+1) if 0<=n-i<=d and abs(2*i-n)>=2]
        if vals: e[n]=vals[len(vals)//2][1]
    return e

GAMMA1=mp.mpf('14.134725141734693790457251983562')
X_TARGET = mp.mpf('0.16') + 1/GAMMA1**2          # a_* + y_1
print(f"target leading node x* = a_*+y_1 = 0.16 + 1/gamma_1^2 = {mp.nstr(X_TARGET,10)}")

print("\n=== comp77: leading node (e_{n+1}/e_n) convergence to a_*+y_1, and inertia growth ===")
for d in (12,18,24,30):
    e=get_e(d); ns=sorted(e)
    rat=[e[ns[k+1]]/e[ns[k]] for k in range(len(ns)-1)]
    lead=rat[-1]
    # signed Gaussian quadrature: Hankel pencil on available moments
    nlo=ns[0]; m=(len(ns))//2 - 1
    if m>=2:
        H0=mp.matrix(m,m); H1=mp.matrix(m,m); ok=True
        for i in range(m):
            for j in range(m):
                a=nlo+i+j; b=a+1
                if a in e and b in e: H0[i,j]=e[a]; H1[i,j]=e[b]
                else: ok=False
        nodes=[]
        if ok:
            try:
                Ev=mp.eig(mp.inverse(H0)*H1, left=False, right=False)
                nodes=sorted([mp.re(x) for x in Ev if abs(mp.im(x))<mp.mpf('1e-6')], key=lambda t:-abs(t))
            except Exception: nodes=[]
        # inertia of full Hankel block
        ev=mp.eigsy((H0+H0.T)/2,eigvals_only=True)
        npos=sum(1 for x in ev if x>0); nneg=sum(1 for x in ev if x<0)
        sc=sum(1 for k in range(len(ns)-1) if e[ns[k]]*e[ns[k+1]]<0)
        topn=[mp.nstr(x,6) for x in nodes[:4]]
        print(f" d={d}: lead e_{{n+1}}/e_n={mp.nstr(lead,8)} (target {mp.nstr(X_TARGET,6)}, err {mp.nstr(abs(lead-X_TARGET),2)}); "
              f"Hankel inertia=({npos},{nneg}); sign-changes={sc}; top nodes={topn}")

print("\n=== comp78: F_E(z)=sum e_n z^n  Pade poles (support 1/x_alpha? natural boundary?) ===")
d=30; e=get_e(d); ns=sorted(e)
# build a Taylor list from n=nlo.. (shift so series starts at z^0); F_E ~ sum_{k} e_{nlo+k} z^k
coeffs=[e[n] for n in ns]
K=len(coeffs)//2 - 1
try:
    p,q=mp.pade(coeffs, K, K)
    roots=mp.polyroots(list(reversed(q)), maxsteps=200, extraprec=200)
    poles=sorted([r for r in roots], key=lambda r: abs(r))
    print(f" Pade [{K}/{K}] on {len(coeffs)} coeffs; nearest poles |z| and 1/z (=x support pt):")
    for r in poles[:6]:
        print(f"   z={mp.nstr(r,6)}  |z|={mp.nstr(abs(r),6)}  1/z={mp.nstr(1/r,6)}  (target x*={mp.nstr(X_TARGET,6)})")
    mods=[float(abs(r)) for r in poles[:8]]
    print(f" pole-|z| spread (clustered=>simple poles; spread on a ring=>natural boundary): {[round(m,4) for m in mods]}")
except Exception as ex:
    print(" pade failed:", ex)
print("\nDONE")
