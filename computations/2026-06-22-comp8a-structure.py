"""comp8a / rt#38: does the bridge STRUCTURE reproduce for genuine Dirichlet L?
For zeta and each real primitive chi: margin(d)=lambda_min(H^0,M_triv^own),
exponent e_d (normalized by that function's gamma_d), lambda_max(K_d), and
dangerous-direction overlap with pole vector u=(-4)^i. Key: y=-4 is the POLE for zeta,
a TRIVIAL ZERO for even-chi L, ABSENT for odd-chi L. Does overlap stay ~0.97 regardless?"""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py"); L=imp("hgtlib_L","hgtlib_L.py")
DMAX=24; DPS=int(5*float(mp.log10(mp.factorial(DMAX))))+160

def find_gammas(name,n):
    mp.mp.dps=40
    if name=='zeta':
        return H.load_zeros('zeros.txt', n)
    Z=lambda t: mp.re(L.xi_chi(name, mp.mpf('0.5')+1j*mp.mpf(t)))
    gs=[]; t=mp.mpf('0.2'); vp=Z(t)
    while len(gs)<n and t<200:
        t+=mp.mpf('0.1'); v=Z(t)
        if vp==0 or v*vp<0:
            g=mp.findroot(Z,t-mp.mpf('0.05'))
            if g>0.05 and (not gs or abs(g-gs[-1])>1e-3): gs.append(g)
        vp=v
    return gs

def run(name):
    gammas=find_gammas(name, DMAX+2)
    mp.mp.dps=DPS
    if name=='zeta':
        T=H.T_moments_exact(2*DMAX+1); B=H.Mtriv_matrix(DMAX)
    else:
        T=L.T_moments_L(name,2*DMAX+1); a=L.CHARS[name][1]; B=L.Mtriv_L_matrix(DMAX,a)
    A=H.H0_matrix(DMAX,T)
    sub=lambda Mx,d: mp.matrix([[Mx[i,j] for j in range(d+1)] for i in range(d+1)])
    print(f"## {name}  (dps={DPS}, gamma_1={mp.nstr(gammas[0],8)})")
    prev=None
    for d in range(2,DMAX+1):
        Ad,Bd=sub(A,d),sub(B,d)
        Lc=mp.cholesky(Bd); Li=mp.inverse(Lc); C=Li*Ad*Li.T; C=(C+C.T)/2
        if d in (10,20,24):
            E,Q=mp.eigsy(C); idx=min(range(len(E)),key=lambda i:E[i]); m=E[idx]
            q=mp.matrix([Q[r,idx] for r in range(d+1)]); c=Li.T*q; ov=H.overlap_with_pole(c)
            extra=f"  overlap_u={mp.nstr(ov,5)}"
        else:
            E=mp.eigsy(C,eigvals_only=True); m=min(E); extra=""
        lg=float(mp.log10(m)) if m>0 else float('nan')
        es=f"{float(-mp.log(m/prev)/mp.log(gammas[d-1])):6.3f}" if (prev and m>0) else "  --  "
        flag="" if m>0 else "  <-- NOT PSD (lambda_max>1)"
        if d in (10,15,20,24): print(f"  d={d:2d}  log10(margin)={lg:11.4f}  e_d={es}{extra}{flag}",flush=True)
        prev=m if m>0 else None
for nm in ['zeta','chi4','chi3','chi5','chi8']:
    run(nm)
