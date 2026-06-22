"""comp53+54 / rt#53,54 / gpt39 c1,c2.
Bulk H^- = H^0 - a_* v_* v_*^T, v_*=e(-0.16), a_*=(2.5)^{-2}=0.16, inertia(H^-)=(d,1).
a_c(y) = -1/(e(y)^T (H^-)^{-1} e(y)).  Tasks:
 (53) stationarity: a_c'(-0.16), a_c''(-0.16); true argmin of a_c near -0.16.
 (54) UNIFY (should be ONE identity, Sherman-Morrison): scalar Weyl gap
   s_d (Schur) = a_* + 1/(v_*^T(H^-)^{-1}v_*)
      (Christoffel) = 1/(v_*^T(H^0)^{-1}v_*) = 1/K_nu'(-0.16,-0.16)
      (margin)      = (2.5)^{-2} * margin_d.   Verify all agree."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
y0=mp.mpf('-0.16'); a_=mp.power(mp.mpf('2.5'),-2)
def ev(y,d,der=0):
    if der==0: return mp.matrix([mp.power(y,i) for i in range(d+1)])
    if der==1: return mp.matrix([ (i*mp.power(y,i-1) if i>=1 else mp.mpf(0)) for i in range(d+1)])
    if der==2: return mp.matrix([ (i*(i-1)*mp.power(y,i-2) if i>=2 else mp.mpf(0)) for i in range(d+1)])
def genmin(A,B):
    Li=mp.inverse(mp.cholesky(B)); C=Li*A*Li.T; return min(mp.eigsy((C+C.T)/2,eigvals_only=True))
for d in [8,12,16]:
    mp.mp.dps=int(6.5*d)+120
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)
    v=ev(y0,d); Hm=A-a_*(v*v.T); Hm=(Hm+Hm.T)/2; Mi=mp.inverse(Hm); Ai=mp.inverse(A)
    # (54) unification
    m=(v.T*Mi*v)[0]                       # v^T (H^-)^{-1} v  (<0)
    s_schur = a_ + 1/m
    K = (v.T*Ai*v)[0]                     # K_nu'(-0.16) = v^T (H^0)^{-1} v
    s_chris = 1/K
    margin = genmin(A,B); s_marg = a_*margin
    # (53) stationarity of a_c(y)=-1/f, f=e(y)^T Mi e(y)
    f   = (v.T*Mi*v)[0]
    fp  = 2*(ev(y0,d,1).T*Mi*v)[0]
    fpp = 2*(ev(y0,d,2).T*Mi*v)[0] + 2*(ev(y0,d,1).T*Mi*ev(y0,d,1))[0]
    acp = fp/f**2
    acpp= fpp/f**2 - 2*fp**2/f**3
    print(f"d={d}:")
    print(f"  [54 UNIFY] s(Schur)={mp.nstr(s_schur,8)}  s(Christoffel=1/K)={mp.nstr(s_chris,8)}  s(0.16*margin)={mp.nstr(s_marg,8)}")
    print(f"            agree: |Schur-Chris|/s={mp.nstr(abs(s_schur-s_chris)/abs(s_chris),2)}  |Chris-marg|/s={mp.nstr(abs(s_chris-s_marg)/abs(s_marg),2)}")
    print(f"  [53 STATIONARITY] a_c(-0.16)={mp.nstr(-1/f,8)}  a_c'(-0.16)={mp.nstr(acp,5)}  a_c''(-0.16)={mp.nstr(acpp,5)}")
    if d==12:
        # true argmin of a_c near -0.16 (maximize |f| in f<0): solve f'(y)=0 by findroot
        fpr=lambda y: 2*(ev(y,d,1).T*Mi*ev(y,d))[0]
        try:
            ymin=mp.findroot(fpr, y0); print(f"            true argmin a_c (f'(y)=0) near -0.16: y={mp.nstr(ymin,10)}  (offset {mp.nstr(ymin-y0,3)})")
        except Exception as e: print(f"            argmin solve: {e}")
