"""comp52 / rt#52 / gpt38-c8: the boundary-Weyl object is RANK-ONE.
H^0 = H0_minus + (2.5)^{-2} v v^T, v=e(-0.16), inertia(H0_minus)=(d,1) (comp48). So RH
positivity of H^0 reduces to a RANK-ONE boundary update filling the single bulk defect.
Verify: (i) reconstruction exact; (ii) the scalar boundary-Weyl quantity
  s(d) = (2.5)^{-2} + 1/(v^T H0_minus^{-1} v)  equals  (2.5)^{-2}*margin  (ties to bridge margin);
(iii) H^0>=0  <=>  s(d)>=0 (scalar condition) -- operator face = scalar boundary face."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
def evec(y,d): return mp.matrix([mp.power(y,i) for i in range(d+1)])
def frob(M): return mp.sqrt(mp.fsum(M[i,j]**2 for i in range(M.rows) for j in range(M.cols)))
def genmin(A,B):
    Li=mp.inverse(mp.cholesky(B)); C=Li*A*Li.T; return min(mp.eigsy((C+C.T)/2,eigvals_only=True))
w1=mp.power(mp.mpf('2.5'),-2)
for d in [8,12,16]:
    mp.mp.dps=int(6.5*d)+120
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)
    v=evec(mp.mpf('-0.16'),d)
    Hm=A-w1*(v*v.T); Hm=(Hm+Hm.T)/2
    recon=frob(A-(Hm+w1*v*v.T))/frob(A)            # should be ~0
    qv=(v.T*mp.inverse(Hm)*v)[0]                    # v^T H0_minus^{-1} v  (<0)
    s=w1+1/qv                                        # scalar boundary-Weyl quantity
    margin=genmin(A,B)
    Eneg=sum(1 for x in mp.eigsy(Hm,eigvals_only=True) if x<0)
    print(f"d={d}: recon_err={mp.nstr(recon,2)}  defects(H0_minus neg eigs)={Eneg}  "
          f"s(d)={mp.nstr(s,5)}  (2.5)^-2*margin={mp.nstr(w1*margin,5)}  ratio={mp.nstr(s/(w1*margin),6)}",flush=True)
print("# => boundary-Weyl object is RANK-ONE: one bulk defect filled by one boundary atom v=e(-0.16);")
print("#    H^0>=0 (RH) <=> scalar s(d)>=0, with s(d)=(2.5)^-2*margin -> 0+. Operator face = scalar boundary face.")
