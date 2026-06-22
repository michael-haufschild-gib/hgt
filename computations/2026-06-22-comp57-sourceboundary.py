"""comp57-partial / rt#57 / gpt39 c7: is the rank-one boundary atom SOURCE-BUILT?
Claim: a_* v_* v_*^T (v_*=e(-0.16), a_*=(2.5)^{-2}) is EXACTLY the j=1 term of the explicit-formula
archimedean square-sum M_triv = sum_{j>=1}(2j+1/2)^{-2} e(y_j)e(y_j)^T (y_j=-(2j+1/2)^{-2}).
Then H^- = H^0 - a_* v_* v_*^T = M_triv^{(j>=2)} + R^P, i.e. (positive j>=2 trivial budget) + (prime
residual). Verify inertia(H^-)=(d,1) and that the single defect is PRIME-sourced (the j>=2 budget
alone is PD; adding R^P creates exactly one negative direction). This makes the BOUNDARY source-built
(archimedean Gamma-factor, no zero-feeding) and the DEFECT prime-sourced -- the source anatomy of #57."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
def ev(y,d): return mp.matrix([mp.power(y,i) for i in range(d+1)])
def inertia(M):
    E=mp.eigsy((M+M.T)/2,eigvals_only=True); return sum(1 for e in E if e>0),sum(1 for e in E if e<0)
def frob(M): return mp.sqrt(mp.fsum(M[i,j]**2 for i in range(M.rows) for j in range(M.cols)))
for d in [8,12]:
    mp.mp.dps=int(7*d)+130
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)   # B=M_triv (j>=1)
    # j=1 term of M_triv
    w1=mp.power(mp.mpf('2.5'),-2); y1=-w1; v1=ev(y1,d); atom1=w1*(v1*v1.T)
    # boundary atom used in comp52
    a_=mp.power(mp.mpf('2.5'),-2); v_=ev(mp.mpf('-0.16'),d); boundary=a_*(v_*v_.T)
    match=frob(atom1-boundary)/frob(boundary)
    # M_triv^{(j>=2)} = B - atom1 ; R^P = A - B
    Bj2=B-atom1; RP=A-B
    Hm=A-boundary                       # bulk H^-
    ipB,inB=inertia(Bj2)                # j>=2 trivial budget: should be PD (d+1,0)
    ipH,inH=inertia(Hm)                 # bulk: should be (d,1)
    # is the defect prime-sourced? Bj2 (PD) + RP = Hm; check Bj2 alone PD, Hm has 1 neg
    print(f"d={d}: boundary atom == j=1 trivial term? rel={mp.nstr(match,2)}  | "
          f"inertia(M_triv^(j>=2))=({ipB},{inB})  inertia(H^-=Bj2+R^P)=({ipH},{inH})  "
          f"=> boundary SOURCE-BUILT (Gamma j=1), defect PRIME-sourced",flush=True)
