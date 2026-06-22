"""comp66 / rt#66: is the bulk H^- a (signed) moment matrix in SOME coordinate?
H^-=H^0−a_* v_* v_*^T (split-independent). A moment matrix is Hankel (M_{ij}=mu[x^{i+j}])
in the right coordinate. Test the Hankel-DEFECT of H^- across coordinate families (shift y->y+t),
and whether H^- is Hankel up to a similarity. H^0 IS Hankel (T_{i+j+1}); subtracting the rank-one
a_*v_*v_*^T breaks Hankel by a rank-2 amount. Question: can a coordinate make H^- Hankel again
(=> moment problem / Krein-string applies) or is it irreducibly non-Hankel (=> need a genuine
operator/canonical system, not a moment problem)."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
def ev(y,d): return mp.matrix([mp.power(y,i) for i in range(d+1)])
def shiftS(d,t):
    S=mp.zeros(d+1,d+1)
    for i in range(d+1):
        for j in range(i+1): S[j,i]=mp.binomial(i,j)*mp.power(t,i-j)  # (y+t)^i
    return S
def hankel_defect(M):  # fraction of Frobenius energy in antidiagonal-variation (0 iff Hankel)
    n=M.rows; dev=mp.mpf(0); tot=mp.mpf(0)
    for s in range(2*n-1):
        vals=[M[i,s-i] for i in range(max(0,s-n+1),min(n-1,s)+1)]
        mn=mp.fsum(vals)/len(vals); dev+=mp.fsum((v-mn)**2 for v in vals); tot+=mp.fsum(v**2 for v in vals)
    return mp.sqrt(dev/tot)
for d in [10,14]:
    mp.mp.dps=int(7*d)+130
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T)
    a_=mp.power(mp.mpf('2.5'),-2); v=ev(mp.mpf('-0.16'),d); Hm=A-a_*(v*v.T)
    print(f"d={d}: Hankel-defect of H^0 (should be 0) = {mp.nstr(hankel_defect(A),2)}")
    # scan shift coordinate y->y+t; report min Hankel-defect of S^T H^- S
    best=None
    for t100 in range(-400,400,5):
        t=mp.mpf(t100)/100; S=shiftS(d,t); Hs=S.T*Hm*S; hd=hankel_defect(Hs)
        if best is None or hd<best[1]: best=(t,hd)
    print(f"  H^- Hankel-defect: at t=0 (monomial)={mp.nstr(hankel_defect(Hm),3)}  min over shifts={mp.nstr(best[1],3)} at t={mp.nstr(best[0],3)}")
    # rank of the Hankel-breaking part: H^- - (Hankel projection)
    n=d+1; Hk=mp.zeros(n,n)
    for s in range(2*n-1):
        vals=[Hm[i,s-i] for i in range(max(0,s-n+1),min(n-1,s)+1)]; mn=mp.fsum(vals)/len(vals)
        for i in range(max(0,s-n+1),min(n-1,s)+1): Hk[i,s-i]=mn
    D=Hm-Hk; ev=sorted([abs(x) for x in mp.eigsy((D+D.T)/2,eigvals_only=True)],reverse=True)
    eff=sum(1 for x in ev if x>1e-20*ev[0])
    print(f"  H^- minus its Hankel-projection: effective rank={eff}/{n}  (low => H^- ~ Hankel+lowrank; high => irreducibly non-Hankel)")
