"""comp16+comp12+comp15 combined (shared H^0/M_triv machinery)."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")

print("=== comp16 / rt#44 : is the 'boundary' R^P=H^0-M_triv low-rank? (eigenvalue decay) ===")
for d in [10,14]:
    mp.mp.dps=int(6.5*d)+90
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d); RP=A-B
    E=sorted(mp.eigsy((RP+RP.T)/2,eigvals_only=True), key=lambda e:-abs(e))
    mags=[float(mp.log10(abs(e))) for e in E]
    # rank-r truncation residual energy fraction
    tot=mp.fsum(e**2 for e in E)
    resid=lambda r: float(mp.sqrt(mp.fsum(E[i]**2 for i in range(r,len(E)))/tot))
    print(f" d={d}: |eig| log10 spectrum (desc): {[round(m,2) for m in mags]}")
    print(f"       rank-1 residual={resid(1):.3f} rank-2={resid(2):.3f} rank-3={resid(3):.3f}  => {'LOW-RANK boundary' if resid(3)<0.05 else 'NOT low-rank (full boundary)'}")

print("=== comp15 / rt#43 : Christoffel identity 1/margin = 0.16 * e(-0.16)^T (H^0)^{-1} e(-0.16) ===")
for d in [10,15,20]:
    mp.mp.dps=int(6.5*d)+110
    T=H.T_moments_exact(2*d+1); A=H.H0_matrix(d,T); B=H.Mtriv_matrix(d)
    Lc=mp.cholesky(B); Li=mp.inverse(Lc); C=Li*A*Li.T; C=(C+C.T)/2
    margin=min(mp.eigsy(C,eigvals_only=True))
    e=mp.matrix([mp.power(mp.mpf('-0.16'),i) for i in range(d+1)])
    Kchr=(e.T*mp.inverse(A)*e)[0]    # K_nu'(-0.16,-0.16)=e^T (H^0)^{-1} e
    lhs=1/margin; rhs=mp.power(mp.mpf('2.5'),-2)*Kchr
    rel=abs(lhs-rhs)/abs(lhs)
    print(f" d={d}: 1/margin={mp.nstr(lhs,6)}  0.16*K_chr={mp.nstr(rhs,6)}  rel={mp.nstr(rel,3)}  log10 K_chr={float(mp.log10(Kchr)):.2f}")

print("=== comp12 / rt#40 : Gram-Heine tuple identity + d=2,3 unconditional positivity ===")
# (a) tuple identity at d=2 with N=15 atoms: det[mu_{i+j}] = sum_{n0<n1<n2} prod(w) prod(y_i-y_j)^2
mp.mp.dps=60
g=H.load_zeros('zeros400.txt',15); ys=[1/(x*x) for x in g]; w=[2*y for y in ys]
def mom(k): return mp.fsum(w[n]*ys[n]**k for n in range(len(ys)))
Hm=mp.matrix([[mom(i+j) for j in range(3)] for i in range(3)]); detM=mp.det(Hm)
import itertools
tup=mp.mpf(0)
for c in itertools.combinations(range(len(ys)),3):
    pr=w[c[0]]*w[c[1]]*w[c[2]]
    vd=(ys[c[0]]-ys[c[1]])**2*(ys[c[0]]-ys[c[2]])**2*(ys[c[1]]-ys[c[2]])**2
    tup+=pr*vd
print(f" (a) d=2, N=15: det(moment)={mp.nstr(detM,12)}  tuple-sum={mp.nstr(tup,12)}  rel={mp.nstr(abs(detM-tup)/abs(detM),3)}")
# (b) d* at low gamma0 to establish d=2,3 unconditional (need d*>3 for all off-line zeros)
mp.mp.dps=160; DMAX=8
Tb=H.T_moments_exact(2*DMAX+1); Bf=H.Mtriv_matrix(DMAX)
LiC={d:mp.inverse(mp.cholesky(mp.matrix([[Bf[i,j] for j in range(d+1)] for i in range(d+1)]))) for d in range(2,DMAX+1)}
def dstar(g0,de):
    Tinj=H.add_quartet_moments(Tb, mp.mpf('0.5')+de, g0)
    for d in range(2,DMAX+1):
        Ad=H.H0_matrix(d,Tinj); C=LiC[d]*Ad*LiC[d].T; C=(C+C.T)/2
        if min(mp.eigsy(C,eigvals_only=True))<0: return d
    return None
print(" (b) lowest d* over delta in {0.05,0.45} at low gamma0 (d*>3 => det H_2,H_3 unconditional):")
for g0 in [14,16,18,20]:
    ds=[dstar(mp.mpf(g0),mp.mpf(de)) for de in ['0.05','0.45']]
    print(f"     gamma0={g0}: d*(delta=.05)={ds[0]}  d*(delta=.45)={ds[1]}  -> det H_2,H_3 {'UNCONDITIONAL' if min(x for x in ds if x)>3 else 'can flip'}")
