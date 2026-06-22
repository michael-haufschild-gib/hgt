"""comp59 / rt#59 / gpt39 c6: Gram-Heine at d=5,6. Verify the tuple-sum identity (does the
manifestly-positive bulk-cross structure persist) and find d* for det H_5,H_6 (extend the
unconditional ladder). Numerical pattern-check; rigorous interval version is a follow-on."""
import sys, mpmath as mp, itertools, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
mp.mp.dps=70
# (a) tuple identity at d=5,6 (small N)
for d,N in [(5,13),(6,13)]:
    g=H.load_zeros('zeros400.txt',N); ys=[1/(x*x) for x in g]; w=[2*y for y in ys]
    Hm=mp.matrix([[mp.fsum(w[n]*ys[n]**(i+j) for n in range(N)) for j in range(d+1)] for i in range(d+1)])
    detM=mp.det(Hm); tup=mp.mpf(0)
    for c in itertools.combinations(range(N),d+1):
        pr=mp.fprod(w[k] for k in c)
        vd=mp.fprod((ys[c[i]]-ys[c[j]])**2 for i in range(d+1) for j in range(i+1,d+1))
        tup+=pr*vd
    print(f"(a) d={d}, N={N}: det={mp.nstr(detM,10)} tuple-sum={mp.nstr(tup,10)} rel={mp.nstr(abs(detM-tup)/abs(detM),3)} (all on-line tuples >0)")
# (b) d* for det H_5,H_6 (extend ladder); need d*>5,6 resp for unconditional
mp.mp.dps=200; DMAX=8
Tb=H.T_moments_exact(2*DMAX+1); Bf=H.Mtriv_matrix(DMAX)
LiC={d:mp.inverse(mp.cholesky(mp.matrix([[Bf[i,j] for j in range(d+1)] for i in range(d+1)]))) for d in range(2,DMAX+1)}
def dstar(g0,de):
    Tinj=H.add_quartet_moments(Tb, mp.mpf('0.5')+de, g0)
    for d in range(2,DMAX+1):
        Ad=H.H0_matrix(d,Tinj); C=LiC[d]*Ad*LiC[d].T
        if min(mp.eigsy((C+C.T)/2,eigvals_only=True))<0: return d
    return None
print("(b) d* for injected quartets (det H_d unconditional iff d*>d):")
for g0 in [16,18,20,25,30]:
    ds=[dstar(mp.mpf(g0),mp.mpf(de)) for de in ['0.05','0.45']]
    dmin=min([x for x in ds if x] or [99])
    print(f"    gamma0={g0}: d*(.05)={ds[0]} d*(.45)={ds[1]} -> det H_5 {'OK' if dmin>5 else 'flips'}, H_6 {'OK' if dmin>6 else 'flips'}")
