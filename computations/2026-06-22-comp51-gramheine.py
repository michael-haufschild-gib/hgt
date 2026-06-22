"""comp51 / rt#51 / gpt38-c7: Gram-Heine ladder at d=3,4. Verify the tuple-sum identity
det[mu_{i+j}]_{0..d} = sum_{n0<...<nd} prod w_{n_k} prod_{i<j}(y_i-y_j)^2 (reusable bulk-cross
domination structure?), and find d* for det H_4 (extend the unconditional ladder)."""
import sys, mpmath as mp, itertools, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
mp.mp.dps=70
# (a) tuple identity at d=3,4 (small N)
for d,N in [(3,14),(4,12)]:
    g=H.load_zeros('zeros400.txt',N); ys=[1/(x*x) for x in g]; w=[2*y for y in ys]
    Hm=mp.matrix([[mp.fsum(w[n]*ys[n]**(i+j) for n in range(N)) for j in range(d+1)] for i in range(d+1)])
    detM=mp.det(Hm); tup=mp.mpf(0)
    for c in itertools.combinations(range(N),d+1):
        pr=mp.fprod(w[k] for k in c)
        vd=mp.fprod((ys[c[i]]-ys[c[j]])**2 for i in range(d+1) for j in range(i+1,d+1))
        tup+=pr*vd
    print(f"(a) d={d}, N={N}: det(moment)={mp.nstr(detM,10)}  tuple-sum={mp.nstr(tup,10)}  rel={mp.nstr(abs(detM-tup)/abs(detM),3)}  (all on-line tuples >0)")
# (b) d* for det H_4: inject quartet, find first d with non-PSD (extend ladder)
mp.mp.dps=160; DMAX=6
Tb=H.T_moments_exact(2*DMAX+1); Bf=H.Mtriv_matrix(DMAX)
LiC={d:mp.inverse(mp.cholesky(mp.matrix([[Bf[i,j] for j in range(d+1)] for i in range(d+1)]))) for d in range(2,DMAX+1)}
def dstar(g0,de):
    Tinj=H.add_quartet_moments(Tb, mp.mpf('0.5')+de, g0)
    for d in range(2,DMAX+1):
        Ad=H.H0_matrix(d,Tinj); C=LiC[d]*Ad*LiC[d].T
        if min(mp.eigsy((C+C.T)/2,eigvals_only=True))<0: return d
    return None
print("(b) det H_4 unconditional? d* for injected quartets (need d*>4):")
for g0 in [16,18,20,25]:
    ds=[dstar(mp.mpf(g0),mp.mpf(de)) for de in ['0.05','0.45']]
    print(f"    gamma0={g0}: d*(.05)={ds[0]} d*(.45)={ds[1]} -> det H_4 {'UNCONDITIONAL' if min(x for x in ds if x)>4 else 'can flip'}")
