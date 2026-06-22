"""comp13 / rt#41: hard-edge fake-divisor battery. With ZETA's M_triv protector FIXED,
and ALL moments computed the SAME truncated way (fair), compare margin exponent + dangerous-
direction overlap_u for: zeta-actual, jittered-zeta (density kept, correlations destroyed),
Poisson same-density, rigid picket-fence, FID (gamma_n=n), n^2 (sparse). Tests whether the
K_d margin law carries ANY zeta/prime-specific content or is generic to the hard-edge class."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
mp.mp.dps=200
N=300; DMAX=16
zeta=H.load_zeros('zeros400.txt', N)
# deterministic pseudo-random from a fixed integer stream (no Date/rand; reproducible)
def lcg(seed):
    x=seed
    while True:
        x=(1103515245*x+12345)% (2**31); yield mp.mpf(x)/(2**31)
def build(name):
    if name=='zeta': g=zeta
    elif name=='rigid':  # picket fence at zeta's mean local spacing
        g=[zeta[0]]; 
        for n in range(1,N): g.append(g[-1]+(zeta[-1]-zeta[0])/(N-1))
    elif name=='jitter': # zeta positions + uniform jitter of +-0.5 local spacing
        r=lcg(7); g=[]
        for n in range(N):
            sp=(zeta[min(n+1,N-1)]-zeta[max(n-1,0)])/2
            g.append(zeta[n]+(next(r)-mp.mpf('0.5'))*sp)
        g=sorted(abs(x) for x in g)
    elif name=='poisson': # same mean density, exponential gaps
        r=lcg(13); mean=(zeta[-1]-zeta[0])/(N-1); g=[zeta[0]]
        for n in range(1,N): g.append(g[-1]-mean*mp.log(next(r)+mp.mpf('1e-9')))
    elif name=='FID':  g=[mp.mpf(n) for n in range(1,N+1)]      # gamma_n=n
    elif name=='nsq':  g=[mp.sqrt(mp.mpf(n)) for n in range(1,N+1)]  # y_n=1/n (n^2 in gamma^2)
    ys=[1/(x*x) for x in g]
    return ys
B=H.Mtriv_matrix(DMAX)
Lc=mp.cholesky(B); Li=mp.inverse(Lc)
def run(name):
    ys=build(name); T=H.T_moments(ys,2*DMAX+1)
    prev=None; es=[]
    for d in range(2,DMAX+1):
        A=H.H0_matrix(d,T); Ld=mp.matrix([[Li[i,j] for j in range(d+1)] for i in range(d+1)])
        # use leading submatrix of Li? Li is for DMAX; need Li for d. Recompute small:
        Bd=mp.matrix([[B[i,j] for j in range(d+1)] for i in range(d+1)]); Lid=mp.inverse(mp.cholesky(Bd))
        C=Lid*A*Lid.T; C=(C+C.T)/2
        if d in (8,16):
            E,Q=mp.eigsy(C); idx=min(range(len(E)),key=lambda i:E[i]); m=E[idx]
            q=mp.matrix([Q[r,idx] for r in range(d+1)]); c=Lid.T*q; ov=H.overlap_with_pole(c)
        else:
            m=min(mp.eigsy(C,eigvals_only=True)); ov=None
        if prev and m>0: es.append(float(-mp.log(m/prev)/mp.log(d)))  # exponent vs degree index
        if d==16: ov16=ov; m16=m
        prev=m if m>0 else None
    import statistics
    emean=sum(es)/len(es) if es else float('nan')
    print(f"  {name:8s}: exponent(per-degree, mean)~{emean:5.2f}  log10(margin@16)={float(mp.log10(abs(m16))):.1f}{' (NOT PSD)' if m16<0 else ''}  overlap_u@16={mp.nstr(ov16,5)}",flush=True)
print(f"# comp13: zeta M_triv FIXED, N={N} atoms (identical truncation), exponent normalized by degree index")
for nm in ['zeta','jitter','poisson','rigid','FID','nsq']:
    run(nm)
