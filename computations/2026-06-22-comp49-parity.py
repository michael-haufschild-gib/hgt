"""comp49 / rt#49 / gpt38-c5: parity/protector exponent FORMULA. ZETA zeros fixed (exact
moments); synthetic protector P_b with trivial chain atoms (2l+b+1/2), l>=0, weights
(2l+b+1/2)^{-2} (P_m(b)=4^{-m} zeta(2m,(b+1/2)/2)). Coarsest point y_*(b)=-(b+1/2)^{-2}.
b=0 == even-chi protector, b=1 == odd-chi, b=2 == zeta's own (j>=1). Sweep b; measure
margin exponent alpha(b); test alpha vs ln|y_*|. comp8 anchors: (y_*=-4,alpha~5.05),
(-0.444,3.90),(-0.16,3.41)."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py")
gammas=H.load_zeros('zeros400.txt', 60)
def Pb_matrix(d,b):
    P=[None]+[mp.power(4,-m)*mp.zeta(2*m,(mp.mpf(b)+mp.mpf('0.5'))/2) for m in range(1,2*d+2)]
    return mp.matrix([[(1 if (i+j)%2==0 else -1)*P[i+j+1] for j in range(d+1)] for i in range(d+1)])
DMAX=20; mp.mp.dps=int(6.5*DMAX)+120
T=H.T_moments_exact(2*DMAX+1); A=H.H0_matrix(DMAX,T)
sub=lambda M,d: mp.matrix([[M[i,j] for j in range(d+1)] for i in range(d+1)])
print(f"# b   y_*=-(b+.5)^-2   ln|y_*|   alpha(mean e_d, d=6..20)   [comp8 anchor]")
for b in [mp.mpf(x) for x in ['0','0.5','1','1.5','2','2.5','3','4']]:
    ystar=-mp.power(b+mp.mpf('0.5'),-2)
    B=Pb_matrix(DMAX,b)
    prev=None; es=[]
    for d in range(2,DMAX+1):
        Ad,Bd=sub(A,d),sub(B,d)
        Li=mp.inverse(mp.cholesky(Bd)); C=Li*Ad*Li.T; m=min(mp.eigsy((C+C.T)/2,eigvals_only=True))
        if prev and m>0 and d>=6: es.append(float(-mp.log(m/prev)/mp.log(gammas[d-1])))
        prev=m if m>0 else None
    alpha=sum(es)/len(es) if es else float('nan')
    anchor={'0':'even-chi 5.05','1':'odd-chi 3.90','2':'zeta 3.41'}.get(mp.nstr(b,2),'')
    print(f"  {mp.nstr(b,3):4s} {mp.nstr(ystar,6):12s}  {float(mp.log(abs(ystar))):7.3f}   {alpha:6.3f}   {anchor}",flush=True)
