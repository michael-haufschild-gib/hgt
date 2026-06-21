"""
Check that the no-margin exponent is DENSITY-DETERMINED (asymptotically 4, generic), not zeta-specific.
Replace the actual zeros gamma_n by synthetic sets with controlled density, keep M_triv fixed (arch),
and measure the per-step margin exponent log(margin(d)/margin(d-1))/log(1/gamma_d).
  - actual zeta zeros: density ~ log gamma  -> exponent 4 minus a log correction (~3.4, drifting up)
  - linear gamma_n = g1*n: density CONSTANT (no log) -> should give exponent ~4 cleanly
  - sqrt gamma_n = g1*sqrt(n): density ~ gamma (denser) -> different exponent, tracking the density
If the exponent tracks the synthetic density, it is generic (RH not in the rate; only the product's
positivity = reality of the zeros is RH-bearing).
args: mode N DMAX dps     mode in {actual, linear, sqrt, quad}
"""
import sys, mpmath as mp
mode=sys.argv[1] if len(sys.argv)>1 else "actual"
N=int(sys.argv[2]) if len(sys.argv)>2 else 250
DMAX=int(sys.argv[3]) if len(sys.argv)>3 else 16
mp.mp.dps=int(sys.argv[4]) if len(sys.argv)>4 else 200
KMAX=2*DMAX+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gactual=[mp.mpf(f.readline().strip()) for _ in range(N)]
g1=gactual[0]
if mode=="actual": gam=gactual
elif mode=="linear": gam=[g1*n for n in range(1,N+1)]                    # density const
elif mode=="sqrt":   gam=[g1*mp.sqrt(mp.mpf(n)) for n in range(1,N+1)]   # density ~ gamma (denser)
elif mode=="quad":   gam=[g1*mp.mpf(n)**2 for n in range(1,N+1)]         # density ~ 1/gamma^... (sparser)
else: gam=gactual
TN=gam[-1]
def tail(k):  # crude tail; negligible for the exponent (dominated by low zeros)
    pp=2*k-1; return mp.mpf(0)
T={k:2*mp.fsum(g**(-2*k) for g in gam) for k in range(1,KMAX+1)}
def maMM(m): return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
def margin(d):
    H0=mp.matrix(d+1,d+1); MA=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H0[i,j]=T[i+j+1]; MA[i,j]=maMM(i+j)
    L=mp.cholesky(MA); Li=mp.inverse(L); G=Li*H0*Li.T; G=(G+G.T)/2
    return min(mp.eigsy(G,eigvals_only=True))
print(f"# synthetic exponent, mode={mode}, N={N}, DMAX={DMAX}, dps={mp.mp.dps}")
mg=[margin(d) for d in range(1,DMAX+1)]
prev=None
for d in range(2,DMAX+1):
    gd=gam[d-1]
    if prev is not None and mg[d-1]>0 and prev>0:
        e=mp.log(mg[d-1]/prev)/mp.log(1/gd)
        print(f"  d={d:2d} gamma_d={mp.nstr(gd,6):>9s}  margin={mp.nstr(mg[d-1],4):>11s}  per-step exp={mp.nstr(e,5)}")
    prev=mg[d-1]
