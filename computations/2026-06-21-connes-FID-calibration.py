"""
gpt/27 FID positive-control calibration — is the Q_0 ill-conditioning / distributed-obstruction
RH-SPECIFIC, or generic to any reciprocal-squared measure accumulating at 0?

FID integer divisor: nu = sum_n n^{-3} delta_{1/n^2}; shifted Hankel H_FID[i,j]=zeta(2(i+j)+3).
This is strictly totally positive (Cauchy-Binet), RH-EMPTY. Its atoms y_n=1/n^2 also accumulate at 0
(ratios (n/(n+1))^2 -> 1), like the zero divisor's y_n=1/gamma_n^2. So if FID shows the SAME
conditioning and the SAME mid-range / auto-deflating dangerous polynomial, the numerical difficulty is
generic (not RH-specific), and the RH content is only the integer->zero explicit-formula transfer.

Compare to the zero divisor (Q_0). No zeros / high precision needed for FID (moments are zeta(2k+1)).
Chunk args: DMAX dps.
"""
import sys, mpmath as mp
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 90

# FID shifted Hankel: m_l = zeta(2 l + 3) for the Q_0-analog (one power of y weighting: 2(i+j)+3)
def Hfid(d):
    H = mp.matrix(d+1, d+1)
    for i in range(d+1):
        for j in range(d+1): H[i,j] = mp.zeta(2*(i+j)+3)
    return H

print(f"# FID positive control H_FID[i,j]=zeta(2(i+j)+3), dps={mp.mp.dps}")
print(f"# {'d':>3} {'lambda_min':>14} {'lambda_max':>12} {'cond':>12} {'nneg':>5}")
for d in [2,4,6,DMAX]:
    H = Hfid(d); ev = mp.eigsy(H, eigvals_only=True)
    nneg = sum(1 for e in ev if e < 0)
    print(f"  {d:>3} {mp.nstr(ev[0],6):>14} {mp.nstr(ev[-1],5):>12} {mp.nstr(ev[-1]/ev[0],5):>12} {nneg:>5}")

# dangerous polynomial for FID: where does it localize among atoms y_n=1/n^2?
d = DMAX
H = Hfid(d); E, V = mp.eigsy(H)
v = [V[i,0] for i in range(d+1)]
def pd(yy): return mp.fsum(v[i]*yy**i for i in range(d+1))
print(f"\n# FID dangerous polynomial (d={d}, lambda_min={mp.nstr(E[0],5)}):")
roots = mp.polyroots([v[d-i] for i in range(d+1)], maxsteps=200, extraprec=200)
rr = sorted(float(mp.re(r)) for r in roots if abs(mp.im(r))<1e-15)
print(f"#   real roots: {[f'{r:.4e}' for r in rr]}  (FID atoms 1/n^2 = 1, 0.25, 0.111, 0.0625, 0.04)")
contrib = [mp.zeta(3)*0+ (1/mp.mpf(n)**3)*(1/mp.mpf(n)**2)*pd(1/mp.mpf(n)**2)**2 for n in range(1,200)]
tot = mp.fsum(contrib); cum = mp.mpf(0)
print(f"#   contribution share by atom n (tot={mp.nstr(tot,5)}):")
for n in range(1,200):
    cum += contrib[n-1]
    if n<=6 or n in (8,12,20,50,100,199):
        print(f"     n={n:>3} (y=1/n^2={float(1/mp.mpf(n)**2):.3e}): cum_share={mp.nstr(cum/tot,5)}")
