"""
gpt/27 Comp 6 — most dangerous polynomial: where does the Q_0 near-degeneracy localize?

The eigenvector of H_d^(0)=[T_{i+j+1}] at lambda_min is the real polynomial p_d(y)=Sum v_i y^i that
nearly violates Q_0[p]>=0 (Q_0[p_d]=lambda_min, the smallest positive value). Question (undecidable):
do its roots / its contribution mass sit near the dominant atom y_1=1/gamma_1^2, near the hard edge
y->0 (high zeros), or broad? That names the regime the analytic proof must control.

Q_0[p] = 2 Sum_n y_n p(y_n)^2,  y_n=1/gamma_n^2.  Report: roots of p_d, and the cumulative share of
|2 y_n p_d(y_n)^2| by atom index (which atoms carry the dangerous mass).

Chunk args: N DMAX dps.
"""
import sys, mpmath as mp
N    = int(sys.argv[1]) if len(sys.argv) > 1 else 120
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6
mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 90
KMAX = 2*DMAX + 1

gam = [mp.zetazero(n).imag for n in range(1, N+1)]
y = [1/g**2 for g in gam]
TN = gam[-1]
def tail(k):
    p = 2*k-1; return (1/mp.pi)*TN**(-p)/p*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/p)
T = {k: 2*mp.fsum(g**(-2*k) for g in gam) + tail(k) for k in range(1, KMAX+1)}

H = mp.matrix(DMAX+1, DMAX+1)
for i in range(DMAX+1):
    for j in range(DMAX+1): H[i,j] = T[i+j+1]
E, V = mp.eigsy(H)                                  # ascending eigenvalues
lmin = E[0]
v = [V[i,0] for i in range(DMAX+1)]                 # eigenvector of lambda_min = coeffs of p_d
def pd(yy): return mp.fsum(v[i]*yy**i for i in range(DMAX+1))

print(f"# most dangerous polynomial p_d, d={DMAX}, N={N}, dps={mp.mp.dps}")
print(f"# lambda_min(H_d^(0)) = {mp.nstr(lmin,6)};  y_1={float(y[0]):.4e}  y_hardedge≈{float(y[-1]):.2e}")
print(f"# p_d coeffs: {[mp.nstr(c,4) for c in v]}")
# roots of p_d
roots = mp.polyroots([v[DMAX-i] for i in range(DMAX+1)], maxsteps=200, extraprec=200)
realroots = sorted(float(mp.re(r)) for r in roots if abs(mp.im(r)) < 1e-20)
print(f"# real roots of p_d: {[f'{r:.4e}' for r in realroots]}  (compare atoms y_1..y_5 = {[f'{float(y[i]):.3e}' for i in range(5)]})")
# contribution share by atom
contrib = [2*y[n]*pd(y[n])**2 for n in range(N)]
tot = mp.fsum(contrib)
cum = mp.mpf(0); print(f"# cumulative share of Q_0[p_d] by atom (tot={mp.nstr(tot,5)}):")
for n in range(N):
    cum += contrib[n]
    if n < 8 or n in (9,14,19,29,49,N-1):
        print(f"    atom n={n+1:>3} (y={float(y[n]):.3e}): contrib={mp.nstr(contrib[n],4):>12}  cum_share={mp.nstr(cum/tot,5)}")
