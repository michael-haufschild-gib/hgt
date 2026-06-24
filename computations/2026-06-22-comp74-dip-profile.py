"""comp74 [P4] / gpt/43 #6 — rescaled Christoffel dip profile.

comp70: m_d(y)=v(y)^T (H^-)^{-1} v(y)  (inverse-Christoffel of the bulk H^-=H^0-a_* v_* v_*^T)
is NEGATIVE in a thin window bracketing y_*=-0.16 (two real roots y_-<y_*<y_+), width w_d ~ margin -> 0.
Question (gpt/43): rescale Y=(y-y_*)/w_d, normalize the dip; does the profile become UNIVERSAL as d grows?
  universal profile           -> opens an asymptotic kernel proof;
  profile depends on d only via w_d -> rate-generic;
  no convergence              -> no local asymptotic proof.
Also track w_d vs s_d and the margin (comp70 said width ~ margin)."""
import mpmath as mp, sys
sys.path.insert(0,'.')
from hgtlib import T_moments_exact, H0_matrix
A_STAR = mp.mpf('0.16'); Y_STAR = -A_STAR

def vy(y,d): return mp.matrix([[y**i] for i in range(d+1)])

def setup(d):
    mp.mp.dps = int(6.5*d)+140
    T = T_moments_exact(2*d+2)
    H0 = H0_matrix(d,T)
    vs = vy(Y_STAR,d)
    Hm = H0 - A_STAR*(vs*vs.T)            # H^- = H^0 - a_* v_* v_*^T
    Hminv = mp.inverse(Hm)
    m_star = (vs.T*Hminv*vs)[0]           # scalar m_d = m_d(y_*)
    s_d = A_STAR + 1/m_star               # scalar gap
    # m_d(y)=v(y)^T Hminv v(y) = sum_n p_n y^n, p_n = anti-diagonal sums of Hminv
    p=[mp.mpf(0)]*(2*d+1)
    for i in range(d+1):
        for j in range(d+1): p[i+j]+=Hminv[i,j]
    def md(y): return mp.polyval(list(reversed(p)), y)
    def mderiv(y,r):
        from math import comb
        return mp.fsum(p[n]*mp.factorial(n)/mp.factorial(n-r)*y**(n-r) for n in range(r,2*d+1))
    return md, mderiv, s_d, m_star

print("=== dip geometry vs d (curvature-based, no root-finding floor) ===")
print(f"{'d':>4} {'s_d':>14} {'m_d(y_*)':>12} {'y_min-y_*':>14} {'w_d(curv)':>14} {'w_d ratio':>12}")
profiles={}; widths={}; prev_w=None
for d in (8,12,16,20,24,28):
    md, mder, s_d, mstar = setup(d)
    m0=md(Y_STAR); m1=mder(Y_STAR,1); m2=mder(Y_STAR,2)
    y_min = Y_STAR - m1/m2                      # Newton step to the stationary point
    dipmin = md(y_min)
    w_d = 2*mp.sqrt(-2*m0/m2)                   # zero-crossing width of the osculating parabola
    ratio = (prev_w/w_d) if prev_w else mp.mpf('nan'); prev_w=w_d
    print(f"{d:>4} {mp.nstr(s_d,6):>14} {mp.nstr(m0,6):>12} {mp.nstr(y_min-Y_STAR,4):>14} {mp.nstr(w_d,6):>14} {mp.nstr(ratio,5):>12}")
    widths[d]=w_d
    prof=[]
    for j in range(-15,16):
        Y=mp.mpf(j)/10; y=y_min+Y*w_d
        prof.append(float(md(y)/abs(dipmin)))
    profiles[d]=prof

print("\n=== rescaled profile  P(Y)=m_d(y)/|dip_min|, Y=(y-y_min)/w_d  vs parabola 4Y^2-1 ===")
Ys=[mp.mpf(j)/10 for j in range(-15,16)]; ds=sorted(profiles)
print("   Y   "+"".join(f"  d={d:>2}  " for d in ds)+"   4Y^2-1   max|dev|")
maxdev=0.0
for idx,Y in enumerate(Ys):
    if abs(round(float(Y)*2)-float(Y)*2)>1e-9: continue
    vals=[profiles[d][idx] for d in ds]; par=float(4*Y*Y-1)
    dev=max(abs(v-par) for v in vals); maxdev=max(maxdev,dev)
    print(f"{float(Y):6.2f} "+"".join(f"{v:8.4f}" for v in vals)+f"  {par:8.4f}  {dev:.2e}")
print(f"\nmax |profile - (4Y^2-1)| over d and |Y|<=1.5:  {maxdev:.3e}  (universal parabolic dip if ~0)")
print("width scaling w_d(d): "+", ".join(f"d{d}:{mp.nstr(widths[d],4)}" for d in ds))
print("DONE")
