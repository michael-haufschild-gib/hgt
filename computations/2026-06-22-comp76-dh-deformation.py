"""comp76 [P6] / gpt/43 #6 — DH deformation family around the scalar crossing.

Interpolate genuine zeta (lambda=0) -> DH-like (lambda>0) by adding lambda * (one off-line FE
quartet) to the reciprocal moments, KEEPING the same Gamma boundary (y_*=-0.16, a_*=0.16):
  T(lambda) = T_zeta + lambda * quartet(beta,g0),   quartet off-line (beta>1/2).
Track the scalar gap s_d(lambda)=a_*+1/m_d and locate the crossing s_d=0.  Questions (gpt/43):
  what parameter controls s_d=0?  does lambda_crit(d) shrink with d (height-limited detection)?
  is the crossing monotone/smooth?  (E-tail invariance already established by comp69.)"""
import mpmath as mp, sys
sys.path.insert(0,'.')
from hgtlib import T_moments_exact, add_quartet_moments, H0_matrix
A_STAR=mp.mpf('0.16'); Y_STAR=-A_STAR
def vy(y,d): return mp.matrix([[y**i] for i in range(d+1)])

def s_d_of(T,d):
    H0=H0_matrix(d,T); vs=vy(Y_STAR,d)
    Hm=H0-A_STAR*(vs*vs.T)
    m=(vs.T*mp.inverse(Hm)*vs)[0]
    return A_STAR+1/m

def lambda_crit(d, beta, g0, Tz):
    "bisection in lambda for s_d(lambda)=0; returns (lambda_crit, slope sign) or None."
    def s(lam): return s_d_of(add_quartet_moments(Tz,beta,g0,weight=lam), d)
    s0=s(mp.mpf(0))
    # scan upward for a sign change
    lo,hi=mp.mpf(0), mp.mpf('0.25'); slo=s0
    found=None
    for _ in range(40):
        shi=s(hi)
        if mp.sign(shi)!=mp.sign(slo): found=(lo,hi); break
        lo,slo=hi,shi; hi*=mp.mpf('1.5')
        if hi>mp.mpf('1e6'): break
    if not found: return None, s0
    a,b=found
    for _ in range(80):
        m=(a+b)/2
        if mp.sign(s(m))==mp.sign(s0): a=m
        else: b=m
    return (a+b)/2, s0

print("=== s_d(lambda) for ZETA + lambda*quartet(beta=0.7,g0=20), d=10 (shape of the crossing) ===")
mp.mp.dps=int(6.5*10)+150
Tz=T_moments_exact(2*10+2)
for lam in ('0','0.5','1','2','3','5','8'):
    sd=s_d_of(add_quartet_moments(Tz,'0.7',20,weight=mp.mpf(lam)),10)
    print(f"  lambda={lam:>4}:  s_d = {mp.nstr(sd,8)}")

print("\n=== lambda_crit(d): off-line weight needed to flip s_d, vs degree (beta=0.7,g0=20) ===")
print(f"{'d':>4} {'s_d(lambda=0)':>16} {'lambda_crit':>16}")
prev=None
for d in (8,12,16,20,24,28):
    mp.mp.dps=int(6.5*d)+150
    Tz=T_moments_exact(2*d+2)
    lc, s0 = lambda_crit(d,'0.7',20,Tz)
    rat = (prev/lc) if (prev and lc) else None; prev=lc
    extra = f"  (ratio prev/this={mp.nstr(rat,4)})" if rat else ""
    print(f"{d:>4} {mp.nstr(s0,6):>16} {(mp.nstr(lc,6) if lc else 'no crossing'):>16}{extra}")

print("\n=== dependence on off-line height g0 (does a deeper/shallower off-line zero matter?) d=16 ===")
mp.mp.dps=int(6.5*16)+150
Tz=T_moments_exact(2*16+2)
for g0 in (10,20,40,80):
    lc,s0=lambda_crit(16,'0.7',g0,Tz)
    print(f"  g0={g0:>3}: lambda_crit = {mp.nstr(lc,6) if lc else 'no crossing'}")
print("\n=== dependence on off-line distance beta (closer to line = weaker effect?) d=16,g0=20 ===")
for beta in ('0.55','0.7','1.0','1.5'):
    lc,s0=lambda_crit(16,beta,20,Tz)
    print(f"  beta={beta:>4}: lambda_crit = {mp.nstr(lc,6) if lc else 'no crossing'}")
print("\nDONE")
