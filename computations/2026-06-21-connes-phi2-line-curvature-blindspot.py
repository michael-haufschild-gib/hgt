"""
Is the line-local curvature condition Φ_2(t)<0 ∀t a faithful RH certificate?

Φ_2(t) = Σ_ρ (½+it−ρ)^{-2}  (Re part along the critical line = ∂²_σ log|ξ| = −∂²_t log|ξ|, by harmonicity).
PH3: RH ⟹ Φ_2<0 (log|ξ| concave along the line). Question: does the converse hold — does an off-line
zero always force Φ_2>0 somewhere (so Φ_2<0 ∀t ⟺ RH)?

An off-line FE quartet {β±iγ0, 1−β±iγ0} (a=|½−β|) contributes a POSITIVE curvature bump C_a, peak
C_a(0)=2/a², while on-line zeros contribute negative spikes. So near-line zeros (small a, huge spike) are
always detected. But the bump is bounded (2/a²≥8 for a≤½) while the on-line background |Φ_2| grows like
(log γ)²/π² with height — so a FAR-off-line zero may be swamped. This script tests detection vs height.

Result: a=0.45 quartet is undetected (Φ_2 stays <0) at heights 180, 260, 261 — so Φ_2<0 ∀t is
NECESSARY but NOT SUFFICIENT (RH-blind to far-off-line zeros), unlike the reciprocal-Hankel Q_0 which is
faithful at all heights (obstruction Im y, fixed sign).
"""
import mpmath as mp
mp.mp.dps=20
N=900
gam=[mp.zetazero(n).imag for n in range(1,N+1)]
def Phi2_online(t):
    s=mp.mpf(0)
    for g in gam:
        s+=1/(mp.mpc(0,(t-g)))**2 + 1/(mp.mpc(0,(t+g)))**2
    return mp.re(s)
def quartet_term(t,beta,g0):
    out=mp.mpf(0)
    for (b,gg) in [(beta,g0),(beta,-g0),(1-beta,g0),(1-beta,-g0)]:
        out+= 1/(mp.mpf('0.5')+mp.mpc(0,t)-mp.mpc(b,gg))**2
    return mp.re(out)
def maxnear(beta,g0):
    best=mp.mpf('-1e30'); t=g0-mp.mpf('1.5')
    while t<=g0+mp.mpf('1.5'):
        v=Phi2_online(t)+quartet_term(t,beta,g0)
        if v>best: best=v
        t+=mp.mpf('0.03')
    return best
if __name__=="__main__":
    a=mp.mpf('0.45'); beta=mp.mpf('0.5')+a
    print(f"# far-off-line a={float(a)} quartet; 2/a^2={float(2/a**2):.2f}; >0 = detected")
    for g0c in [60,120,180,240,260,261,262,263,264,265]:
        m=maxnear(beta,mp.mpf(g0c))
        print(f"   g0={g0c:5}  maxPhi2={mp.nstr(m,5):>11}   {'detected' if m>0 else 'NOT detected'}")
