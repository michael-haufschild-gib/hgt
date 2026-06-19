"""
M_infty (the Source-A Gamma-module) — numeric pre-certification (card: gamma-module-construction).
Gamma_R(s) = pi^{-s/2} Gamma(s/2).  dps=30.
(1) recurrence:  Gamma_R(s+2)/Gamma_R(s) = s/(2 pi)              [multiplier a(s)=s/2pi]
(2) connection:  d_s log Gamma_R = -1/2 log pi + 1/2 psi(s/2)    [rank-1 d_s-connection]
(3) Lerch zeta-reg determinant:  d/dz HurwitzZeta(z,a)|_{z=0} = log Gamma(a) - 1/2 log(2pi)
    => zeta-reg prod_{k>=0}(a+k) = sqrt(2pi)/Gamma(a); with a=s/2 this realizes Gamma_R as a
    zeta-regularized determinant of the shift generator on M_infty.
"""
import mpmath as mp
mp.mp.dps = 30
def GR(s): return mp.power(mp.pi, -s/2) * mp.gamma(s/2)

print("=== M_infty pre-cert (dps=30) ===")
for s in [mp.mpf('3'), mp.mpc('0.5','14'), mp.mpc('2','5'), mp.mpf('1'), mp.mpc('0.25','3')]:
    rec = GR(s+2)/GR(s); rec_pred = s/(2*mp.pi)
    dlog = mp.diff(lambda z: mp.log(GR(z)), s); dlog_pred = -mp.log(mp.pi)/2 + mp.digamma(s/2)/2
    print(f"s={complex(s):>12.4g} | rec-err={mp.nstr(abs(rec-rec_pred),3)} | conn-err={mp.nstr(abs(dlog-dlog_pred),3)}")
print("# Lerch:")
for a in [mp.mpf('0.5'), mp.mpf('1.5'), mp.mpc('0.7','2'), mp.mpf('2.0')]:
    lhs = mp.diff(lambda z: mp.zeta(z,a), 0); rhs = mp.log(mp.gamma(a)) - mp.log(2*mp.pi)/2
    regprod = mp.e**(-lhs); pred = mp.sqrt(2*mp.pi)/mp.gamma(a)
    print(f"a={complex(a):>10.4g} | Lerch-err={mp.nstr(abs(lhs-rhs),3)} | regprod-err={mp.nstr(abs(regprod-pred),3)}")
