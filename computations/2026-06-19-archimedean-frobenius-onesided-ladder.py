# Past-the-wall conjecture test (DeWitt 2026-06-19):
# Is the archimedean Euler factor the INVERSE zeta-regularized determinant of the
# one-sided number-operator ladder N+a (spectrum {a, a+1, a+2, ...})?
# Claim:  det_zeta(N+a) = exp(-zeta'(0,a)) = sqrt(2*pi) / Gamma(a),  i.e.  Gamma(a)*det_zeta(N+a) = sqrt(2*pi).
# (zeta'(0,a) = log Gamma(a) - (1/2) log 2pi  -- Lerch.)  This grounds "the archimedean Frobenius lives on the
# one-sided ladder", with a_inf = (1/2)log 2pi = log det_zeta(N) the a->1 case.
import mpmath as mp
mp.mp.dps = 40
sqrt2pi = mp.sqrt(2*mp.pi)
print("target sqrt(2pi) =", mp.nstr(sqrt2pi, 25))
print()
print(" a       det_zeta(N+a)=exp(-zeta'(0,a))     Gamma(a)*det_zeta(N+a)      err")
for a in [mp.mpf(1)/2, mp.mpf(1), mp.mpf(3)/2, mp.mpf(2), mp.mpf(5)/2]:
    zp0   = mp.diff(lambda s: mp.zeta(s, a), 0)      # zeta'(0,a), derivative in s of Hurwitz zeta
    detz  = mp.e**(-zp0)
    prod  = mp.gamma(a)*detz
    print(" %-6s  %-32s  %-26s %s" % (mp.nstr(a,4), mp.nstr(detz,20), mp.nstr(prod,20), mp.nstr(abs(prod-sqrt2pi),4)))
print()
# cross-check the Lerch closed form zeta'(0,a) = logGamma(a) - (1/2)log2pi directly
print("Lerch check  zeta'(0,a) vs logGamma(a)-(1/2)log2pi:")
for a in [mp.mpf(1)/2, mp.mpf(1), mp.mpf(2)]:
    lhs = mp.diff(lambda s: mp.zeta(s,a), 0)
    rhs = mp.log(mp.gamma(a)) - mp.log(2*mp.pi)/2
    print("  a=%-4s  diff=%s" % (mp.nstr(a,4), mp.nstr(abs(lhs-rhs),4)))
print()
print("=> archimedean factor Gamma(a) = sqrt(2pi)/det_zeta(N+a): the LOCAL archimedean Euler factor is the")
print("   inverse zeta-reg determinant of the one-sided ladder N+a. a_inf=(1/2)log2pi = log det_zeta(N) (a=1).")
