"""Repair of gamma-module-construction claim (3): Gamma is the INVERSE zeta-reg determinant.
det_zeta(N+a) = exp(-zeta_H'(0,a)) = sqrt(2pi)/Gamma(a)  (Lerch). So Gamma(a)*det = sqrt(2pi).
Euler-factor = inverse determinant, uniform with finite primes (1-p^{-s}Fr)^{-1}."""
import mpmath as mp
mp.mp.dps = 40
print("a            det-reciprocal      Gamma*det - sqrt(2pi)")
for a in [mp.mpf('0.5'), mp.mpf('1'), mp.mpf('1.5'), mp.mpf('2'), mp.mpf('0.25')+mp.mpf('7')*1j]:
    zp  = mp.zeta(0, a, 1)                 # d/ds zeta_Hurwitz(s,a) at s=0
    det = mp.e**(-zp)                       # zeta-reg determinant of spectrum {a+k}
    rec = mp.sqrt(2*mp.pi)/mp.gamma(a)      # claimed reciprocal
    prod = mp.gamma(a)*det
    print(f"{str(a):>14}  {float(abs(det-rec)):.2e}        {float(abs(prod-mp.sqrt(2*mp.pi))):.2e}")
print("=> Gamma(a) = sqrt(2pi) * det_zeta(N+a)^{-1}. Confirmed.")
