#!/usr/bin/env python3
# Verification for: completed-base-archimedean-coordinate.md (the ring R+ = R[g; sigma_inf], d_s).
# g <-> Gamma_R(s)=pi^{-s/2}Gamma(s/2). Checks: Gamma-recurrence, connection, digamma recurrence
# (the [d_s, sigma_inf]=0 consistency), and sigma_inf = prod sigma_p^2 on monomials.
# Local, sub-second, no runpod.
import mpmath as mp
mp.mp.dps = 30

GR = lambda s: mp.pi**(-s/2) * mp.gamma(s/2)   # Gamma_R(s)

print("(1) Gamma_R(s+2) = (s/2pi) Gamma_R(s)   [sigma_inf g = (s/2pi) g]")
for s in [mp.mpf('1.3'), mp.mpf('2.7'), mp.mpf('0.4')]:
    print("    s=%s |diff|=%.1e" % (mp.nstr(s,3), float(abs(GR(s+2) - (s/(2*mp.pi))*GR(s)))))

print("(2) d/ds log Gamma_R(s) = -1/2 log pi + 1/2 psi(s/2)   [connection d_s g = g(...)]")
for s in [mp.mpf('1.3'), mp.mpf('2.7')]:
    lhs = mp.diff(lambda x: mp.log(GR(x)), s)
    rhs = -mp.log(mp.pi)/2 + mp.digamma(s/2)/2
    print("    s=%s |diff|=%.1e" % (mp.nstr(s,3), float(abs(lhs - rhs))))

print("(3) psi(s/2+1) = psi(s/2) + 2/s   [the [d_s, sigma_inf]g = 0 consistency]")
for s in [mp.mpf('1.3'), mp.mpf('2.7')]:
    print("    s=%s |diff|=%.1e" % (mp.nstr(s,3), float(abs(mp.digamma(s/2+1) - (mp.digamma(s/2) + 2/s)))))

print("(4) sigma_inf e_m = n_m^{-2} e_m = (prod_p sigma_p^2) e_m   [product formula in operator form]")
# e_m = n_m^{-s}; sigma_inf: s->s+2 gives n_m^{-(s+2)} = n_m^{-2} e_m. prod sigma_p^2 gives prod p^{-2 m_p} = n_m^{-2}.
for m in [{2:1, 3:2}, {5:1, 7:1, 2:3}]:
    n_m = 1
    for p, e in m.items():
        n_m *= p**e
    # eigenvalue from sigma_inf (s->s+2 on n_m^{-s}) :
    eig_sigma_inf = mp.mpf(n_m)**(-2)
    # eigenvalue from prod sigma_p^2 :
    eig_prod = 1
    for p, e in m.items():
        eig_prod *= mp.mpf(p)**(-2*e)
    print("    m=%s  n_m=%d  sigma_inf eig=%s  prod sigma_p^2 eig=%s  |diff|=%.1e"
          % (m, n_m, mp.nstr(eig_sigma_inf,12), mp.nstr(eig_prod,12), float(abs(eig_sigma_inf - eig_prod))))
