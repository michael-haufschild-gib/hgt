#!/usr/bin/env python3
"""
Doc 46 SS4 (1): the reach statistic at the 8 survivors (task #130, (HOLD-lemma)
empirical anchor).

reach(rho) := |P_N(rho)| / |Phi'(rho)|,  P_N = gamma(s)N^-s + gamma(1-s)N^{s-1}
(the marginal RS-pair term). "Term-held" quantitatively: the term can move the
zero across its own depth: reach >= eta.

PRE-REGISTERED: P-T1 (prior 0.70): reach >= eta/2 for ALL 8 survivors.
Also recorded: reach/eta and the background share |P_N(rho)|/|Phi_{N-1}(rho)|
(must be exactly 1 by Phi_N(rho) = 0 -- transcription check).
"""
from mpmath import mp, mpc, mpf, pi, re, im, fabs, diff, gamma as Gamma
from euler_suppression_boxcount import make_phi, coeffs
mp.dps = 40
NC = 50
SURV = [(mpf('0.67106'), mpf('1415.6767'), 14),
        (mpf('0.61541'), mpf('4253.5428'), 26),
        (mpf('0.67795'), mpf('4589.7089'), 27),
        (mpf('0.64232'), mpf('4990.3903'), 28),
        (mpf('0.61566'), mpf('6430.8007'), 31),
        (mpf('0.59619'), mpf('7712.8523'), 35),
        (mpf('0.59711'), mpf('7734.7144'), 35),
        (mpf('0.62190'), mpf('11127.6330'), 42)]
a = coeffs('E', 0, NC)
ok = 0
from mpmath import findroot
for sig, t0, N in SURV:
    phi = make_phi(a, N)
    rho = findroot(phi, mpc(sig, t0), solver='muller', tol=mpf('1e-30'))
    eta = re(rho) - mpf('0.5')
    PN = (pi**(-rho/2)*Gamma(rho/2)*mpf(N)**(-rho)
          + pi**(-(1-rho)/2)*Gamma((1-rho)/2)*mpf(N)**(rho-1))
    dphi = diff(phi, rho)
    reach = fabs(PN)/fabs(dphi)
    # transcription check: Phi_{N-1}(rho) = -P_N(rho)
    phim = make_phi(a, N-1)
    chk = fabs(phim(rho) + PN)/fabs(PN)
    good = reach >= eta/2
    ok += 1 if good else 0
    print(f"t0={float(t0):.1f} N={N}: eta={float(eta):.3f} "
          f"reach={float(reach):.3f} reach/eta={float(reach/eta):.2f} "
          f"{'HELD' if good else 'BEYOND-REACH'} (chk={float(chk):.1e})")
print(f"\nP-T1 reach >= eta/2 at {ok}/8: {'PASS' if ok == 8 else 'FAIL'}")
