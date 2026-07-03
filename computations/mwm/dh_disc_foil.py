#!/usr/bin/env python3
"""
(DISC-zeta) foil test on the REAL objects — task #132, doc 20 SS4.

Skeleton: structural mutation of mirror_test.py (same D-H family, chi mod 5, kappa).

PRE-REGISTERED PREDICTIONS (before first run):
  Recentered Jensen sections of the t-plane carriers at window centers:
    gamma(m) = XiCarrier^{(m)}(t0),  J^{d,n}(X) = sum_j C(d,j) gamma(n+j) X^j.
  D-H carrier XiDH(t) = Re Phi(1/2+it), Phi(s) = (5/pi)^{(s+1)/2} Gamma((s+1)/2) f_kappa(s);
  its certified off-line zero rho = 0.808517182456637386 + 85.6993484853775922i
  becomes the non-real t-plane pair t = gamma0 -+ i(beta-1/2) (distance 0.3085 from
  the real t-axis; local zero spacing ~1). zeta carrier Xi(t) = Re xi(1/2+it).

  PA (carrier reality):   |Im Phi(1/2+it)| / |Phi| < 1e-15 on sample points.
  PB (zero sanity):       findroot from the banked seed stays within 1e-6 of it.
  PC (FOIL):   D-H recentered sections at t0 = Im rho: non-real pair count = 1
               (disc < 0) for d in {4,6,8}, n in {0,1}.
  PD (CONTROL): zeta recentered sections at t0 = 85.6993...: count = 0 (disc > 0).
  FALSIFIER: PC count 0 (reader misses a real off-line zero) or >= 2 (spurious pairs
  on the real object) kills the (DISC-zeta) shape from doc 20.
"""
from mpmath import mp, mpc, mpf, zeta, gamma as Gamma, pi, sqrt, findroot, fabs, diff, binomial, polyroots, re, im

mp.dps = 50

i = mpc(0, 1)
chi = {1: mpc(1), 2: i, 3: -i, 4: mpc(-1)}
kappa = (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)
RHO = mpc(mpf('0.808517182456637386'), mpf('85.6993484853775922'))


def L(s, conj_char=False):
    tot = mpc(0)
    for a in range(1, 5):
        c = chi[a].conjugate() if conj_char else chi[a]
        tot += c * zeta(s, mpf(a) / 5)
    return 5 ** (-s) * tot


def f_dh(s):
    return (1 - i * kappa) / 2 * L(s) + (1 + i * kappa) / 2 * L(s, True)


def Phi_dh(s):
    return (5 / pi) ** ((s + 1) / 2) * Gamma((s + 1) / 2) * f_dh(s)


def xi_zeta(s):
    return s * (s - 1) / 2 * pi ** (-s / 2) * Gamma(s / 2) * zeta(s)


def carrier(F):
    def Xi(t):
        return F(mpf(1) / 2 + i * t)
    return Xi


def pair_counts(Xi_complex, t0, dmax=8):
    # jets: real carrier => take real part after checking Im is noise
    gam = []
    for m in range(dmax + 2):
        d = diff(Xi_complex, t0, m, direction=0)
        gam.append(re(d))
    out = {}
    for d in (4, 6, 8):
        for n in (0, 1):
            coeffs = [binomial(d, j) * gam[n + j] for j in range(d, -1, -1)]
            roots = polyroots(coeffs, maxsteps=200, extraprec=200)
            nr = sum(1 for r in roots if fabs(im(r)) / (1 + fabs(r)) > mpf('1e-25'))
            assert nr % 2 == 0
            out[(d, n)] = nr // 2
    return out, gam


if __name__ == "__main__":
    # PA carrier reality
    worst = mpf(0)
    for tt in (mpf('80.1'), mpf('85.7'), mpf('90.3')):
        v = Phi_dh(mpf(1) / 2 + i * tt)
        worst = max(worst, fabs(im(v)) / fabs(v))
    print("PA max |Im|/|Phi| on line =", worst, "PASS" if worst < mpf('1e-15') else "FAIL")

    # PB zero sanity
    r = findroot(f_dh, RHO)
    print("PB |root-seed| =", fabs(r - RHO), "PASS" if fabs(r - RHO) < mpf('1e-6') else "FAIL")

    t0 = im(r)
    XiDH = carrier(Phi_dh)
    cDH, gDH = pair_counts(XiDH, t0)
    print("PC D-H recentered pair counts:", {k: v for k, v in sorted(cDH.items())})
    pc = all(v == 1 for v in cDH.values())
    print("PC PASS" if pc else "PC FAIL")

    XiZ = carrier(xi_zeta)
    cZ, gZ = pair_counts(XiZ, t0)
    print("PD zeta recentered pair counts:", {k: v for k, v in sorted(cZ.items())})
    pd = all(v == 0 for v in cZ.values())
    print("PD PASS" if pd else "PD FAIL")
