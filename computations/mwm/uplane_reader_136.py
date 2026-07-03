#!/usr/bin/env python3.13
"""
P-U — u-plane reader on the #136 truncation instance (task #140; docs 24 §6, 25 §5).

First theorem-track finite window: the truncation carrier's off-line pair read on the
ONE-SIDED-FAR u-plane carrier — the shape covered by doc 25's proved tracking clearance
and the T = 1 counting regime.

Object: g5(s) = sum_{n<=5} n^{-s} + chi(s) * sum_{n<=5} n^{s-1},
  chi(s) = pi^{s-1/2} * Gamma((1-s)/2) / Gamma(s/2)   (exact FE: g5(s) = chi(s) g5(1-s)).
Completion: Phi(s) = pi^{-s/2} * Gamma(s/2) * g5(s) — satisfies Phi(1-s) = Phi(s)
  EXACTLY (one-line check from chi), hence Phi(1/2 + w) = H(w^2) descends to the u-plane
  and H is real on the negative real axis (Schwarz + evenness).
Verified off-line zero (#136, DISC-RESULTS run 5): rho = beta + i*t0,
  beta = 0.60941068066067, t0 = 221.0788841113159, delta := beta - 1/2.
Recenter at u0 = -t0^2; local coordinate v: h(v) := Phi(1/2 + i*sqrt(t0^2 - v))
  (principal sqrt; the branch choice is irrelevant by evenness). The off-line pair sits
  at v_pair = delta^2 +- 2*i*delta*t0 ~ 0.012 +- 48.37i; nearest on-line zeros at
  |v| ~ 2*t0*(unit t-spacing) ~ 4e2: model-2 one-sided-far shape (bounded right range,
  infinite left range).
Reader: gamma(m) = m! * [v^m] h;  J^{d,0}(X) = sum_j C(d,j) gamma(j) X^j, d = 4, 6, 8.

Pre-registered predictions (BEFORE the run):
  P-U0: Newton refinement of rho on Phi converges with residual < 1e-30 (the #136 zero
        is a genuine zero of the completed carrier).
  P-U1: J^{d,0} has EXACTLY ONE non-real conjugate root pair for d = 4, 6, 8 —
        the u-plane reading matches the t-plane reading (run 5).
  P-U2: disc(J^{4,0}) < 0 (the mod-2 shadow).
  P-U3 (control): same reader on zeta's carrier xi(s) = (s(s-1)/2) pi^{-s/2} Gamma(s/2)
        zeta(s) at the SAME u0: ZERO non-real pairs at d = 4, 6, 8; disc(J^4) > 0
        (RH verified at this height — nothing to see).
FAIL of P-U1/P-U2 => the application map (doc 24 §6) is miswired; re-cut before any
theorem-track claim.
"""
from mpmath import mp, mpf, mpc, pi, gamma, sqrt, zeta, exp, factorial, binomial, polyroots

mp.dps = 120

BETA0 = mpf('0.60941068066067')
T0_SEED = mpf('221.0788841113159')
NTR = 5


def chi(s):
    return pi ** (s - mpf(1) / 2) * gamma((1 - s) / 2) / gamma(s / 2)


def g5(s):
    return (sum(mpf(n) ** (-s) for n in range(1, NTR + 1))
            + chi(s) * sum(mpf(n) ** (s - 1) for n in range(1, NTR + 1)))


def phi_trunc(s):
    return pi ** (-s / 2) * gamma(s / 2) * g5(s)


def xi_zeta(s):
    return s * (s - 1) / 2 * pi ** (-s / 2) * gamma(s / 2) * zeta(s)


def newton_zero(f, s, steps=40):
    for _ in range(steps):
        eps = mpf(10) ** (-30)
        fp = (f(s + eps) - f(s - eps)) / (2 * eps)
        ds = f(s) / fp
        s = s - ds
        if abs(ds) < mpf(10) ** (-60):
            break
    return s


# ---- P-U0: refine the off-line zero on the completed truncation carrier
rho = newton_zero(phi_trunc, mpc(BETA0, T0_SEED))
res = abs(phi_trunc(rho))
print(f"P-U0  rho = {mp.nstr(rho, 20)}   |Phi(rho)| = {mp.nstr(res, 3)}   "
      f"{'PASS' if res < mpf(10)**(-30) else 'FAIL'}")
delta, t0 = rho.real - mpf(1) / 2, rho.imag
print(f"      predicted v_pair = {mp.nstr(delta**2, 8)} +- {mp.nstr(2*delta*t0, 8)} i")

U0 = t0 * t0     # u0 = -t0^2; h(v) = Phi(1/2 + i*sqrt(U0 - v))


def jets(f, order, r=mpf(8), M=256):
    """Cauchy coefficients c_0..c_order of v -> f(1/2 + i*sqrt(U0 - v)) at v = 0,
    by the M-node trapezoid on |v| = r (exponentially accurate, f analytic)."""
    vals = []
    for k in range(M):
        th = 2 * pi * k / M
        v = r * exp(mpc(0, 1) * th)
        vals.append(f(mpf(1) / 2 + mpc(0, 1) * sqrt(U0 - v)))
    cs = []
    for m_ in range(order + 1):
        acc = mpc(0)
        for k in range(M):
            th = 2 * pi * k / M
            acc += vals[k] * exp(-mpc(0, 1) * m_ * th)
        cs.append(acc / (M * r ** m_))
    return cs


def read(cs, d):
    """Roots + pair count of J^{d,0}; coefficients normalized by c_0."""
    b = [binomial(d, j) * factorial(j) * (cs[j] / cs[0]) for j in range(d + 1)]
    im_noise = max(abs(x.imag) / (abs(x) + mpf(10) ** (-50)) for x in b)
    coeffs = [x.real for x in reversed(b)]           # leading first
    roots = polyroots(coeffs, maxsteps=200, extraprec=200)
    pairs = sum(1 for z in roots if abs(getattr(z, 'imag', mpf(0))) >
                mpf(10) ** (-25) * (1 + abs(z))) // 2
    dsc = mpf(1)
    for i in range(len(roots)):
        for j in range(i + 1, len(roots)):
            dsc *= (roots[i] - roots[j]) ** 2
    return pairs, dsc, im_noise


for label, f, pred_pairs in (("truncation g5", phi_trunc, 1), ("zeta control", xi_zeta, 0)):
    cs = jets(f, 8)
    print(f"---- {label}  (jets at u0 = -t0^2, |c0| = {mp.nstr(abs(cs[0]), 3)})")
    for d in (4, 6, 8):
        pairs, dsc, noise = read(cs, d)
        dsign = '<0' if dsc.real < 0 else '>0'
        ok = 'PASS' if pairs == pred_pairs else 'FAIL'
        print(f"  d={d}: nonreal pairs = {pairs} (pred {pred_pairs}) {ok}   "
              f"disc {dsign}   coeff-Im-noise = {mp.nstr(noise, 2)}")
