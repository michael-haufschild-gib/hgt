#!/usr/bin/env python3.13
"""
P-C/P-D/P-E/P-F — the reversal identity and the log-gap race (task #138, doc 26).

Setup: g in LP0 with POSITIVE zeros, A_d = J^d_g hyperbolic (zeros a_1<...<a_d > 0),
critical points c_i in (a_i, a_{i+1}). Reversed field: b_k = 1/a_k, y = 1/c.
E(c) = sum (c-a_k)^{-2}; Ehat(y) = sum (y-b_k)^{-2}; Fhat(y) = sum (y-b_k)^{-1}.
margin(c) = q_d(c)/(c^4 E(c)), q_d = |tau|^2 - 2*a*d*c + d(d-1)c^2, tau = a+bi.
V(y) := Ahat(y)*exp(-a*y), Ahat = reversed section; V''/V = (Fhat-a)^2 - Ehat.

Pre-registered predictions (BEFORE the run):
  P-C (reversal identity, exact): at every critical point c of A_d,
      c^4*E(c) = Ehat(1/c) - d/c^{-2}... precisely: c^4 E(c) = Ehat(y) - d*(1/y)^...
      = Ehat(y) - d/y^2  with y = 1/c — algebraic identity via Fhat(y) = d/y at
      equilibria; MUST hold to working precision (~40+ digits) at ALL critical points.
  P-D (oscillator form): copy/flip verdict from margin > 1 vs the sign of
      (V''/V + b^2) = |Fhat - tau|^2 - Ehat agrees at EVERY critical point, and the
      ordered pattern has EXACTLY ONE copy->flip transition (d >= 10).
  P-E (log-gap monotonicity): delta_i = log a_{i+1} - log a_i is strictly decreasing
      in i on the outer half of the zero field (violations = 0 there).
  P-F (O(1) race): the copy->flip crossing index i* sits where d*delta_i crosses
      2*sqrt(q_d(c_i))/(d*c_i)-normalized threshold ~ O(1); far-end margin tends to a
      LIMIT in (0,1) (previously measured ~0.28 for model 1), not to 0.
FAIL of P-C kills the reversal identity (algebra error); FAIL of P-D kills the
oscillator reformulation; P-E/P-F chart the named core (LOG-GAP).
"""
from mpmath import mp, mpf, mpc, factorial, binomial, polyroots, log, sqrt

mp.dps = 80

MODELS = [
    ("cos-sqrt, tau=10+4i", None, mpf(10), mpf(4), [16, 24, 40]),
    ("(1-x/9)cos-sqrt, tau=2+3i", 9, mpf(2), mpf(3), [16, 24, 40]),
]


def gamma_seq(x0, jmax):
    """gamma_j = j! * c_j for g = cos(sqrt x) (x0 None) or (1 - x/x0)*cos(sqrt x)."""
    cs = [mpf(-1) ** k / factorial(2 * k) for k in range(jmax + 1)]
    if x0 is not None:
        cs = [cs[j] - (cs[j - 1] / x0 if j >= 1 else 0) for j in range(jmax + 1)]
    return [factorial(j) * cs[j] for j in range(jmax + 1)]


for label, x0, aa, bb, ds in MODELS:
    print(f"==== model: {label} ====")
    q0 = aa * aa + bb * bb
    for d in ds:
        gam = gamma_seq(x0, d)
        coef = [binomial(d, j) * gam[j] for j in range(d + 1)]          # ascending
        dcoef = [coef[j] * j for j in range(1, d + 1)]
        ddcoef = [dcoef[j] * j for j in range(1, d)]
        alph = sorted(r.real for r in polyroots(list(reversed(coef)),
                                                maxsteps=300, extraprec=300))
        crit = sorted(r.real for r in polyroots(list(reversed(dcoef)),
                                                maxsteps=300, extraprec=300))
        assert all(a > 0 for a in alph), "zeros must be positive"
        bet = [1 / a for a in alph]

        def horner(cf, x):
            v = mpf(0)
            for c_ in reversed(cf):
                v = v * x + c_
            return v

        pc_err = mpf(0)
        pattern = []
        osc_agree = True
        for c in crit:
            y = 1 / c
            E = sum((c - a) ** (-2) for a in alph)
            Ecx = -horner(ddcoef, c) / horner(coef, c)      # cross-check: -A''/A
            Ehat = sum((y - b) ** (-2) for b in bet)
            Fhat = sum((y - b) ** (-1) for b in bet)
            pc_err = max(pc_err, abs(c ** 4 * E - (Ehat - d / y ** 2)) / (c ** 4 * E),
                         abs(E - Ecx) / E)
            q = q0 - 2 * aa * d * c + d * (d - 1) * c * c
            marg = q / (c ** 4 * E)
            osc = (Fhat - aa) ** 2 + bb * bb - Ehat          # = V''/V + b^2
            if (marg > 1) != (osc > 0):
                osc_agree = False
            pattern.append('C' if marg > 1 else 'F')
        trans = sum(1 for i in range(len(pattern) - 1) if pattern[i] != pattern[i + 1])
        # P-E: log-gaps on the outer half
        dl = [log(alph[i + 1]) - log(alph[i]) for i in range(d - 1)]
        outer = dl[(d - 1) // 2:]
        viol = sum(1 for i in range(len(outer) - 1) if outer[i + 1] >= outer[i])
        # P-F: crossing index and far margin
        i_star = pattern.index('F') if 'F' in pattern else -1
        c_far = crit[-1]
        E_far = sum((c_far - a) ** (-2) for a in alph)
        m_far = (q0 - 2 * aa * d * c_far + d * (d - 1) * c_far ** 2) / (c_far ** 4 * E_far)
        ddel = [mp.nstr(d * x, 4) for x in (dl[max(0, i_star - 1)], dl[min(d - 2, i_star)])] \
            if i_star >= 0 else ['-', '-']
        print(f" d={d}: P-C err={mp.nstr(pc_err, 3)} | P-D agree={osc_agree} "
              f"transitions={trans} | P-E outer-viol={viol} | "
              f"P-F i*={i_star}/{len(pattern)} d*delta@i*={ddel} far-margin={mp.nstr(m_far, 4)}")
