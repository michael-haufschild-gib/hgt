#!/usr/bin/env python3.13
"""
P-H — majorization march of the equilibrium pole weights (task #138, doc 26).

At each critical point c_i of A_d (reversed equilibrium y_i = 1/c_i, reciprocal zeros
b_k = 1/a_k): xi_k^{(i)} := y_i/(y_i - b_k). Sum rule (exact, proved): sum_k xi_k = d at
EVERY equilibrium. Flip <=> S_i := sum xi_k^2 > (d - a*y_i)^2 + b^2*y_i^2 ~ d^2.
S is Schur-convex, so single crossing would follow from:

Pre-registered prediction (BEFORE the run):
  P-H: along consecutive OUTER equilibria (i >= i_mid), xi^{(i+1)} majorizes xi^{(i)}:
       all partial sums of the descending-sorted vectors satisfy
       sum_{k<=m} xi_sorted^{(i+1)} >= sum_{k<=m} xi_sorted^{(i)} - tol, every m.
       Report: #violating pairs, and separately whether the TOP-1 partial sum
       (the dominant weight) is monotone — the weak form that already feeds the
       S-race in the crossing band.
FAIL of full majorization but PASS of a top-segment form re-cuts (MAJ) to top-k
domination; FAIL of both kills the Schur route.
"""
from mpmath import mp, mpf, factorial, binomial, polyroots

mp.dps = 60

MODELS = [
    ("cos-sqrt, tau=10+4i", None, mpf(10), mpf(4), [16, 24, 40]),
    ("(1-x/9)cos-sqrt, tau=2+3i", 9, mpf(2), mpf(3), [16, 24, 40]),
]


def gamma_seq(x0, jmax):
    cs = [mpf(-1) ** k / factorial(2 * k) for k in range(jmax + 1)]
    if x0 is not None:
        cs = [cs[j] - (cs[j - 1] / x0 if j >= 1 else 0) for j in range(jmax + 1)]
    return [factorial(j) * cs[j] for j in range(jmax + 1)]


for label, x0, aa, bb, ds in MODELS:
    print(f"==== model: {label} ====")
    for d in ds:
        gam = gamma_seq(x0, d)
        coef = [binomial(d, j) * gam[j] for j in range(d + 1)]
        dcoef = [coef[j] * j for j in range(1, d + 1)]
        alph = sorted(r.real for r in polyroots(list(reversed(coef)),
                                                maxsteps=300, extraprec=300))
        crit = sorted(r.real for r in polyroots(list(reversed(dcoef)),
                                                maxsteps=300, extraprec=300))
        bet = [1 / a for a in alph]
        xis, sums = [], []
        for c in crit:
            y = 1 / c
            xi = sorted((y / (y - b) for b in bet), reverse=True)
            xis.append(xi)
            sums.append(sum(xi))
        sr_err = max(abs(s - d) for s in sums)
        mid = len(crit) // 2
        tol = mpf(10) ** (-30)
        maj_viol, top1_viol = 0, 0
        for i in range(mid, len(crit) - 1):
            p1, p2 = mpf(0), mpf(0)
            ok = True
            for m in range(d):
                p1 += xis[i][m]
                p2 += xis[i + 1][m]
                if p2 < p1 - tol:
                    ok = False
                    break
            if not ok:
                maj_viol += 1
            if xis[i + 1][0] < xis[i][0] - tol:
                top1_viol += 1
        S = [sum(x * x for x in xi) for xi in xis]
        s_viol = sum(1 for i in range(mid, len(crit) - 1) if S[i + 1] <= S[i])
        print(f" d={d}: sum-rule err={mp.nstr(sr_err, 3)} | outer pairs={len(crit)-1-mid} "
              f"| full-majorization viol={maj_viol} | top1 viol={top1_viol} "
              f"| S-monotone viol={s_viol}")
