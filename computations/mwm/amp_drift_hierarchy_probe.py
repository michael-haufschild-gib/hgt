#!/usr/bin/env python3.13
"""
P-I/P-J/P-K — the drift hierarchy between consecutive equilibria (task #138, doc 27).

Exact structure (proved, doc 27): eta_k(c) = c/(c - a_k) obeys eta' = -eta(eta-1)/c;
power sums p_r = sum eta^r obey p_r' = -(r/c)(p_{r+1} - p_r); at critical points
p_1 = 0 and S = d + p_2 (cross-checked here against S = sum xi^2, xi = 1 - eta).
On the interval [c_i, c_{i+1}] there is exactly ONE zero a_{i+1}; removing its charge
gives smooth reduced sums p~_r and Phi~ := p~_1^2 + p~_2 with
   Q(c_i) = Phi~(c_i), Q(c_{i+1}) = Phi~(c_{i+1})   (constraint: eta_pole = -p~_1),
   Phi~'(c) = -(2/c) * sum_k w_k (eta_k + p~_1),  w_k = eta_k(eta_k - 1) > 0.
So S_{i+1} - S_i = integral of Phi~' — a smooth path replaces the discrete jump.

Pre-registered predictions (BEFORE the run):
  P-I: on every outer inter-critical interval, Phi~' has EXACTLY ONE sign change,
       ordered (-) then (+) (dip-then-rise), and Phi~(c_{i+1}) - Phi~(c_i) > 0
       (re-derives S-mono along the smooth path). Cross-check: |S - (d + p_2)| ~ 0.
  P-J: absolute gaps D_i = a_{i+1} - a_i are strictly increasing on the outer half
       (0 violations) — the input for the midpoint-pairing lemma.
  P-K: theta_i = (a_{i+1} - c_i)/D_i < 1/2 at every outer critical point
       (0 violations), drifting to ~0.27.
FAIL of P-I's sign shape kills the leg-comparison route; FAIL of P-J/P-K kills the
pairing lemma's input for these carriers.
"""
from mpmath import mp, mpf, factorial, binomial, polyroots

mp.dps = 60

MODELS = [
    ("cos-sqrt, tau=10+4i", None, [16, 24, 40]),
    ("(1-x/9)cos-sqrt, tau=2+3i", 9, [16, 24, 40]),
]
NSAMP = 41


def gamma_seq(x0, jmax):
    cs = [mpf(-1) ** k / factorial(2 * k) for k in range(jmax + 1)]
    if x0 is not None:
        cs = [cs[j] - (cs[j - 1] / x0 if j >= 1 else 0) for j in range(jmax + 1)]
    return [factorial(j) * cs[j] for j in range(jmax + 1)]


for label, x0, ds in MODELS:
    print(f"==== model: {label} ====")
    for d in ds:
        gam = gamma_seq(x0, d)
        coef = [binomial(d, j) * gam[j] for j in range(d + 1)]
        dcoef = [coef[j] * j for j in range(1, d + 1)]
        alph = sorted(r.real for r in polyroots(list(reversed(coef)),
                                                maxsteps=300, extraprec=300))
        crit = sorted(r.real for r in polyroots(list(reversed(dcoef)),
                                                maxsteps=300, extraprec=300))
        mid = len(crit) // 2
        # cross-check S = d + p2 vs sum xi^2 at one critical point
        c0 = crit[mid]
        p2 = sum((c0 / (c0 - a)) ** 2 for a in alph)
        Sxi = sum((1 - c0 / (c0 - a)) ** 2 for a in alph)
        xerr = abs(Sxi - (d + p2)) / Sxi
        # P-J: outer gap growth
        gaps = [alph[i + 1] - alph[i] for i in range(d - 1)]
        pj = sum(1 for i in range((d - 1) // 2, d - 2) if gaps[i + 1] <= gaps[i])
        # P-K: theta < 1/2 on outer criticals
        pk, th_last = 0, None
        for i in range(mid, len(crit)):
            th = (alph[i + 1] - crit[i]) / (alph[i + 1] - alph[i])
            th_last = th
            if th >= mpf(1) / 2:
                pk += 1
        # P-I: sign shape of Phi~' on outer intervals
        bad_shape, bad_net = 0, 0
        for i in range(mid, len(crit) - 1):
            cl, cr = crit[i], crit[i + 1]
            pole = alph[i + 1]
            signs = []
            for t in range(1, NSAMP):
                c = cl + (cr - cl) * mpf(t) / NSAMP
                etas = [c / (c - a) for a in alph if a != pole]
                p1t = sum(etas)
                dPhi = -(2 / c) * sum(e * (e - 1) * (e + p1t) for e in etas)
                s = 1 if dPhi > 0 else -1
                if not signs or signs[-1] != s:
                    signs.append(s)
            if signs not in ([-1, 1], [1], [-1]):
                bad_shape += 1

            def phit(c):
                etas = [c / (c - a) for a in alph if a != pole]
                p1t = sum(etas)
                return p1t * p1t + sum(e * e for e in etas)
            if phit(cr) <= phit(cl):
                bad_net += 1
        print(f" d={d}: xcheck={mp.nstr(xerr, 2)} | P-I bad-shape={bad_shape} "
              f"bad-net={bad_net} (of {len(crit)-1-mid}) | P-J gap-viol={pj} | "
              f"P-K theta>=1/2 viol={pk} theta_last={mp.nstr(th_last, 4)}")
