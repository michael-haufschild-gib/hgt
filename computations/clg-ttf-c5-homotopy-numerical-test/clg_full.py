"""Test all pieces of the C5 likelihood-homotopy card: M'''>0 on [0,1], M''(0)>=0, M'(0) >= -M(0)/5, M(1)>0,
   on the physical structural tail 0<t<=u, pi e^{2u} >= 6 (u >= 0.3236)."""
from mpmath import mp, mpf, exp, log, pi
import clg_compensation as C
mp.dps = 120; C.mp.dps = 120; C.NMAX = 60
def comps(D, l):
    t = D['t']; aff = lambda x, dx: x + l*dx
    jet1 = aff(D['a'], D['da']); jet2 = aff(D['b'], D['db']); jet3 = aff(D['c'], D['dc'])
    sA = aff(D['s'], D['ds']); sM1 = aff(D['m'], D['dm']); sM2 = aff(D['n'], D['dn']); act = aff(D['q'], D['dq'])
    vC = jet1*(t*sM1) - (jet1 + t*jet2)*sA
    vC1 = D['da']*(t*sM1) + jet1*(t*D['dm']) - (D['da'] + t*D['db'])*sA - (jet1 + t*jet2)*D['ds']
    vC2 = 2*(D['da']*(t*D['dm']) - (D['da'] + t*D['db'])*D['ds'])
    vS = jet1*(t*sM1 + t**2*sM2) - (jet1 + 3*t*jet2 + t**2*jet3)*sA
    vS1 = D['da']*(t*sM1 + t**2*sM2) + jet1*(t*D['dm'] + t**2*D['dn']) - (D['da'] + 3*t*D['db'] + t**2*D['dc'])*sA - (jet1 + 3*t*jet2 + t**2*jet3)*D['ds']
    vS2 = 2*(D['da']*(t*D['dm'] + t**2*D['dn']) - (D['da'] + 3*t*D['db'] + t**2*D['dc'])*D['ds'])
    e = exp(act); r = e - 1; dq = D['dq']
    bR = 1/r; bR1 = -e*dq/r**2; bR2 = e*(e+1)*dq**2/r**3; bR3 = -e*(e**2+4*e+1)*dq**3/r**4
    v = t*jet1; dv = t*D['da']
    bC = 14 + 10*v + 8*v*bR; bC1 = 10*dv + 8*(dv*bR + v*bR1); bC2 = 8*(2*dv*bR1 + v*bR2); bC3 = 8*(3*dv*bR2 + v*bR3)
    M0 = 5*vS - bC*vC
    M1 = 5*vS1 - bC1*vC - bC*vC1
    M2 = 5*vS2 - bC2*vC - 2*bC1*vC1 - bC*vC2
    M3 = -(bC3*vC + 3*bC2*vC1 + 3*bC1*vC2)
    return M0, M1, M2, M3
umin = log(mpf(6)/pi)/2
print("u_min =", mp.nstr(umin, 6))
bad = {"M3":[], "M2_0":[], "tangent":[], "M1_end":[]}
rows = []
for u in [umin + mpf(k)/40 for k in range(0, 120)] + [mpf(x) for x in ("4","5","6")]:
    for fr in ("0.01","0.1","0.25","0.5","0.75","0.9","1.0"):
        t = u*mpf(fr); D = C.data(u, t)
        m3min = min(comps(D, mpf(k)/10)[3] for k in range(11))
        M0_0, M1_0, M2_0, _ = comps(D, mpf(0)); M0_1, _, _, _ = comps(D, mpf(1))
        tang = M1_0 + M0_0/5
        if m3min <= 0: bad["M3"].append((float(u), float(t)))
        if M2_0 < 0: bad["M2_0"].append((float(u), float(t), float(M2_0)))
        if tang < 0: bad["tangent"].append((float(u), float(t), float(tang)))
        if M0_1 <= 0: bad["M1_end"].append((float(u), float(t), float(M0_1)))
        rows.append((float(u), float(t), mp.nstr(m3min,3), mp.nstr(M2_0,3), mp.nstr(tang,3), mp.nstr(M0_0,3), mp.nstr(M0_1,3)))
print("points:", len(rows))
for k, v in bad.items(): print(k, "violations:", len(v), v[:6])
for r in rows[::37]: print(r)
