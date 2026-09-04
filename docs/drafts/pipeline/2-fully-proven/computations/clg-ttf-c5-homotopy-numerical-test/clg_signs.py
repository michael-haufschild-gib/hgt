import sys
from mpmath import mp, mpf, exp
import clg_compensation as C
mp.dps = 80; C.mp.dps = 80; C.NMAX = 60
def pieces(D, l):
    t = D['t']; aff = lambda x, dx: x + l*dx
    jet1 = aff(D['a'], D['da']); jet2 = aff(D['b'], D['db'])
    sA = aff(D['s'], D['ds']); sM1 = aff(D['m'], D['dm']); act = aff(D['q'], D['dq'])
    vC = jet1*(t*sM1) - (jet1 + t*jet2)*sA
    vC1 = D['da']*(t*sM1) + jet1*(t*D['dm']) - (D['da'] + t*D['db'])*sA - (jet1 + t*jet2)*D['ds']
    vC2 = 2*(D['da']*(t*D['dm']) - (D['da'] + t*D['db'])*D['ds'])
    e = exp(act); r = e - 1; dq = D['dq']
    bR = 1/r; bR1 = -e*dq/r**2; bR2 = e*(e+1)*dq**2/r**3; bR3 = -e*(e**2 + 4*e + 1)*dq**3/r**4
    v = t*jet1; dv = t*D['da']
    bC1 = 10*dv + 8*(dv*bR + v*bR1); bC2 = 8*(2*dv*bR1 + v*bR2); bC3 = 8*(3*dv*bR2 + v*bR3)
    return dict(dq=dq, da=D['da'], vC=vC, vC1=vC1, vC2=vC2, bC1=bC1, bC2=bC2, bC3=bC3, T1=bC3*vC, T2=3*bC2*vC1, T3=3*bC1*vC2, c3=-(bC3*vC+3*bC2*vC1+3*bC1*vC2), act=act, jet1=jet1)
pats = {}
rows = []
for u in [mpf(x) for x in ("0.02","0.05","0.1","0.2","0.3","0.5","0.7","1.0","1.3","1.6")]:
    for fr in ("0.05","0.2","0.5","0.8","1.0"):
        t = u*mpf(fr); D = C.data(u, t)
        for l in (mpf(0), mpf("0.5"), mpf(1)):
            P = pieces(D, l)
            sg = "".join("+" if P[k] > 0 else ("-" if P[k] < 0 else "0") for k in ("dq","da","vC","vC1","vC2","bC1","bC2","bC3","T1","T2","T3","c3"))
            pats[sg] = pats.get(sg, 0) + 1
            rows.append((float(u), float(t), float(l), sg, mp.nstr(P['c3'], 5), mp.nstr(P['T1'],4), mp.nstr(P['T2'],4), mp.nstr(P['T3'],4)))
print("sign patterns (dq da vC vC1 vC2 bC1 bC2 bC3 T1 T2 T3 c3):")
for k, v in sorted(pats.items(), key=lambda kv: -kv[1]): print("  ", k, v)
for r in rows[::7]: print(r)
