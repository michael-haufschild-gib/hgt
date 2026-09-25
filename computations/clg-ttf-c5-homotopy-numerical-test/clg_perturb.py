"""Relative size of the homotopy change: |M(1)-M(0)|/M(0), sup|M'|/M(0), and d-jet/atom-jet ratios on the structural tail."""
from mpmath import mp, mpf, log, pi
import clg_compensation as C
from clg_full import comps
mp.dps = 120; C.mp.dps = 120; C.NMAX = 60
umin = log(mpf(6)/pi)/2
worst = mpf(0); worst_pt = None; rows = []
for u in [umin + mpf(k)/20 for k in range(0, 60)] + [mpf(x) for x in ("4","6")]:
    for fr in ("0.01","0.1","0.5","0.9","1.0"):
        t = u*mpf(fr); D = C.data(u, t)
        M = [comps(D, mpf(k)/10) for k in range(11)]
        M0 = M[0][0]; M1 = M[10][0]
        rel = abs(M1 - M0)/M0
        supM1 = max(abs(m[1]) for m in M)/M0
        jets = max(abs(D['dq']/D['q']), abs(D['da']/D['a']), abs(D['db']/D['b']), abs(D['dc']/D['c']), abs(D['ds']/D['s']), abs(D['dm']/D['m']), abs(D['dn']/D['n']))
        if rel > worst: worst, worst_pt = rel, (float(u), float(t))
        rows.append((float(u), float(t), mp.nstr(rel, 3), mp.nstr(supM1, 3), mp.nstr(jets, 3), mp.nstr(M0, 3)))
print("max |M(1)-M(0)|/M(0) on the tail:", mp.nstr(worst, 4), "at", worst_pt)
for r in rows[::13]: print(r)
