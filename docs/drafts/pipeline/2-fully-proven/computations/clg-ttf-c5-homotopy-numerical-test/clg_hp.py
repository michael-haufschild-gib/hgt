from mpmath import mp, mpf, exp
import clg_compensation as C
from clg_signs import pieces
import sys
mp.dps = 400; C.mp.dps = 400; C.NMAX = 80
worst = (None, 1e9)
rows = []
for u in [mpf(x) for x in ("1.5","2","2.5","3","4","5","6","8")] + [mpf(x) for x in ("0.001","0.005","0.01")]:
    for fr in ("0.001","0.01","0.1","0.3","0.5","0.7","0.9","0.99","1.0"):
        t = u*mpf(fr); D = C.data(u, t)
        for l in (mpf(0), mpf("0.25"), mpf("0.5"), mpf("0.75"), mpf(1)):
            P = pieces(D, l)
            c3 = P['c3']; T1, T2, T3 = P['T1'], P['T2'], P['T3']
            ratio = (T1 if T1 > 0 else mpf(0))/(abs(T2)+abs(T3)) if (abs(T2)+abs(T3)) != 0 else mpf('nan')
            rows.append((float(u), float(t), float(l), mp.nstr(c3, 4), mp.nstr(ratio, 3), "+" if c3 > 0 else ("-" if c3 < 0 else "0")))
            if c3 <= 0: worst = ((float(u), float(t), float(l)), float(c3))
print("any nonpositive c3:", worst)
for r in rows[::4]: print(r)
