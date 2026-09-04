from mpmath import mp, mpf, exp
import clg_compensation as C
from clg_signs import pieces
mp.dps = 60; C.mp.dps = 60; C.NMAX = 60
def faces(D, l):
    t = D['t']; aff = lambda x, dx: x + l*dx
    jet1 = aff(D['a'], D['da']); P = pieces(D, l)
    vC, vC1, vC2, dq, da = P['vC'], P['vC1'], P['vC2'], P['dq'], P['da']
    v = t*jet1; dv = t*da
    Z0 = v*vC
    Z1 = dv*vC + v*vC1 - dq*Z0
    Z2 = 2*dv*vC1 + v*vC2 - 2*dq*(dv*vC + v*vC1) + dq**2*Z0
    Z3 = 3*dv*vC2 - 3*dq*(2*dv*vC1 + v*vC2) + 3*dq**2*(dv*vC + v*vC1) - dq**3*Z0
    return Z0, Z1, Z2, Z3, jet1
cnt = {}; fail = []
for u in [mpf(x)/20 for x in range(1, 41)]:
    for fr in ("0.05","0.2","0.4","0.6","0.8","1.0"):
        t = u*mpf(fr); D = C.data(u, t)
        for l in (mpf(0), mpf("0.5"), mpf(1)):
            Z = faces(D, l)
            sg = "".join("+" if z > 0 else ("-" if z < 0 else "0") for z in Z[:4]) + ("J+" if Z[4] > 0 else "J-")
            cnt[sg] = cnt.get(sg, 0) + 1
            if any(z > 0 for z in Z[:4]): fail.append((float(u), float(t), float(l), sg))
print("face sign patterns (Z0 Z1 Z2 Z3, jetOne sign):")
for k, v in sorted(cnt.items(), key=lambda kv: -kv[1]): print("  ", k, v)
print("cone failures:", len(fail), "of", sum(cnt.values()))
for f in fail[:12]: print("  ", f)
