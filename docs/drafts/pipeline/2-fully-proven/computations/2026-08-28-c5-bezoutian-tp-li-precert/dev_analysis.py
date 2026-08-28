"""Deviation-variable analysis: sizes of A = alpha-2q, B = beta-2q vs slack, F_gauss check."""
import json, math
rows = []
for line in open("/root/precert/c5_grid.jsonl"):
    r0 = json.loads(line)
    if "error" in r0 or r0["tq1"] is None or r0["t2q2"] is None or r0["r_log10"] is None: continue
    if r0["r_log10"] > 30: continue   # far zone: trivially dominated
    rr = 10.0**r0["r_log10"]
    q = math.log1p(rr)
    al = r0["tq1"]; be = r0["t2q2"]
    A = al - 2*q; B = be - 2*q
    Fg = 24*rr*rr - 8*q*rr - 20*q*q*rr - 16*q*q
    T = Fg + 5*rr*B - (9*rr + 16*q + 20*q*rr)*A - (4 + 5*rr)*A*A
    T_direct = 24*rr**2 - 9*al*rr + 5*rr*be - 4*al**2 - 5*al**2*rr
    rows.append((r0["u"], r0["t"], q, rr, A, B, Fg, T, T_direct))
print("points in bulk window:", len(rows))
# identity check
iderr = max(abs(T - Td)/(abs(Td)+1e-30) for *_, T, Td in rows)
print("max deviation-identity rel err:", f"{iderr:.2e}")
# F_gauss nonnegativity check
fmin = min((Fg, u, t, q) for u, t, q, rr, A, B, Fg, T, Td in rows)
print("min F_gauss:", fmin[:1], "at u,t,q =", fmin[1:])
# deviation sizes normalized by q^2 (cusp scale) in the handover window q <= 2
w = [x for x in rows if 1e-4 < x[2] <= 2.0]
maxAq2 = max((abs(A)/q**2, u, t, q) for u, t, q, rr, A, B, Fg, T, Td in w)
maxBq2 = max((abs(B)/q**2, u, t, q) for u, t, q, rr, A, B, Fg, T, Td in w)
minA = min((A/q**2, u, t, q) for u, t, q, rr, A, B, Fg, T, Td in w)
minB = min((B/q**2, u, t, q) for u, t, q, rr, A, B, Fg, T, Td in w)
print("q<=2 window:", len(w))
print("max |A|/q^2:", [round(v,4) for v in maxAq2])
print("max |B|/q^2:", [round(v,4) for v in maxBq2])
print("min A/q^2:", [round(v,4) for v in minA])
print("min B/q^2:", [round(v,4) for v in minB])
# where is T tightest relative to F_gauss in bulk q in [0.1, 3]?
w2 = [x for x in rows if 0.1 <= x[2] <= 3.0]
tight = sorted(((T/(Fg+1e-30), u, t, q) for u, t, q, rr, A, B, Fg, T, Td in w2))[:6]
print("6 smallest T/F_gauss in q in [0.1,3]:")
for v in tight: print("  ", [round(x,4) for x in v])
