import json, math
rows = []
for line in open("/root/precert/c5_grid.jsonl"):
    r = json.loads(line)
    if "error" in r or r["tq1"] is None or r["t2q2"] is None or r["r_log10"] is None: continue
    if r["r_log10"] > 100: continue
    rr = 10.0**r["r_log10"]
    a = r["tq1"]; b = r["t2q2"]
    num = 9*rr*a + 5*rr*a*a + 4*a*a
    den = 24*rr*rr + 5*rr*b
    if den <= 0:
        print("NONPOS DEN:", r); continue
    rows.append((num/den, r["u"], r["t"], rr, a, b))
rows.sort(reverse=True)
print("top 12 criticality G = (9ra+5ra^2+4a^2)/(24r^2+5rb)  [G<1 <=> C5>0]:")
for G,u,t,rr,a,b in rows[:12]:
    print(f"  G={G:.6f} u={u:.3f} t={t:.4f} r={rr:.4g} a=tq1={a:.4g} b=t2q2={b:.4g} a/log1pr={a/math.log1p(rr):.4f}")
sl = [x for x in rows if x[2] < 0.002]; sl.sort(reverse=True)
print("t~0.001 slice top G:", [(round(g,5), u) for g,u,t,_,_,_ in sl[:4]])
sl2 = [x for x in rows if x[2] > 4.0]; sl2.sort(reverse=True)
print("t>4 top G:", [(round(g,5), u, round(t,2)) for g,u,t,_,_,_ in sl2[:4]])
