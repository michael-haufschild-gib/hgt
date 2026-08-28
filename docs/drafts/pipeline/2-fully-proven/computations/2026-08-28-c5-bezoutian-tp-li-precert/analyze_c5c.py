import json
rows = []
for line in open("/root/precert/c5_grid.jsonl"):
    r = json.loads(line)
    if "error" in r or r["tq1"] is None or r["t2q2"] is None or r["r_log10"] is None: continue
    if r["r_log10"] > 100 or r["t"] < 0.25: continue
    rr = 10.0**r["r_log10"]; a = r["tq1"]; b = r["t2q2"]
    num = 9*rr*a + 5*rr*a*a + 4*a*a; den = 24*rr*rr + 5*rr*b
    rows.append((num/den, r["u"], r["t"], rr, a, b))
rows.sort(reverse=True)
print("interior (t>=0.25) top criticality G:")
for G,u,t,rr,a,b in rows[:8]:
    print(f"  G={G:.6f} u={u:.3f} t={t:.4f} r={rr:.4g} tq1={a:.4g} t2q2={b:.4g}")
