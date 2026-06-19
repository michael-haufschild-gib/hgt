from mpmath import mp, mpf, pi, zeta, stieltjes, pslq, log10

def run(dps, maxcoeff):
    mp.dps = dps
    g = [stieltjes(n) for n in range(4)]   # γ0=γ_E, γ1, γ2, γ3
    P2 = pi**2
    z3, z5, z7 = zeta(3), zeta(5), zeta(7)
    tests = {
      "Stieltjes linear  {1,γ0,γ1,γ2,γ3}": [mpf(1), g[0], g[1], g[2], g[3]],
      "period linear     {1,π²,ζ3,ζ5,ζ7}": [mpf(1), P2, z3, z5, z7],
      "CROSS linear      {1,π²,ζ3,ζ5,γ0,γ1,γ2}": [mpf(1), P2, z3, z5, g[0], g[1], g[2]],
      "CROSS quad-ish    {1,γ0,γ0²,π²,ζ3,γ1}": [mpf(1), g[0], g[0]**2, P2, z3, g[1]],
    }
    out=[]
    for name, vec in tests.items():
        n=len(vec); guard=n*log10(maxcoeff)
        rel = pslq(vec, maxcoeff=int(maxcoeff), maxsteps=10**5)
        safe = "precision-safe" if dps > 1.5*guard else "GUARD-LOW"
        out.append((name, rel, n, float(guard), safe))
    return out

print("=== (DSS-cross) numerical test: are Stieltjes constants free of the period field? ===")
for dps in (150, 300):
    print(f"\n--- dps={dps}, maxcoeff=1e12 ---")
    for name, rel, n, guard, safe in run(dps, 1e12):
        verdict = "NO relation" if rel is None else f"RELATION {rel}"
        print(f"  {name:42s}: {verdict}   (n={n}, guard≈{guard:.0f}, {safe})")
