from mpmath import mp, mpf, pi, zeta, stieltjes, pslq, log, log10, diff

def run(dps, maxcoeff):
    mp.dps = dps
    g0, g1 = stieltjes(0), stieltjes(1)         # Euler γ, Stieltjes γ1
    L2pi = log(2*pi)                            # = -2 ζ'(0)
    zp_m1 = diff(lambda s: zeta(s), -1)         # ζ'(-1) = 1/12 - log A (Glaisher)
    zp_0  = diff(lambda s: zeta(s), 0)          # ζ'(0) = -½ log(2π)
    P2, z3, z5 = pi**2, zeta(3), zeta(5)
    tests = {
      "regularized set {1,γ0,γ1,log2π,ζ'(-1)}": [mpf(1), g0, g1, L2pi, zp_m1],
      "sanity ζ'(0)+½log2π = 0 (known)        ": [zp_0, L2pi],   # expect relation 2·ζ'(0)+log2π=0
      "CROSS {1,γ0,log2π,ζ'(-1),π²,ζ3,ζ5}     ": [mpf(1), g0, L2pi, zp_m1, P2, z3, z5],
    }
    out=[]
    for name, vec in tests.items():
        n=len(vec); guard=n*log10(maxcoeff)
        rel = pslq(vec, maxcoeff=int(maxcoeff), maxsteps=10**5)
        safe = "precision-safe" if dps > 1.5*guard else "GUARD-LOW"
        out.append((name, rel, n, float(guard), safe))
    return out

print("=== meta-principle test: are regularized/derivative constants free of periods? ===")
for dps in (150, 300):
    print(f"\n--- dps={dps}, maxcoeff=1e12 ---")
    for name, rel, n, guard, safe in run(dps, 1e12):
        verdict = "NO relation" if rel is None else f"RELATION {rel}"
        print(f"  {name}: {verdict}  (n={n}, guard≈{guard:.0f}, {safe})")
