import mpmath as mp
mp.mp.dps = 240
N = 12
g = [mp.stieltjes(n) for n in range(N+1)]          # gamma_0..gamma_12 (gamma_0 = Euler-Mascheroni)
pi2  = mp.pi**2
z3,z5,z7 = mp.zeta(3), mp.zeta(5), mp.zeta(7)
log2pi = mp.log(2*mp.pi)                            # = -2 zeta'(0)
logA   = mp.log(mp.glaisher)                        # Glaisher; zeta'(-1)=1/12-logA  (exponential/non-period candidate)

def report(name, vec, maxcoeff=10**12):
    rel = mp.pslq(vec, maxcoeff=maxcoeff, maxsteps=10**5)
    print(f"[{name}] terms={len(vec)} -> {'RELATION '+str(rel) if rel else 'no relation (coeffs< %g)'%maxcoeff}")

print("=== Stieltjes independence experiment (dps=240) ===")
# A) linear floor: are gamma_0..gamma_12 Q-linearly independent (with 1)?
report("A linear-floor {1,gamma_0..12}", [mp.mpf(1)]+g)

# C) DSS-CROSS: gamma_n independent from motivic + exponential companions?
report("C cross {1,g0..g5,pi^2,z3,z5,z7,log2pi,logA}",
       [mp.mpf(1)]+g[:6]+[pi2,z3,z5,z7,log2pi,logA])

# B) low-degree ALGEBRAIC relations among g0,g1,g2 (the H_2/relations = apex level)
g0,g1,g2 = g[0],g[1],g[2]
deg2 = [mp.mpf(1), g0,g1,g2, g0*g0,g0*g1,g1*g1,g0*g2,g1*g2,g2*g2, pi2,z3,z5, log2pi,logA]
report("B deg<=2 algebraic {monomials(g0,g1,g2)+motivic}", deg2)

# B') is gamma_0^2 reducible to {gammas, motivic}? (test product structure = free vs constrained)
report("B' g0^2 vs {1,g0..g4,pi^2,z3,z5,log2pi,logA}",
       [g0*g0, mp.mpf(1)]+g[:5]+[pi2,z3,z5,log2pi,logA])
print("=== done ===")
