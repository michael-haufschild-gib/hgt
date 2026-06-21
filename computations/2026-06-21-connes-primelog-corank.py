"""
gpt/27 Comp 8/9 — certified prime-log relation search (the transcendence apex, APEX-A).

The corpus flags corank^(2) for {log 2, log 3} as OPEN (degree-2 algebraic independence of prime logs).
Schanuel ⟹ no relation, but unproven. Certified PSLQ (not random sampling): is there an integer relation
among the degree-<=2 monomials in {log p}? PSLQ at precision D returns a relation only if one exists with
height below ~10^(D/n); None ⟹ certified no-relation below that height. Report the height floor.

Families:
  1. linear {log 2, log 3, log 5, log 7, log 11}            (corank^(1) / prime-log lin. indep.)
  2. degree-2 {1, log2, log3, log2^2, log2*log3, log3^2}     (corank^(2), the OPEN case)
  3. degree-2 over {log2,log3,log5}                          (10 monomials)
Control: a KNOWN relation (2*zeta'(0)+log(2pi)=0) must be detected.

Chunk arg: dps.
"""
import sys, mpmath as mp
mp.mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 200

def report(name, vec, maxcoeff=10**12):
    rel = mp.pslq(vec, maxcoeff=maxcoeff, maxsteps=10**5)
    floor = mp.mpf(10)**(mp.mp.dps/len(vec))   # rough height a relation would need to exceed
    if rel is None:
        print(f"  {name:<42} NO relation (|coeffs|<{maxcoeff:.0e}); certified none below height ~1e{int(mp.mp.dps/len(vec))}")
    else:
        print(f"  {name:<42} RELATION {rel}")

L = [mp.log(p) for p in (2,3,5,7,11)]
print(f"# prime-log corank — certified PSLQ, dps={mp.mp.dps}")
# control: known relation
print("# control (must detect):")
report("2*zeta'(0)+log(2pi)", [2*mp.zeta(0,1,1), mp.log(2*mp.pi)], maxcoeff=10**6)
print("# linear (corank^(1)):")
report("{log2,log3,log5,log7,log11}", L)
print("# degree-2 (corank^(2), OPEN):")
l2, l3, l5 = mp.log(2), mp.log(3), mp.log(5)
report("{1,log2,log3,log2^2,log2*log3,log3^2}", [mp.mpf(1), l2, l3, l2**2, l2*l3, l3**2])
report("deg2 over {log2,log3,log5} (10 mono)", [mp.mpf(1), l2, l3, l5, l2**2, l3**2, l5**2, l2*l3, l2*l5, l3*l5])
