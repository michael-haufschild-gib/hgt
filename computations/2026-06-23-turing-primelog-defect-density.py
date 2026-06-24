#!/usr/bin/env python3
"""
crystal-defects x queueing collision with the ARITHMETIC axis (seed 3875624814646229910).
A defect in the {log p} set = a hidden algebraic relation. Linear defects are
forbidden (unique factorization / Baker). Degree-2 defects = open (Schanuel).

Concrete test with controls: run integer-relation search (PSLQ) on degree-2
monomials of prime-logs, and CALIBRATE against:
  (+) POSITIVE control: {log6,log10,log15} which have KNOWN linear relations
      (log6=log2+log3) -> PSLQ must find them (verifies the instrument).
  (0) NULL controls: degree-2 monomials of (a) logs of random large primes,
      (b) transcendentals {pi,e,euler}. These should be as relation-free as prime-logs.

Verdict: if prime-log degree-2 set is relation-free at the SAME precision depth as
the null controls -> generic, no special arithmetic 'defect', Schanuel-consistent
(reduces). If prime-logs admit a relation a matched null does not -> anomaly/signal.
"""
import mpmath as mp
mp.mp.dps = 120

def deg2_monos(vals):
    # [1] + vals + all products v_i*v_j (i<=j)
    out = [mp.mpf(1)] + list(vals)
    n = len(vals)
    for i in range(n):
        for j in range(i, n):
            out.append(vals[i] * vals[j])
    return out

def try_pslq(label, vals, maxcoeff=10**6, maxsteps=10000):
    try:
        rel = mp.pslq(vals, maxcoeff=maxcoeff, maxsteps=maxsteps)
    except Exception as e:
        rel = None
        print(f"  [{label}] pslq error: {e}")
        return
    if rel is None:
        print(f"  [{label}] NO integer relation (maxcoeff={maxcoeff}) over {len(vals)} values")
    else:
        # verify
        s = mp.fsum(mp.mpf(rel[i]) * vals[i] for i in range(len(vals)))
        nz = sum(1 for c in rel if c != 0)
        print(f"  [{label}] RELATION found, {nz} nonzero coeffs, residual={mp.nstr(s,5)}, coeffs={rel}")

L = {p: mp.log(p) for p in [2,3,5,7,11,13]}

print("=== (+) POSITIVE control: linear relations among log6,log10,log15 (should FIND) ===")
pos = [mp.log(1), mp.log(2), mp.log(3), mp.log(5), mp.log(6), mp.log(10), mp.log(15)]
try_pslq("pos-linear", pos)

print("\n=== degree-2 prime-log sets (should find NO relation if Schanuel) ===")
try_pslq("primelogs {2,3,5}", deg2_monos([L[2],L[3],L[5]]))
try_pslq("primelogs {2,3,5,7}", deg2_monos([L[2],L[3],L[5],L[7]]))

print("\n=== (0) NULL control A: logs of random large primes (same structure) ===")
import sympy
rps = [sympy.prime(k) for k in [200, 350, 500]]   # the 200th,350th,500th primes
rpl = [mp.log(int(p)) for p in rps]
print(f"  random primes: {rps}")
try_pslq("randprimelogs", deg2_monos(rpl))

print("\n=== (0) NULL control B: transcendentals {pi,e,euler} ===")
try_pslq("transcend", deg2_monos([mp.pi, mp.e, mp.euler]))

print("\n=== (0) NULL control C: logs of {2,3,5} vs degree-2 BUT also add cross with pi (mixed) ===")
try_pslq("primelogs+pi {2,3,5,pi}", deg2_monos([L[2],L[3],L[5],mp.pi]))

print("\nDONE. Expectation: pos-linear FOUND; all degree-2 sets (prime + null) relation-free")
print("at maxcoeff=1e6 -> prime-logs show NO special degree-2 defect vs controls (generic).")
