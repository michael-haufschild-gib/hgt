# Cycle 12: energy spread blocks the counterexample; refined conjecture (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-12 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsEnergySpread.lean`, wired, built, no sorry,
axioms clean.

## Scope of the cycle-11 falsification
The counterexample needs S energy-DEGENERATE (all elements comparable, e.g. primes in a
dyadic window [N,2N]). This is forced, not incidental:
- S1 `no_truncation_dichotomy`: a light/heavy dichotomy at level J requires
  max_{|T|=J} e(T) < min_{|T|=J+1} e(T). One (J+1)-set no heavier than some J-set refutes
  it: R ≤ x·e(T₂) ≤ x·e(T₁) ≤ ε < R.
- S2: for S = primes ≤ y, level J would need (product of J largest primes) < (J+1)-st
  primorial — false for large y (y^J vs a constant). Already {2,3,7} ⊆ S blocks level 1
  (`no_truncation_dichotomy_of_two_three_seven`, since 2·3 ≤ 7).

## THE REFINED OPEN CORE (Route E-relevant)
Cycle 11 falsifies sector stability for GENERAL S only. The natural gas is untouched.
**Refined conjecture: S = {p prime : p ≤ y} is sector-stable at every coupling.**
Structural dichotomy behind it:
  sharp truncation of the coefficient profile ⟹ Szegő regime ⟹ RHP zeros;
  gradual/super-exponentially decaying profile ⟹ Kurtz regime ⟹ real negative zeros.
Natural gas profile = Poisson-like bulk (mean λ = loglog(1/x)) + super-exponentially thin
primorial tail ⟹ expected to be in the Kurtz regime. NOTE: Kurtz's condition
A_j² > 4A_{j−1}A_{j+1} FAILS in the Poisson bulk (ratio 1+1/j), so the bulk needs a
different argument (the Poisson PGF e^{λ(z−1)} is entire and zero-free — that is the
heuristic reason the bulk contributes no zeros).

## Status of the whole gas programme (12 cycles)
Proved+formalized: vortex laws T0–T3′, locking law R1–R3, sector stability k ≤ 4 (all
couplings) and all k at weak coupling (x·σ(m) < 1), confinement W2, quantitative totient
law W4, two-scale engine U1 + levels 0/1/2, CONDENSATION LAW (cycle 10 — the load-bearing
identity, all couplings), truncation lemma Z1, falsification Z3/Z4, spread obstruction
S1/S2. Dead lines: X1 criterion (k ≥ 5), TSP engine (sufficient for a false statement),
general-S sector stability.
