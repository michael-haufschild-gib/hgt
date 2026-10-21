# Arithmetic Continuation and Critical Energy (ACCE)

- **ID:** acce
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — programme
- **Source:** docs/reports/review-2110/astra.md § "New field - research programme"
- **Statement:** Which exact arithmetic relations prevent a complete signed critical energy from
  escaping under continuation in damping, cutoff or aperture?

## Goal
A Lean programme (`formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy`) supplying
the continuation and compensation theorems the RH work lacks: transport of an *endpoint* budget
backwards through a damping interval, the exact signed-work identity of the damped Möbius energy,
the countermodels that fix which uniformity is indispensable, and the discrete envelope tools for
sector compensation.

Non-circularity: every criterion names its arithmetic input (a horizon-uniform bound on one signed
pairing) and nothing about zeros. The continuation machinery itself is unconditional real analysis.

## Gates
- [x] 0 → 1  in-progress: objects fixed (energy family, admission, continuation, compensation)
- [ ] 1 → 2  fully-proven: paper proofs of the pillars
- [ ] 2 → 3  formalized: Lean modules + umbrella wiring
- [ ] 3 → 4  n/a (no stage 4)

## Approach
1. **Admission language.** `EnergyFamily := ℝ → ℕ → ℝ`; `Admits E ε := ∃ B, ∀ T, E ε T ≤ B`.
2. **Osgood/Grönwall backward continuation.** `Ψ` a primitive of `1/Φ`, `β` a primitive of the
   continuation budget: `-ψ(E_T) · E_T' ≤ β'` on `[a,c]` forces `Ψ(E_T(a)) ≤ Ψ(E_T(c)) + β(c) - β(a)`;
   coercive `Ψ` turns a budget at `c` into a budget at `a`, uniformly in the horizon.
3. **Signed work identity.** `∂_ε E_T(ε) = 2 Σ_{n≤T} A_ε(n) E_ε(n)/(n(n+1))` for the centred damped
   divisor prefix, from the owned tangent law.
4. **Criterion.** A horizon-uniform integrable bound on the *negative part* of the signed work on
   every `[a,1/2]` gives cofinal admission, hence RH.
5. **Selectivity.** (i) the tangent-norm receiver implies the signed-work criterion (so the new
   demand is formally weaker); (ii) a two-coordinate rotation has zero signed work and arbitrarily
   large tangent norm (so it is strictly weaker); (iii) `T^{2(1/2-ε)}-1` satisfies a per-horizon
   continuation bound with endpoint budget and still escapes (so horizon uniformity is the theorem).
6. **Compensation.** Complete signed three-term decomposition; affine recurrence envelope for (R);
   recovery-is-not-control countermodel.

## Log
- 2026-10-22 — created in 1-in-progress; programme initiated from astra.md.
