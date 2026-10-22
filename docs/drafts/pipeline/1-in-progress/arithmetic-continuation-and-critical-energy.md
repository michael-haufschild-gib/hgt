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

## Lean assets (programme folder `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy`)
- `CriticalEnergyFamilies` — `Admits`, `CofinallyAdmits`, `UniformlyAdmitsOn`.
- `BackwardContinuationCalculus` — `scaledEnergy_add_budget_le` (master monotonicity),
  `one_add_le_mul_exp_of_linear_work` (Grönwall), `bddAbove_of_tendsto_atTop` (coercive recovery),
  `monotoneOn_of_hasDerivAt_nonneg_Ici`.
- `ContinuationTransportsAdmission` — `LinearContinuation`, `OsgoodContinuation`,
  `Admits.of_linearContinuation`, `Admits.of_osgoodContinuation`,
  `cofinallyAdmits_of_linearContinuation`, `cofinallyAdmits_of_osgoodContinuation`.
- `HorizonUniformityIsTheTheorem` — `escapeEnergy`, `hasDerivAt_escapeEnergy`,
  `not_admits_escapeEnergy`, `not_linearContinuation_escapeEnergy`.
- `AffineRecurrenceEnvelope` — `affineEnvelope`, `le_affineEnvelope`, `affineEnvelope_eq`,
  `affineEnvelope_le_of_contraction`, `affineEnvelope_one_one`.
- `GroundFloorNoCrossing` — `floor_le_of_relative_decay`, `floor_le_of_relative_decay_Ico`.
- `TheDampedMobiusCriticalEnergy` — `dampedMobiusEnergy`, `mem_receiverDampings_iff_admits`,
  `riemannHypothesis_iff_cofinallyAdmits`.
- `SignedDampingWorkOfTheMobiusEnergy` — `signedDampingWork`, `hasDerivAt_dampedMobiusEnergy`
  (`∂_ε E_T = 2W_T`), `two_mul_signedDampingWork_eq_markov` (bridge to the owned Markov flux form),
  `neg_two_mul_signedDampingWork_le_of_tangentNorm_le`.
- `TheDampingContinuationCriterion` — `riemannHypothesis_of_dampingContinuation_endpoint`,
  `riemannHypothesis_of_dampingContinuation_above_half_abscissa`,
  `zetaZeroAbscissa_le_half_add_of_partial_dampingContinuation`,
  `dampingContinuation_of_tangentNorm_le`,
  `arithmeticDampingTotalJumpEnergy_le_of_continuation_bound`.
- `TheSignedWorkDemandIsStrictlyWeaker` — `exists_vanishing_signed_work_with_large_tangent`.
- `SuperlinearOsgoodScale` — `riemannHypothesis_of_superlinear_dampingContinuation`.
- `CompensationNeedsItsCrossTerms` — `pronicNorm_add_sq`, `exists_sector_count_complete_energy_gt`,
  `exists_ratio_tendsto_zero_and_complete_unbounded`.

Foundational README: `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md`
(shared-target section synchronised across the now eight programme READMEs; new programme added to
the shared section as the continuation layer with mechanism 6).

## Log
- 2026-10-22 — programme folder, umbrella `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy`
  wired into `MainTheorems`, foundational README written.
