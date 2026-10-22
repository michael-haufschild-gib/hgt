# Completion primitive, variance--Dirichlet conservation, and positive formation action — Lean formalization

- **ID:** ULF-TAFM-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / GLOBAL SOURCE-ACTION AND PROPERNESS COORDINATE
- **Paper source:** `completion-primitive-variance-dirichlet-conservation-and-positive-formation-action-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.AnchoredCesaroVarianceCompletion`;
  `GaloisForLFunctions.RHTower.Suzuki.SuzukiCompletedFormationEnergy`
- **Status:** `[FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [BRIDGE] [NOT RH]`

## Certified generic mechanism

The generic module proves:

1. `anchoredCesaroVariance_eq_centered` and `anchoredCesaroVariance_nonneg`: anchored raw variance
   is exactly a positive sum of centered squares.
2. `anchoredCesaroVariance_add_const`: formation variance descends through the complete constant-
   gauge kernel of the scale current.
3. `anchoredCesaroVariance_succ_sub`: local variance production is exactly
   `(N+1)/(N+2) * highPass N ^ 2`.
4. `anchoredCesaroVariance_eq_scaleDirichletEnergy`: source variance equals weighted Dirichlet
   action of the formation potential.
5. `scaleCurrentPrimitive_succ_sub`: every additive correction current on the scale ray has an
   exact canonical harmonic primitive.
6. `completedScalePotential_scaled_succ_sub`: after that lift, corrected current is a pure
   weighted potential increment.
7. `completedScaleDirichletEnergy_succ_sub` and
   `completedScaleDirichletEnergy_monotoneOn`: its square is exact positive production of a
   monotone completed action.

## Certified literal mechanism

The Suzuki module proves:

1. `suzukiTransitionCoreCompletedAbelSource_succ_eq_completedFormationCurrent`: every terminal
   correction is absorbed into one completed potential; completed Abel is its pure scale current.
2. `suzukiCompletedFormationEnergy_succ_sub`: completed Abel squared is exact local production of
   the divisor-free completed formation energy.
3. `suzukiCompletedFormationEnergy_monotoneOn`: completed source action is unconditionally
   monotone.
4. `suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_formationProduction`: aligned Gamma
   energy is the exact condition-weighted production readout.
5. `suzukiScaledFormationProduction_le_alignedGamma` and
   `suzukiAlignedGamma_le_condition_mul_scaledFormationProduction`: existing transition-core
   estimates give the exact two-sided condition-number comparison.
6. `suzukiCompletedFormationEnergyIncrementEventuallyBounded_iff_alignedGamma`: eventual bounded
   production is equivalent to eventual boundedness of aligned Gamma energy.
7. `riemannHypothesis_iff_suzukiCompletedFormationEnergyIncrementEventuallyBounded`: RH is exactly
   bounded local production of one monotone, divisor-free completed source action.

## Verification

- Direct foreground elaboration passed for both modules.
- Targeted leaf builds only:
  - `GaloisForLFunctions.HTGeometry.AnchoredCesaroVarianceCompletion`: `3029/3029`
  - `GaloisForLFunctions.RHTower.Suzuki.SuzukiCompletedFormationEnergy`: `14115/14115`
    (large inherited dependency replay after concurrent cache changes)
- Umbrella wiring:
  - both modules imported by `HTGeometry.UniversalLawField`
  - literal module imported by `RHTower`
  - neither umbrella built
- Axiom audit: seventeen significant declarations report only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Exact remaining producer

ULF-TAFM-16 removes correction control as a separate algebraic obstruction. On one-dimensional
scale every terminal current is exact; after integration, positivity is source variance production
rather than a receiver-imposed square. The remaining RH-bearing obligation is now irreducible:
prove a uniform arithmetic upper bound on local production of the literal completed formation
action. Monotonicity alone is insufficient, and the formal RH equivalence is not that bound.
