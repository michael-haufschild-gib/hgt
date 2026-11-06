# Review-0611 §2.1 effectivization and assembly tasks (A9–A14)

- **ID:** review-0611-effectivization
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md), "Effectivization and assembly"
- **Statement:** Each task A9–A14 gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A13 Γ-limit lower bound | done | `ArithmeticHodgeTheoryOfDegenerations/TheCriticalFormHasAGammaLiminf.lean`: `eventually_lt_weilQuad_of_L1_limit_full`, liminf `Q(U_N) ≥ Q_T(F) + α_R ∫_{y<0} F²e^{−8y}` for every `T ≥ e^{G₀}`, along every `L¹` limit with `‖U_N‖₂ ≤ 1` and bounded eighth mass; `tendsto_integral_sq_sub_of_bounded_weilQuad`, bounded form upgrades the limit to `L²`. Inputs `CriticalArithmeticCorrelationTheory/{ThePrimeAndPoleFormsAreContinuousInTheWeightedNorm,BoundedWeilEnergyUpgradesL1LimitsToStrongLimits}.lean` |
| A14 star horizons, gcd strata, Künneth jets | primitive horizon in compile | Star horizon `HodgeTheoryWithoutVarieties/TheDepthLawIsEffective.lean`. Primitive horizon `HodgeTheoryWithoutVarieties/ThePrimitiveDepthLawIsEffective.lean`, on `RenormalizedArithmeticPotentialTheory/TheTensorizationConstantIsExplicit.lean`. Gcd strata: exact identity `completeWeilEnergy_gcd_stratification`. Künneth jets: equivalence `ArithmeticHarmonicAnalysis/SameOrderJetRecoveryIsHomogeneousLogIndependence` |
| A10 explicit `R₀` | not started | Plan: explicit `C_arch` (`C_comm`, bump slope `L_B`, sup bounds of the spline), then far complement on `0 < R < R₀` by copying `exists_critical_multiple_weighted_far_complement` with the ratio kept |
| A11 literal channels | upward channel done | `ReceivingCharges/LiteralChannelScaleDomination.lean`, uniform in period and offset count on `ceMQ⁵⌈log N⌉ ≤ N`. Joint bound with center, cross and overlap channels not started; overlap channel has a conductor-subspace bound only, so it covers even periodic `G` |
| A12 mixed Schur debit | fixed blocks done | `CompletedArithmeticForms/ThePrefixSchurCostIsThePrefixResidual.lean`: `S(tail z) = zᵀWz − rᵀA⁻¹r`, floor on fixed conductor blocks. Growing blocks not started. Full tail is the same statement as positivity of `W` (`eventually_completeWeil_posSemidef_iff_prefixSchur`), so for the plateau it is known only for `c` up to the certified boundary |
| A9 explicit `K₀` | not started | `K₁ = min(K_far, g/(64(C+1)), K_low)`; `K_low` needs `K_bi`, `K_d7` of the log-free conductor residuals. Chain of thousands of lines; not yet estimated |

## Rule

Explicit means a closed expression. A theorem `∃ C, RHVerifiedThrough (C …) → X` with `X` implied by RH is classically
trivial, so heights carry explicit values.
