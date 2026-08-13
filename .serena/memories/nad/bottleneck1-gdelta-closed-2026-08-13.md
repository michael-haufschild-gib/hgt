# Bottleneck 1 `phase_isGδ` — PROVED, field eliminated (2026-08-13)

`HTGeometry/NevanlinnaFullRankPhaseGdelta.lean` (wired at umbrella EOF, axiom-clean):

- **`isGδ_maximalTranslationFullRankWitness`**, **`isGδ_maximalTranslationDifferentialFree`** —
  unconditional Gδ in the weak topology.  The `phase_isGδ` FIELD was deleted from
  `MaximalTranslationInputs`; `NevanlinnaBoundaryFaceMaximalTranslation` and
  `CofinalCholeskyResidualPhase` keep their capstone statements verbatim (the cofinal
  `carrierRange_maximalTranslationPhase_isGdelta` dropped its `inputs` arg).
- Proof shape worth reusing: countable patterns × compact shift exhaustion
  (`shiftExhaustion m` = ‖nodes‖ ≤ m ∧ separation ≥ 1/(m+1)) × singleton tube lemma
  (`isOpen_forall_compact_section`) × jointly-open finite certificates.  Certificate openness =
  `rectangularRankDefect_isClosed` pullback along `continuousOn_probabilityCarrierExpandedPacketValue`
  (jets = factorial·Cauchy power transforms, `probabilityCarrierExpandedPacketValue_eq_powerTransform`).
- `continuousOn_cauchyPowerTransform` : joint (measure, node) continuity of ∫(x−z)^{-m}dν on
  im z ≠ 0 — ε/3: sup-norm kernel bound `norm_cauchyPow_sub_le` (via
  `(x−z)⁻¹−(x−w)⁻¹=(z−w)(x−z)⁻¹(x−w)⁻¹` + `geom_sum₂_mul` power bound) + fixed-kernel weak
  continuity `tendsto_cauchyPowerTransform_of_tendsto` (BCF re/im mirror of the m=1 corpus proof).
- Free-phase certificate: `stackedEvaluationMatrix` over a packet tuple;
  `forall_relation_coeff_zero_iff_exists_stacked_witness` via Artinian extraction
  `exists_finset_inf_eq_bot_of_iInf_eq_bot` (wellFounded_lt on Submodule, minimal finite inf).

## MaximalTranslationInputs after this
Fields: minimalExponentialType, noCommonZero, zeroPoint(+spec), regularPoint(+spec), upperMap.
All EXCEPT minimalExponentialType discharged for `analyticNevCarrierFamily`
(`NevanlinnaCarrierDenominatorRow` + `analyticNevCarrierFamily_lowerMap`).

## Bottleneck 1 remaining
1. **M. Riesz**: `KernelMinimalExponentialType s` ⟹ `HasMinimalExponentialType F.c` (reduction
   done in `NevanlinnaEntryMinimalType.lean`).  Needs genus-zero Hadamard/Weierstrass
   factorization — NOT in mathlib; Volterra route provably insufficient (order 2).
2. Leaf/label covariance upgrade (`carrierProjector_eq_of_leaf_label_covariance`).
3. Ten per-card assemblies (produce the `MaximalTranslationInputs` term for the constructed
   family — after M. Riesz everything else is in place).

## Lean gotchas hit
`Submodule.mem_finsetInf` (not mem_finset_inf); `inv_anti₀`; `Tendsto.eventually_lt_const`;
`continuous_matrix` + `continuousOn_iff_continuous_restrict` for Matrix-valued ContinuousOn
(Matrix top. instance ≠ syntactic Pi — `rw [continuousOn_pi]` fails); `IsClosed.inter` on
`{f | P ∧ Q}` unifies into lambda-sets — split with explicit `have`s and `Set.setOf_forall`;
`norm_integral_le_of_norm_le_const` needs explicit C (conclusion has `μ.real univ` factor);
`Finset.equivFin`; nested-subtype `.1`-depth errors surface as `↑↑↑` type mismatches.
