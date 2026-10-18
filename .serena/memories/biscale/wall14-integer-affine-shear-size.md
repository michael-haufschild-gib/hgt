# Wall 14: integer affine shear coefficients survive compact corrections

2026-10-18. Formalized package; Wall 14 and broad user goal remain OPEN. This is non-RH field research. No hgtl7, numerical experiments, full builds, new axioms, commits, or edits to either field README or walls ledger.

Card: `docs/drafts/pipeline/3-formalized/wall14-integer-affine-shear-size.md`.
Sources under `formal/GaloisForLFunctions/BiScaleUncertainty/`: `IntegerAffineShear.lean`, `SummableIntegerAffineShear.lean`, `IntegerAffineShearCompactness.lean`. All declarations share namespace `GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear`. All three modules are wired once immediately after SuccessorSequenceHilbert in the umbrella.

## Concrete objects and unconditional result

State is existing SobolevShear.SequenceData ℝ (real l2(N)); Weights is actual lp (fun _ : ℕ => ℝ) 1. For d : ℕ, dilation d sends e_n to e_((d+2)n), built by orthonormal synthesis. With the existing unilateral successor isometry S, shear d = S V_d − V_d S. Its adjoint is exactly mulShift (d+2) (addShift v) − addShift (mulShift (d+2) v), connecting it to existing discrete shear.

For every a : Weights, series a is the operator-norm sum T_a = ∑ a_d C_d; norm_shear_le gives ||C_d||≤2 and norm_series_le gives ||T_a||≤2||a||1. For every n≥d+2, all infinitely many active scales still give exact readouts:
(T_a e_n)((d+2)n+1)=a_d,
(T_a e_n)((d+2)(n+1))=−a_d.

Compact K sends e_n to zero in norm, including every moving coordinate. Thus series_sub_compact_plus_tendsto and series_sub_compact_minus_tendsto recover ±a_d from T_a−K. Main classification:
- series_compact_iff: IsCompactOperator(T_a) iff a=0.
- series_sub_compact_iff: IsCompactOperator(T_a−T_b) iff a=b.
- finite_coefficient_energy_le: for every finite F and every compact K, 2 ∑(d∈F) a_d² ≤ ||T_a−K||².

The quantitative proof uses disjoint positive/negative output coordinates at n≥∑(d∈F)(d+2), finite Bessel inequality, and limits of compact-corrected readouts. New insight: summability across scales controls boundedness but does not remove infinite spatial multiplicity. This proves an injective coefficient family modulo compact operators; it does not prove an exact essential norm or a bounded-below l1 embedding, arithmetic spectral realization, or wall closure.

## Verification and scope

Three named leaves pass without diagnostics; final direct check was `lake --old env lean -j 1 GaloisForLFunctions/BiScaleUncertainty/IntegerAffineShearCompactness.lean`, exit0, empty log. All 26 public exports (11+8+7, including definitions/abbreviations) have complete #check signatures and #print axioms audits: only propext, Classical.choice, Quot.sound. No hidden abstract analytic assumptions. Formal index refreshed three changed source modules; all26 public exports recovered by paginated lexical research queries. Scoped diff check clean.

Evidence: `/tmp/bsu-wall14-manifest.json`, `/tmp/bsu-wall14-signatures-axioms.log`, `/tmp/bsu-wall14-axiom-audit.json`, `/tmp/bsu-wall14-discovery-check.json`, `/tmp/bsu-wall14-final-leaf.log`. Nine obsolete probes/failure logs archived safely under `/tmp/bsu-wall14-retired`. No owned process remains after completion.

Global lint exit1 has six unrelated unwired modules, no diagnostic for this package; see `/tmp/bsu-wall14-lint-summary.json`. Do not repair or claim ownership of concurrent workers' modules. Initial hybrid research searches were partial (deadline/stale coverage), exact lexical frontier and source checks supplemented them. No external novelty claim.

## Useful Lean details

General compact weak-null basis decay reused from non-RH HTGeometry.ObserverHorizonStability. Dilation synthesis uses Orthonormal.orthogonalFamily and OrthogonalFamily.linearIsometry_apply_single. To evaluate the infinite operator series, compose lp.evalCLM with ContinuousLinearMap.apply and use map_tsum. Use tendsto_finsetSum (not obsolete aliases). Explicit `(p := 2)` is needed in `lp.norm_single (p := 2) (by norm_num)` inside simp to avoid an unresolved exponent. For square-root decay, use exact `Real.sqrt_sq (norm_nonneg (z n))` rather than unrestricted simp, which normalizes norm squares too early.

General-lag resonances and weighted-column compactness are possible successors, not established here. Search current corpus before choosing any extension. Do not treat repeating single-scale variants as new field progress.