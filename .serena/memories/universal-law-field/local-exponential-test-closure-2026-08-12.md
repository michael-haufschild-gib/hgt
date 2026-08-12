# ULF-LETCM-2 local-exponential test closure — IN PROGRESS (2026-08-12)

Card: `docs/drafts/pipeline/2-fully-proven/universal-law-field/local-exponential-test-closure-mechanics/local-exponential-complete-order-fusion-and-euler-shell-witness-escape-law.md`
Its **section 14** is the authoritative state + remaining-work list.  Read it first.

## Done (all axiom-clean, umbrella build 11,859 jobs)

`HTGeometry/LocalExponentialTestClosure.lean`
- determinacy: `eventuallyEq_zero_of_iteratedDeriv_eq_zero`, `momentStrip`(+lemmas),
  `measure_eq_of_forall_moment_eq`, `measure_eq_of_forall_real_moment_eq`
- window: `pow_div_factorial_le_exp`, `abs_pow_le_const_mul_exp`, `memLp_two_exp_half`,
  `memLp_two_pow`, `memLp_two_complex_pow`, `integrable_mul_of_le_exp_half`   ((LEF.3))
- **Theorem 2.1**: `posWeight`/`negWeight`(+`coe_*`), `lintegral_toNNReal_ne_top`,
  `memLp_two_coe_weight`, `window_subset_integrableExpSet`,
  `ae_eq_zero_of_forall_moment_eq_zero`, `ae_eq_zero_of_forall_complex_moment_eq_zero`
- **density**: `monomialLp`, `coeFn_monomialLp`, `polySubmodule`, `monomialLp_mem`,
  `polySubmodule_orthogonal`, `exists_polynomial_of_mem_polySubmodule` (span elements are
  a.e. `fun x => Polynomial.eval (x:ℂ) P`), `dense_polySubmodule`

`HTGeometry/LocalExponentialMatrixSignCone.lean`  (NEW)
- `matrixMoment` (LEF.7), `blockHankel` (LEF.8), `vectorPoly`, `matQuad`, `multiplierForm`
  (LEF.11).  Moments are ENTRYWISE — no matrix-valued Bochner integration.
- `integrable_abs_pow`, `integrable_pow_mul_entry`
- **`matQuad_blockHankel_eq_multiplierForm`** = (LEF.9)
- `matQuad_eq_dotProduct` (bridge to `star v ⬝ᵥ M *ᵥ v`)
- `integrable_matQuad_vectorPoly`, **`re_matQuad_blockHankel_nonneg`** = Thm 3.1 forward
- rank-one layer: `conj_mul_self`, `matQuad_smul_vector`, `vectorPoly_rankOne`,
  **`integral_normSq_poly_mul_matQuad_nonneg`** — block-Hankel positivity forces
  `∫ ‖eval x P‖² * (u* J x u).re dμ ≥ 0` for every `P` and every direction `u`.

## Next (card §14 items 3c, 3d, then 4–7)
3c. Scalar endgame: bounded real `g` with `∫ ‖eval x P‖² g dμ ≥ 0` ∀P ⟹ `0 ≤ᵐ g`.
    Route: `λ := μ.withDensity (ENNReal.ofReal |g|)` is finite and inherits the exponential
    window (g bounded); `∫ h g dμ = ∫ h·sign g dλ` via `integral_withDensity_eq_integral_smul₀`;
    apply `dense_polySubmodule` + `exists_polynomial_of_mem_polySubmodule` for λ; test against
    `1_{g<0}`; the convergence `∫|q_k|² s dλ → ∫|1_E|² s dλ` follows from
    `‖|q|²-|f|²‖₁ ≤ ‖q-f‖₂(‖q‖₂+‖f‖₂)`.
3d. Assemble Thm 3.1 converse: apply 3c to `g_u = (matQuad (J x) u).re` for `u` in a countable
    dense set, intersect, extend by continuity in `u`.  Cor 3.2 = contrapositive.
4–7. Rational-phase density/fusion (LEF.15), gauge conservation (LEF.18/19), Euler-shell
    specialization (LEF.20–22), no-uniform-depth (LEF.23–25).

## Mathlib entry points
ComplexMGF: `complexMGF`, `analyticOnNhd_complexMGF`, `iteratedDeriv_complexMGF`,
`complexMGF_id_mul_I`; `Measure.ext_of_charFun`;
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`; `analyticOrderAt_eq_top`;
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`.
Measure/Lp: `integral_withDensity_eq_integral_smul₀`,
`integrable_withDensity_iff_integrable_smul₀`, `isFiniteMeasure_withDensity`,
`withDensity_eq_iff`, `lintegral_ofReal_le_lintegral_enorm`, `AEMeasurable.real_toNNReal`,
`memLp_two_iff_integrable_sq`, `MemLp.of_le`, `MemLp.integrable_mul`, `MemLp.toLp`,
`MemLp.coeFn_toLp`, `Lp.memLp`, `Lp.eq_zero_iff_ae_eq_zero`, `Lp.coeFn_add/_smul/_zero`,
`L2.inner_def`, `RCLike.inner_apply` (`inner 𝕜 x y = y * conj x`), `Submodule.mem_orthogonal`,
`Submodule.topologicalClosure_eq_top_iff`, `Submodule.dense_iff_topologicalClosure_eq_top`,
`Submodule.span_induction`, `Polynomial.eval_eq_sum_range'`, `Fin.sum_univ_eq_sum_range`,
`integral_finsetSum`/`integrable_finsetSum` (the `_finset_` spellings are deprecated),
`integral_re`/`integral_im` (+ `RCLike.re_to_complex`), `Matrix.PosSemidef.re_dotProduct_nonneg`.

## Lean traps hit
- `ℕ∞`: `simp only [Nat.cast_add, Nat.cast_one] at h; rw [ENat.add_one_le_iff (by simp)] at h;
  exact lt_irrefl _ h`.
- `integrableExpSet` is in `ProbabilityTheory`.
- `Matrix.PosSemidef` on ℂ needs `open scoped ComplexOrder`; `⬝ᵥ`/`*ᵥ` need `open scoped Matrix`
  (and `star v ⬝ᵥ (M *ᵥ v)` needs the parentheses).  `dotProduct` is root, not `Matrix.dotProduct`.
- `noncomputable def`s have no `rw` equation lemmas — use `simp only [theDef]`.
- `omit [inst] in` must come BEFORE the docstring, not between docstring and theorem.
- The lint gate fails on warnings; unused simp args must be removed (use `-lemma` when the point
  is to remove it from the simp set).
- The card's §11 claim that the corpus has `CompleteHankelSignCone.lean` is WRONG.
