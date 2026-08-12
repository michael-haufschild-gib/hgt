# ULF-LETCM-2 local-exponential test closure — IN PROGRESS (2026-08-12)

Card: `docs/drafts/pipeline/2-fully-proven/universal-law-field/local-exponential-test-closure-mechanics/local-exponential-complete-order-fusion-and-euler-shell-witness-escape-law.md`
Its **section 14** is the authoritative state + remaining-work list.  Read it first.

## Done
Module `HTGeometry/LocalExponentialTestClosure.lean` (wired into `HTGeometry.UniversalLawField`):
- `eventuallyEq_zero_of_iteratedDeriv_eq_zero`
- `momentStrip` (+ `_convex`, `zero_mem_`, `mul_I_mem_`, `_subset_interior`)
- `measure_eq_of_forall_moment_eq` — **local-exponential moment determinacy**, the analytic heart
  of Theorem 2.1.  Axioms clean.

## The key discovery that makes this card tractable
Mathlib already has `Mathlib/Probability/Moments/ComplexMGF.lean`:
- `ProbabilityTheory.complexMGF X μ z = ∫ ω, cexp (z * X ω) ∂μ`
- `analyticOnNhd_complexMGF` on `{z | z.re ∈ interior (integrableExpSet X μ)}`
- `iteratedDeriv_complexMGF hz n : iteratedDeriv n (complexMGF X μ) z = ∫ x, (X x)^n * cexp (z*X x) ∂μ`
- `complexMGF_id_mul_I (t : ℝ) : complexMGF id μ (↑t * I) = charFun μ t`
- `MeasureTheory.Measure.ext_of_charFun : charFun μ = charFun ν → μ = ν` (finite measures)
- `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`
- `analyticOrderAt_eq_top : analyticOrderAt f z₀ = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0`
- `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`
So the card's (LEF.3)–(LEF.5) Laplace/identity-theorem argument does NOT need to be rebuilt.

## Next step (Theorem 2.1 proper)
`ae_eq_zero_of_forall_moment_eq_zero`: `μ` finite on ℝ with
`Integrable (fun x => Real.exp (a*|x|)) μ`, `f : ℝ → ℝ` with `MemLp f 2 μ`, and
`∀ n, ∫ x^n * f x ∂μ = 0` ⟹ `f =ᵐ[μ] 0`.
Route: `ν± := μ.withDensity (ENNReal.ofReal ∘ f±)`; both finite (μ finite + `MemLp 2` ⟹ `L¹`);
moments agree; the window `(-a/2, a/2) ⊆ integrableExpSet id ν±` by Cauchy–Schwarz
`∫ e^{t x} f± dμ ≤ ‖e^{a|·|/2}‖₂ ‖f‖₂`; then `measure_eq_of_forall_moment_eq` gives `ν₊ = ν₋`,
hence `f⁺ = f⁻` a.e.
Useful mathlib: `integrable_withDensity_iff`, `integral_withDensity_eq_integral_smul`,
`MemLp.integrable_mul` (Hölder p=q=2).

## Lean traps hit here
- `ℕ∞` contradictions: `WithTop.ne_top_iff_exists` gives a `WithTop.some` coercion that does not
  norm_cast against `Nat.cast`.  Working pattern:
  `simp only [Nat.cast_add, Nat.cast_one] at hle; rw [ENat.add_one_le_iff (by simp)] at hle;
   exact lt_irrefl _ hle`.
- `integrableExpSet` lives in `ProbabilityTheory`, not `MeasureTheory`.
- The card's §11 reference to a corpus file `CompleteHankelSignCone.lean` is WRONG — no such file.
  Real nearby corpus assets: `ContinuumMatrixSpectralHankel.lean` (block-Hankel Gram of a matrix
  spectral measure, `integralFeatureGram*`), `WeightedDensityL2.lean` (weighted-L² unitary),
  `FourierKernelAdmission.lean` (finite kernel quadratic), `NonnegativeWeightMomentHankel.lean`.
