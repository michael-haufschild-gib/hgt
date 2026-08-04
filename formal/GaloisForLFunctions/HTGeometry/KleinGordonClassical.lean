import GaloisForLFunctions.HTGeometry.KleinGordonPointwise

/-!
# The free evolution is a classical solution

Everything is now in place to differentiate the free evolution in time at a fixed point of space. The
evolution is an inverse Fourier integral, its integrand is a symbol times a density of unit modulus
times the transform of the datum, and the transform of a Schwartz function is Schwartz — so the
frequency weights `⟨ξ⟩` and `⟨ξ⟩²` that the two time derivatives cost are integrable against it.

The conclusion is the free Klein–Gordon equation for a classical solution:

`∂ₜ²u(t, x) = (2π)⁻²Δu(t, x) - u(t, x)`.
-/

namespace GaloisForLFunctions.HTGeometry

open SchwartzMap Function FourierTransform MeasureTheory

open scoped SchwartzMap Laplacian RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The density -/

/-- The frequency density of the evolution at a fixed point of space. -/
noncomputable def kgDensity (f : 𝓢(E, ℂ)) (x : E) (ξ : E) : ℂ := 𝐞 ⟪ξ, x⟫ • (𝓕 f) ξ

theorem norm_kgDensity (f : 𝓢(E, ℂ)) (x : E) (ξ : E) :
    ‖kgDensity f x ξ‖ = ‖(𝓕 f) ξ‖ := by
  rw [kgDensity, Circle.norm_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgChar (x : E) : Continuous fun ξ : E => 𝐞 ⟪ξ, x⟫ := by
  have hinner : Continuous fun ξ : E => ⟪ξ, x⟫ :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  exact Real.continuous_fourierChar.comp hinner

theorem aestronglyMeasurable_kgDensity (f : 𝓢(E, ℂ)) (x : E) :
    AEStronglyMeasurable (kgDensity f x) (volume : Measure E) :=
  ((continuous_kgChar x).smul (𝓕 f).continuous).aestronglyMeasurable

/-- **The frequency weights are integrable against the density.** -/
theorem integrable_weight_kgDensity (f : 𝓢(E, ℂ)) (x : E) (k : ℕ) :
    Integrable (fun ξ : E => kgFreq ξ ^ k * ‖kgDensity f x ξ‖) (volume : Measure E) := by
  have hgrow : Function.HasTemperateGrowth fun ξ : E => ((kgFreq ξ ^ k : ℝ) : ℂ) :=
    Complex.hasTemperateGrowth_ofReal.comp ((hasTemperateGrowth_kgFreq E).pow k)
  have hschwartz : Integrable
      (fun ξ : E => ((kgFreq ξ ^ k : ℝ) : ℂ) • (𝓕 f) ξ) (volume : Measure E) := by
    have := (smulLeftCLM ℂ (fun ξ : E => ((kgFreq ξ ^ k : ℝ) : ℂ)) (𝓕 f)).integrable
      (μ := (volume : Measure E))
    refine this.congr ?_
    filter_upwards with ξ
    exact smulLeftCLM_apply_apply hgrow (𝓕 f) ξ
  refine (hschwartz.norm).congr ?_
  filter_upwards with ξ
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (kgFreq_pos ξ).le k), norm_kgDensity]

theorem integrable_kgDensity (f : 𝓢(E, ℂ)) (x : E) :
    Integrable (kgDensity f x) (volume : Measure E) := by
  have h := integrable_weight_kgDensity f x 0
  simp only [pow_zero, one_mul] at h
  exact (integrable_norm_iff (aestronglyMeasurable_kgDensity f x)).mp h

/-! ## The evolution as a synthesis -/

/-- **The free evolution at a point is the synthesis of the cosine symbol against the density.** -/
theorem kgFree_apply_eq_synthesis (f : 𝓢(E, ℂ)) (t : ℝ) (x : E) :
    kgFree f t x = ∫ ξ : E, kgCosSymbol t ξ * kgDensity f x ξ := by
  have hcoe := congrFun (coe_kgFree (F := ℂ) f t) x
  rw [hcoe, Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [kgDensity, Circle.smul_def, smul_eq_mul]
  ring

/-- The same for the operator side. -/
theorem kgOperator_kgFree_apply_eq_synthesis (f : 𝓢(E, ℂ)) (t : ℝ) (x : E) :
    (kgFree f t - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • Δ (kgFree f t)) x
      = ∫ ξ : E, (((kgFreq ξ ^ 2 : ℝ) : ℂ) * kgCosSymbol t ξ) * kgDensity f x ξ := by
  have hcoe := congrFun (coe_kgOperator_kgFree (F := ℂ) f t) x
  rw [hcoe, Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [kgDensity, Circle.smul_def, smul_eq_mul]
  ring

/-! ## The classical equation -/

/-- **The first time derivative of the free evolution.** -/
theorem hasDerivAt_kgFree_apply (f : 𝓢(E, ℂ)) (t : ℝ) (x : E) :
    HasDerivAt (fun r : ℝ => kgFree f r x)
      (∫ ξ : E, ((-(kgFreq ξ * Real.sin (t * kgFreq ξ)) : ℝ) : ℂ) * kgDensity f x ξ) t := by
  have hsyn : (fun r : ℝ => kgFree f r x)
      = fun r : ℝ => ∫ ξ : E, kgCosSymbol r ξ * kgDensity f x ξ := by
    funext r
    exact kgFree_apply_eq_synthesis f r x
  rw [hsyn]
  have hint : Integrable (fun ξ : E => kgCosSymbol t ξ * kgDensity f x ξ)
      (volume : Measure E) := by
    refine (integrable_kgDensity f x).bdd_mul (c := 1)
      ((continuous_kgCosSymbol_freq t).aestronglyMeasurable) ?_
    filter_upwards with ξ
    exact norm_kgCosSymbol_le t ξ
  have hg : Integrable (fun ξ : E => kgFreq ξ * ‖kgDensity f x ξ‖) (volume : Measure E) := by
    have h := integrable_weight_kgDensity f x 1
    simpa using h
  exact hasDerivAt_kgSynthesis t (aestronglyMeasurable_kgDensity f x) hint hg

/-- **The free evolution solves the Klein–Gordon equation classically.** -/
theorem hasDerivAt_deriv_kgFree_apply (f : 𝓢(E, ℂ)) (t : ℝ) (x : E) :
    HasDerivAt (fun r : ℝ => deriv (fun q : ℝ => kgFree f q x) r)
      (-((kgFree f t - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • Δ (kgFree f t)) x)) t := by
  have hderiv : (fun r : ℝ => deriv (fun q : ℝ => kgFree f q x) r)
      = fun r : ℝ =>
        ∫ ξ : E, ((-(kgFreq ξ * Real.sin (r * kgFreq ξ)) : ℝ) : ℂ) * kgDensity f x ξ := by
    funext r
    exact (hasDerivAt_kgFree_apply f r x).deriv
  rw [hderiv]
  have hint : Integrable
      (fun ξ : E => ((-(kgFreq ξ * Real.sin (t * kgFreq ξ)) : ℝ) : ℂ) * kgDensity f x ξ)
      (volume : Measure E) := by
    refine Integrable.mono' (integrable_weight_kgDensity f x 1)
      (((continuous_kgSinDeriv t).aestronglyMeasurable).mul
        (aestronglyMeasurable_kgDensity f x)) ?_
    filter_upwards with ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
      abs_of_pos (kgFreq_pos ξ), pow_one]
    have hsin : |Real.sin (t * kgFreq ξ)| ≤ 1 := Real.abs_sin_le_one _
    have hnn : (0 : ℝ) ≤ ‖kgDensity f x ξ‖ := norm_nonneg _
    have h1 : kgFreq ξ * |Real.sin (t * kgFreq ξ)| ≤ kgFreq ξ := by
      nlinarith [mul_le_mul_of_nonneg_left hsin (kgFreq_pos ξ).le]
    exact mul_le_mul_of_nonneg_right h1 hnn
  have hg : Integrable (fun ξ : E => kgFreq ξ ^ 2 * ‖kgDensity f x ξ‖) (volume : Measure E) :=
    integrable_weight_kgDensity f x 2
  have hmain := hasDerivAt_deriv_kgSynthesis t (aestronglyMeasurable_kgDensity f x) hint hg
  refine hmain.congr_deriv ?_
  rw [kgOperator_kgFree_apply_eq_synthesis, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [kgCosSymbol]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
