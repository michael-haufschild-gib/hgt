import GaloisForLFunctions.HTGeometry.HillChartC1

/-!
# Differentiating a weighted synthesis at every time

The syntheses that carry the second-order calculus are not integrals against the character alone:
a spatial derivative multiplies the character by the frequency. So the differentiation theorems are
proved here for an arbitrary multiplier dominated by a weight, and at every time — the bounds of the
two-sided energy estimate are uniform on a unit ball of times.

Both time derivatives are covered: the first, whose density is the velocity density, and the second,
whose density is the equation itself.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

open scoped RealInnerProductSpace

section Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C cmin : ℝ} {c dc : ℝ → ℝ} {G₀ χ : E → ℂ} {μ : Measure E}

/-! ## The second-derivative density at every time -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The second-derivative density at every time**, dominated by two powers of the frequency. -/
theorem norm_hillDensitySecond_le_abs (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (t : ℝ) (ξ : E) :
    ‖hillDensitySecond m c G₀ t ξ‖ ≤
      ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * (max 1 (c 0 / c t) * Real.exp (K * |t|))) * ‖G₀ ξ‖ := by
  have hval : ‖hillDensitySecond m c G₀ t ξ‖
      = |(-(massiveFreq m c ‖ξ‖ t ^ (2 : ℕ))) * hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t| *
          ‖G₀ ξ‖ := by
    rw [hillDensitySecond, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hval]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hsol := abs_hillSolution_massive_le_abs (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl t
  have hfreq : massiveFreq m c ‖ξ‖ t ^ (2 : ℕ) ≤ m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ) :=
    massiveFreq_sq_le hm hC le_rfl t
  have habs : |(-(massiveFreq m c ‖ξ‖ t ^ (2 : ℕ))) * hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t|
      = massiveFreq m c ‖ξ‖ t ^ (2 : ℕ) * |hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t| := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]
  rw [habs]
  exact mul_le_mul hfreq hsol (abs_nonneg _) (by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The second-derivative density is continuous in the frequency**, at every time. -/
theorem continuous_hillDensitySecond_all (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀) (t : ℝ) :
    Continuous (hillDensitySecond m c G₀ t) := by
  have hfibre : Continuous fun s : ℝ => hillFlow (massiveFreq m c s) (1, 0) t :=
    continuous_iff_continuousAt.mpr fun s₀ =>
      continuousAt_hillFlow_massive_all (C := C) hm hc hC (1, 0) t s₀
  have hscalar : Continuous fun s : ℝ => hillSolution (massiveFreq m c s) (1, 0) t :=
    continuous_fst.comp hfibre
  have hfreqs : Continuous fun s : ℝ => massiveFreq m c s t := by
    show Continuous fun s : ℝ => Real.sqrt (m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ))
    exact Real.continuous_sqrt.comp
      (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
  have hprod : Continuous fun ξ : E =>
      (-(massiveFreq m c ‖ξ‖ t ^ (2 : ℕ)) * hillSolution (massiveFreq m c ‖ξ‖) (1, 0) t : ℝ) :=
    (((hfreqs.comp continuous_norm).pow 2).neg).mul (hscalar.comp continuous_norm)
  exact (Complex.continuous_ofReal.comp hprod).mul hG

/-! ## The first derivative of a weighted synthesis -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **A synthesis against a weight-dominated multiplier is differentiable in time, at every
time.** -/
theorem hasDerivAt_hillSynthesis_weighted_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀) (hχ : AEStronglyMeasurable χ μ)
    {W : E → ℝ} (hWnn : ∀ ξ, 0 ≤ W ξ) (hχW : ∀ ξ, ‖χ ξ‖ ≤ W ξ)
    (hint : Integrable (fun ξ : E => W ξ * ‖G₀ ξ‖) μ)
    (hweight : Integrable (fun ξ : E => W ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)) μ) (t : ℝ) :
    HasDerivAt (hillSynthesis m c G₀ χ μ) (hillSynthesisDeriv m c G₀ χ μ t) t := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h2 := hcpos 0
    nlinarith
  have hmeas : ∀ᶠ r in nhds t,
      AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensity m c G₀ r ξ) μ := by
    filter_upwards with r
    exact hχ.mul (aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG r μ)
  have hFint : Integrable (fun ξ : E => χ ξ * hillDensity m c G₀ t ξ) μ := by
    refine Integrable.mono' (hint.const_mul (max 1 (c 0 / c t) * Real.exp (K * |t|)))
      (hχ.mul (aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG t μ)) ?_
    filter_upwards with ξ
    have hden := norm_hillDensity_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC t ξ
    calc ‖χ ξ * hillDensity m c G₀ t ξ‖ = ‖χ ξ‖ * ‖hillDensity m c G₀ t ξ‖ := norm_mul _ _
      _ ≤ W ξ * ((max 1 (c 0 / c t) * Real.exp (K * |t|)) * ‖G₀ ξ‖) :=
          mul_le_mul (hχW ξ) hden (norm_nonneg _) (hWnn ξ)
      _ = (max 1 (c 0 / c t) * Real.exp (K * |t|)) * (W ξ * ‖G₀ ξ‖) := by ring
  have hF'meas : AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensityDeriv m c G₀ t ξ) μ :=
    hχ.mul (continuous_hillDensityDeriv_all (C := C) hm hc hC hG t).aestronglyMeasurable
  have hbound : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t 1,
      ‖χ ξ * hillDensityDeriv m c G₀ r ξ‖ ≤
        Real.exp (K * (|t| + 1)) * (W ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)) := by
    filter_upwards with ξ r hr
    have habs : |r| ≤ |t| + 1 := abs_le_abs_add_one_of_dist_lt (by simpa using hr)
    have hexp : Real.exp (K * |r|) ≤ Real.exp (K * (|t| + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hK0)
    have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
    have hmf : (0 : ℝ) ≤ massiveFreq m c ‖ξ‖ 0 := le_of_lt (massiveFreq_pos hm c ‖ξ‖ 0)
    have hsum : (0 : ℝ) ≤ m + c 0 * ‖ξ‖ := le_trans hmf hfreq
    have hstep : massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |r|)
        ≤ (m + c 0 * ‖ξ‖) * Real.exp (K * (|t| + 1)) :=
      mul_le_mul hfreq hexp (le_of_lt (Real.exp_pos _)) hsum
    have hden := norm_hillDensityDeriv_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC r ξ
    calc ‖χ ξ * hillDensityDeriv m c G₀ r ξ‖ = ‖χ ξ‖ * ‖hillDensityDeriv m c G₀ r ξ‖ :=
          norm_mul _ _
      _ ≤ W ξ * ((massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |r|)) * ‖G₀ ξ‖) :=
          mul_le_mul (hχW ξ) hden (norm_nonneg _) (hWnn ξ)
      _ ≤ W ξ * (((m + c 0 * ‖ξ‖) * Real.exp (K * (|t| + 1))) * ‖G₀ ξ‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hstep (norm_nonneg _)) (hWnn ξ)
      _ = Real.exp (K * (|t| + 1)) * (W ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)) := by ring
  have hdiff : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t 1,
      HasDerivAt (fun s => χ ξ * hillDensity m c G₀ s ξ)
        (χ ξ * hillDensityDeriv m c G₀ r ξ) r := by
    filter_upwards with ξ r _
    exact hasDerivAt_hillDensity hm hc hC ξ r
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun ξ : E =>
      Real.exp (K * (|t| + 1)) * (W ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)))
    (ball_mem_nhds t one_pos) hmeas hFint hF'meas hbound
    (hweight.const_mul (Real.exp (K * (|t| + 1)))) hdiff
  exact hmain.2

/-! ## The second derivative of a weighted synthesis -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The velocity synthesis against a weight-dominated multiplier is differentiable in time, at
every time**, with derivative the synthesis of the second-derivative density. -/
theorem hasDerivAt_hillSynthesisDeriv_weighted_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    (hG : Continuous G₀) (hχ : AEStronglyMeasurable χ μ)
    {W : E → ℝ} (hWnn : ∀ ξ, 0 ≤ W ξ) (hχW : ∀ ξ, ‖χ ξ‖ ≤ W ξ)
    (hweight : Integrable (fun ξ : E => W ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)) μ)
    (hweight2 : Integrable (fun ξ : E => W ξ * ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖)) μ) (t : ℝ) :
    HasDerivAt (hillSynthesisDeriv m c G₀ χ μ) (hillSynthesisSecond m c G₀ χ μ t) t := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h2 := hcpos 0
    nlinarith
  have hmeas : ∀ᶠ r in nhds t,
      AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensityDeriv m c G₀ r ξ) μ := by
    filter_upwards with r
    exact hχ.mul (continuous_hillDensityDeriv_all (C := C) hm hc hC hG r).aestronglyMeasurable
  have hFint : Integrable (fun ξ : E => χ ξ * hillDensityDeriv m c G₀ t ξ) μ := by
    refine Integrable.mono' (hweight.const_mul (Real.exp (K * |t|)))
      (hχ.mul (continuous_hillDensityDeriv_all (C := C) hm hc hC hG t).aestronglyMeasurable) ?_
    filter_upwards with ξ
    have hden := norm_hillDensityDeriv_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC t ξ
    have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
    have hE : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
    have hstep : massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |t|)
        ≤ (m + c 0 * ‖ξ‖) * Real.exp (K * |t|) :=
      mul_le_mul_of_nonneg_right hfreq hE
    calc ‖χ ξ * hillDensityDeriv m c G₀ t ξ‖ = ‖χ ξ‖ * ‖hillDensityDeriv m c G₀ t ξ‖ :=
          norm_mul _ _
      _ ≤ W ξ * ((massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |t|)) * ‖G₀ ξ‖) :=
          mul_le_mul (hχW ξ) hden (norm_nonneg _) (hWnn ξ)
      _ ≤ W ξ * (((m + c 0 * ‖ξ‖) * Real.exp (K * |t|)) * ‖G₀ ξ‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hstep (norm_nonneg _)) (hWnn ξ)
      _ = Real.exp (K * |t|) * (W ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)) := by ring
  have hF'meas : AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensitySecond m c G₀ t ξ) μ :=
    hχ.mul (continuous_hillDensitySecond_all (C := C) hm hc hC hG t).aestronglyMeasurable
  have hbound : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t 1,
      ‖χ ξ * hillDensitySecond m c G₀ r ξ‖ ≤
        max 1 (c 0 / cmin) * Real.exp (K * (|t| + 1)) *
          (W ξ * ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖)) := by
    filter_upwards with ξ r hr
    have habs : |r| ≤ |t| + 1 := abs_le_abs_add_one_of_dist_lt (by simpa using hr)
    have hexp : Real.exp (K * |r|) ≤ Real.exp (K * (|t| + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hK0)
    have hratio : max 1 (c 0 / c r) ≤ max 1 (c 0 / cmin) :=
      max_le_max le_rfl (div_le_div_of_nonneg_left (le_of_lt (hcpos 0)) hcmin (hclow r))
    have hstep : max 1 (c 0 / c r) * Real.exp (K * |r|)
        ≤ max 1 (c 0 / cmin) * Real.exp (K * (|t| + 1)) :=
      mul_le_mul hratio hexp (le_of_lt (Real.exp_pos _)) (le_trans zero_le_one (le_max_left _ _))
    have hsq : (0 : ℝ) ≤ m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ) := by positivity
    have hden := norm_hillDensitySecond_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC r ξ
    calc ‖χ ξ * hillDensitySecond m c G₀ r ξ‖ = ‖χ ξ‖ * ‖hillDensitySecond m c G₀ r ξ‖ :=
          norm_mul _ _
      _ ≤ W ξ * (((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * (max 1 (c 0 / c r) * Real.exp (K * |r|)))
            * ‖G₀ ξ‖) := mul_le_mul (hχW ξ) hden (norm_nonneg _) (hWnn ξ)
      _ ≤ W ξ * (((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) *
            (max 1 (c 0 / cmin) * Real.exp (K * (|t| + 1)))) * ‖G₀ ξ‖) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hsq) (norm_nonneg _))
            (hWnn ξ)
      _ = max 1 (c 0 / cmin) * Real.exp (K * (|t| + 1)) *
            (W ξ * ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖)) := by ring
  have hdiff : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t 1,
      HasDerivAt (fun s => χ ξ * hillDensityDeriv m c G₀ s ξ)
        (χ ξ * hillDensitySecond m c G₀ r ξ) r := by
    filter_upwards with ξ r _
    exact hasDerivAt_hillDensityDeriv hm hc hC ξ r
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun ξ : E =>
      max 1 (c 0 / cmin) * Real.exp (K * (|t| + 1)) *
        (W ξ * ((m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖)))
    (ball_mem_nhds t one_pos) hmeas hFint hF'meas hbound
    (hweight2.const_mul (max 1 (c 0 / cmin) * Real.exp (K * (|t| + 1)))) hdiff
  exact hmain.2

/-! ## Comparing the mass weights with the frequency -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_le_kgFreq (ξ : E) : ‖ξ‖ ≤ kgFreq ξ := by
  rw [kgFreq]
  have hle : ‖ξ‖ ^ (2 : ℕ) ≤ 1 + ‖ξ‖ ^ (2 : ℕ) := by nlinarith
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg ξ)] at h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The mass weight is dominated by the frequency. -/
theorem massWeight_le_kgFreq (hm : 0 < m) (hc0 : 0 < c 0) (ξ : E) :
    m + c 0 * ‖ξ‖ ≤ (m + c 0) * kgFreq ξ := by
  have h1 : (1 : ℝ) ≤ kgFreq ξ := one_le_kgFreq ξ
  have h2 : ‖ξ‖ ≤ kgFreq ξ := norm_le_kgFreq ξ
  nlinarith [hm.le, hc0.le]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The squared mass weight is dominated by two powers of the frequency. -/
theorem massWeightSq_le_kgFreq_sq (ξ : E) :
    m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ) ≤ (m ^ (2 : ℕ) + C ^ (2 : ℕ)) * kgFreq ξ ^ (2 : ℕ) := by
  have h : kgFreq ξ ^ (2 : ℕ) = 1 + ‖ξ‖ ^ (2 : ℕ) := kgFreq_sq ξ
  rw [h]
  nlinarith [sq_nonneg m, sq_nonneg C, sq_nonneg ‖ξ‖]

end Weighted

end GaloisForLFunctions.HTGeometry
