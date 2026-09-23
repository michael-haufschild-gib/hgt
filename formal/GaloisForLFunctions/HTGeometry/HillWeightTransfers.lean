import GaloisForLFunctions.HTGeometry.HillWeightedSynthesis

/-!
# One weight controls the whole second-order calculus

Every domination used by the time-dependent-speed evolution is a polynomial weight against the
initial density: the density costs nothing, the velocity density costs one power of the frequency,
the second-derivative density two. Since the frequency is at least one, all of them are controlled by
the single hypothesis that two powers of the frequency are integrable against the initial density.

This file records those transfers, and the integrability of the three densities that follows.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section Transfers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ} {μ : Measure E}

/-! ## Powers of the frequency -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- One power of the frequency dominates none. -/
theorem integrable_of_kgFreq_mul (hG : Continuous G₀)
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) μ) :
    Integrable (fun ξ : E => ‖G₀ ξ‖) μ := by
  refine Integrable.mono' h1 hG.norm.aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_kgFreq ξ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Two powers of the frequency dominate one. -/
theorem integrable_kgFreq_mul_of_sq (hG : Continuous G₀)
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) μ) :
    Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) μ := by
  refine Integrable.mono' h2 ((continuous_kgFreq.mul hG.norm).aestronglyMeasurable) ?_
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (kgFreq_pos ξ)) (norm_nonneg _))]
  have hle : kgFreq ξ ≤ kgFreq ξ ^ (2 : ℕ) := by
    have h1 := one_le_kgFreq ξ
    nlinarith [kgFreq_pos ξ]
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-! ## The mass weights -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The mass weight is dominated by one power of the frequency. -/
theorem integrable_massWeight (hm : 0 < m) (hc0 : 0 < c 0) (hG : Continuous G₀)
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) μ) :
    Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) μ := by
  refine Integrable.mono' (h1.const_mul (m + c 0))
    (((continuous_const.add (continuous_const.mul continuous_norm)).mul
      hG.norm).aestronglyMeasurable) ?_
  filter_upwards with ξ
  have hnn : (0 : ℝ) ≤ (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖ := by
    have h1 : (0 : ℝ) ≤ m + c 0 * ‖ξ‖ := by
      have := mul_nonneg (le_of_lt hc0) (norm_nonneg ξ)
      linarith [hm.le]
    exact mul_nonneg h1 (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖ ≤ ((m + c 0) * kgFreq ξ) * ‖G₀ ξ‖ :=
        mul_le_mul_of_nonneg_right (massWeight_le_kgFreq hm hc0 ξ) (norm_nonneg _)
    _ = (m + c 0) * (kgFreq ξ * ‖G₀ ξ‖) := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The frequency times the mass weight is dominated by two powers of the frequency. -/
theorem integrable_kgFreq_mul_massWeight (hm : 0 < m) (hc0 : 0 < c 0) (hG : Continuous G₀)
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) μ) :
    Integrable (fun ξ : E => kgFreq ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)) μ := by
  refine Integrable.mono' (h2.const_mul (m + c 0))
    ((continuous_kgFreq.mul
      ((continuous_const.add (continuous_const.mul continuous_norm)).mul
        hG.norm)).aestronglyMeasurable) ?_
  filter_upwards with ξ
  have hw : (0 : ℝ) ≤ m + c 0 * ‖ξ‖ := by
    have := mul_nonneg (le_of_lt hc0) (norm_nonneg ξ)
    linarith [hm.le]
  have hnn : (0 : ℝ) ≤ kgFreq ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) :=
    mul_nonneg (le_of_lt (kgFreq_pos ξ)) (mul_nonneg hw (norm_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc kgFreq ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)
      ≤ kgFreq ξ * (((m + c 0) * kgFreq ξ) * ‖G₀ ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (massWeight_le_kgFreq hm hc0 ξ) (norm_nonneg _))
          (le_of_lt (kgFreq_pos ξ))
    _ = (m + c 0) * (kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The squared mass weight is dominated by two powers of the frequency. -/
theorem integrable_massWeightSq (hG : Continuous G₀)
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) μ) :
    Integrable (fun ξ : E => (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖) μ := by
  refine Integrable.mono' (h2.const_mul (m ^ (2 : ℕ) + C ^ (2 : ℕ)))
    (((continuous_const.add (continuous_const.mul (continuous_norm.pow 2))).mul
      hG.norm).aestronglyMeasurable) ?_
  filter_upwards with ξ
  have hnn : (0 : ℝ) ≤ (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖ ≤ ((m ^ (2 : ℕ) + C ^ (2 : ℕ)) * kgFreq ξ ^ (2 : ℕ)) * ‖G₀ ξ‖ :=
        mul_le_mul_of_nonneg_right (massWeightSq_le_kgFreq_sq ξ) (norm_nonneg _)
    _ = (m ^ (2 : ℕ) + C ^ (2 : ℕ)) * (kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) := by ring

/-! ## The velocity density -/

/-- **The velocity density is integrable at every time.** -/
theorem integrable_hillDensityDeriv_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) (volume : Measure E))
    (t : ℝ) : Integrable (hillDensityDeriv m c G₀ t) (volume : Measure E) := by
  refine Integrable.mono' (hweight.const_mul (Real.exp (K * |t|)))
    (continuous_hillDensityDeriv_all (C := C) hm hc hC hG t).aestronglyMeasurable ?_
  filter_upwards with ξ
  have hden := norm_hillDensityDeriv_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC t ξ
  have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
  have hE : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
  calc ‖hillDensityDeriv m c G₀ t ξ‖
      ≤ (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |t|)) * ‖G₀ ξ‖ := hden
    _ ≤ ((m + c 0 * ‖ξ‖) * Real.exp (K * |t|)) * ‖G₀ ξ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfreq hE) (norm_nonneg _)
    _ = Real.exp (K * |t|) * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) := by ring

/-- **The velocity density carries one more power of the frequency.** -/
theorem integrable_kgFreq_mul_hillDensityDeriv_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hw : Integrable (fun ξ : E => kgFreq ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)) (volume : Measure E))
    (t : ℝ) :
    Integrable (fun ξ : E => kgFreq ξ * ‖hillDensityDeriv m c G₀ t ξ‖) (volume : Measure E) := by
  refine Integrable.mono' (hw.const_mul (Real.exp (K * |t|)))
    ((continuous_kgFreq.mul
      (continuous_hillDensityDeriv_all (C := C) hm hc hC hG t).norm).aestronglyMeasurable) ?_
  filter_upwards with ξ
  have hden := norm_hillDensityDeriv_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC t ξ
  have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
  have hE : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
  have hnn : (0 : ℝ) ≤ kgFreq ξ * ‖hillDensityDeriv m c G₀ t ξ‖ :=
    mul_nonneg (le_of_lt (kgFreq_pos ξ)) (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc kgFreq ξ * ‖hillDensityDeriv m c G₀ t ξ‖
      ≤ kgFreq ξ * ((massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |t|)) * ‖G₀ ξ‖) :=
        mul_le_mul_of_nonneg_left hden (le_of_lt (kgFreq_pos ξ))
    _ ≤ kgFreq ξ * (((m + c 0 * ‖ξ‖) * Real.exp (K * |t|)) * ‖G₀ ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfreq hE) (norm_nonneg _))
          (le_of_lt (kgFreq_pos ξ))
    _ = Real.exp (K * |t|) * (kgFreq ξ * ((m + c 0 * ‖ξ‖) * ‖G₀ ξ‖)) := by ring

/-! ## The density against two powers of the frequency -/

/-- **The density carries two powers of the frequency.** -/
theorem integrable_kgFreq_sq_mul_hillDensity_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) (volume : Measure E)) (t : ℝ) :
    Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖hillDensity m c G₀ t ξ‖) (volume : Measure E) := by
  have hmeas := aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG t (volume : Measure E)
  exact integrable_weight_mul_hillDensity_all (fun ξ => sq_nonneg _)
    (((continuous_kgFreq.pow 2).aestronglyMeasurable).mul hmeas.norm) hm hc hcd hcpos hK hC h2

/-- **The density carries one power of the frequency.** -/
theorem integrable_kgFreq_mul_hillDensity_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) (volume : Measure E)) (t : ℝ) :
    Integrable (fun ξ : E => kgFreq ξ * ‖hillDensity m c G₀ t ξ‖) (volume : Measure E) := by
  have hmeas := aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG t (volume : Measure E)
  exact integrable_weight_mul_hillDensity_all (fun ξ => le_of_lt (kgFreq_pos ξ))
    ((continuous_kgFreq.aestronglyMeasurable).mul hmeas.norm) hm hc hcd hcpos hK hC h1

end Transfers

end GaloisForLFunctions.HTGeometry
