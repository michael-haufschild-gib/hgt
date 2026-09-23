import GaloisForLFunctions.HTGeometry.HillFieldContinuity
import GaloisForLFunctions.HTGeometry.HillRealField

/-!
# Differentiating the synthesis at every time

The differentiation theorems were proved on an interval `0 < t < b`, because the density bounds
assumed a nonnegative time. The two-sided bounds remove that restriction: on the unit ball around any
time the dominating functions are the ones at `|t| + 1`, so the parametric-integral theorem applies
at every real time.

This is what the chart layer needs, since an event is an arbitrary point of spacetime, not one on or
after the initial slice.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

section TwoSided

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C cmin : ℝ} {c dc : ℝ → ℝ} {G₀ χ : E → ℂ} {μ : Measure E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The synthesis is differentiable in time, at every time.** -/
theorem hasDerivAt_hillSynthesis_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀) (hχ : AEStronglyMeasurable χ μ)
    (hχ1 : ∀ ξ, ‖χ ξ‖ ≤ 1)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) μ)
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) μ) (t : ℝ) :
    HasDerivAt (hillSynthesis m c G₀ χ μ) (hillSynthesisDeriv m c G₀ χ μ t) t := by
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc 0| := abs_nonneg _
    have h1 := hK 0
    have h2 := hcpos 0
    nlinarith
  have hnear : ∀ r ∈ ball t 1, |r| ≤ |t| + 1 := by
    intro r hr
    have hdist : |r - t| < 1 := by simpa [Real.dist_eq] using hr
    have hpair := abs_lt.mp hdist
    cases abs_cases r with
    | inl h => cases abs_cases t with
      | inl h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
      | inr h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
    | inr h => cases abs_cases t with
      | inl h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
      | inr h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
  have hmeas : ∀ᶠ r in nhds t,
      AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensity m c G₀ r ξ) μ := by
    filter_upwards with r
    exact hχ.mul (aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG r μ)
  have hFint : Integrable (fun ξ : E => χ ξ * hillDensity m c G₀ t ξ) μ := by
    refine Integrable.mono' (hint.const_mul (max 1 (c 0 / c t) * Real.exp (K * |t|)))
      (hχ.mul (aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG t μ)) ?_
    filter_upwards with ξ
    calc ‖χ ξ * hillDensity m c G₀ t ξ‖ ≤ 1 * ‖hillDensity m c G₀ t ξ‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hχ1 ξ) (norm_nonneg _)
      _ = ‖hillDensity m c G₀ t ξ‖ := one_mul _
      _ ≤ (max 1 (c 0 / c t) * Real.exp (K * |t|)) * ‖G₀ ξ‖ :=
          norm_hillDensity_le_abs hm hc hcd hcpos hK hC t ξ
  have hcontDeriv : ∀ r : ℝ, Continuous fun ξ : E => hillDensityDeriv m c G₀ r ξ := by
    intro r
    have hfibre : Continuous fun s : ℝ => hillFlow (massiveFreq m c s) (1, 0) r :=
      continuous_iff_continuousAt.mpr fun s₀ =>
        continuousAt_hillFlow_massive_all (C := C) hm hc hC (1, 0) r s₀
    have hscalar : Continuous fun s : ℝ => hillSolutionDeriv (massiveFreq m c s) (1, 0) r :=
      continuous_snd.comp hfibre
    exact (Complex.continuous_ofReal.comp (hscalar.comp continuous_norm)).mul hG
  have hF'meas : AEStronglyMeasurable (fun ξ : E => χ ξ * hillDensityDeriv m c G₀ t ξ) μ :=
    hχ.mul (hcontDeriv t).aestronglyMeasurable
  have hbound : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t 1,
      ‖χ ξ * hillDensityDeriv m c G₀ r ξ‖ ≤
        (m + c 0 * ‖ξ‖) * Real.exp (K * (|t| + 1)) * ‖G₀ ξ‖ := by
    filter_upwards with ξ r hr
    have hexp : Real.exp (K * |r|) ≤ Real.exp (K * (|t| + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hnear r hr) hK0)
    have hfreq := massiveFreq_zero_le (c := c) hm hcpos ξ
    have hmf : (0 : ℝ) ≤ massiveFreq m c ‖ξ‖ 0 := le_of_lt (massiveFreq_pos hm c ‖ξ‖ 0)
    have hsum : (0 : ℝ) ≤ m + c 0 * ‖ξ‖ := le_trans hmf hfreq
    have hE : (0 : ℝ) ≤ Real.exp (K * |r|) := le_of_lt (Real.exp_pos _)
    calc ‖χ ξ * hillDensityDeriv m c G₀ r ξ‖ ≤ 1 * ‖hillDensityDeriv m c G₀ r ξ‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hχ1 ξ) (norm_nonneg _)
      _ = ‖hillDensityDeriv m c G₀ r ξ‖ := one_mul _
      _ ≤ (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |r|)) * ‖G₀ ξ‖ :=
          norm_hillDensityDeriv_le_abs hm hc hcd hcpos hK hC r ξ
      _ ≤ ((m + c 0 * ‖ξ‖) * Real.exp (K * (|t| + 1))) * ‖G₀ ξ‖ := by
          have hprod : massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |r|)
              ≤ (m + c 0 * ‖ξ‖) * Real.exp (K * (|t| + 1)) := mul_le_mul hfreq hexp hE hsum
          exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = (m + c 0 * ‖ξ‖) * Real.exp (K * (|t| + 1)) * ‖G₀ ξ‖ := by ring
  have hboundInt : Integrable
      (fun ξ : E => (m + c 0 * ‖ξ‖) * Real.exp (K * (|t| + 1)) * ‖G₀ ξ‖) μ := by
    have := hweight.const_mul (Real.exp (K * (|t| + 1)))
    refine this.congr ?_
    filter_upwards with ξ
    ring
  have hdiff : ∀ᵐ ξ : E ∂μ, ∀ r ∈ ball t 1,
      HasDerivAt (fun s => χ ξ * hillDensity m c G₀ s ξ)
        (χ ξ * hillDensityDeriv m c G₀ r ξ) r := by
    filter_upwards with ξ r _
    exact hasDerivAt_hillDensity hm hc hC ξ r
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun ξ : E =>
      (m + c 0 * ‖ξ‖) * Real.exp (K * (|t| + 1)) * ‖G₀ ξ‖)
    (ball_mem_nhds t one_pos) hmeas hFint hF'meas hbound hboundInt hdiff
  exact hmain.2

/-- **The field is differentiable in time at every time.** -/
theorem hasDerivAt_hillEvolutionField_time_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) (volume : Measure E))
    (x : E) (t : ℝ) :
    HasDerivAt (fun r => hillEvolutionField m c G₀ r x)
      (hillSynthesisDeriv m c G₀ (kgChar x) (volume : Measure E) t) t := by
  have hmain := hasDerivAt_hillSynthesis_all hm hc hcd hcpos hK hC hG
    ((continuous_kgChar' x).aestronglyMeasurable) (fun ξ => le_of_eq (norm_kgChar x ξ))
    hint hweight t
  rwa [hillSynthesis_kgChar] at hmain

/-- **The real field is differentiable in time at every time.** -/
theorem hasDerivAt_hillRealField_time_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) (volume : Measure E))
    (x : E) (t : ℝ) :
    HasDerivAt (fun r => hillRealField m c G₀ r x)
      ((hillSynthesisDeriv m c G₀ (kgChar x) (volume : Measure E) t).re) t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_hillEvolutionField_time_all hm hc hcd hcpos hK hC hG hint hweight x t)

end TwoSided

end GaloisForLFunctions.HTGeometry
