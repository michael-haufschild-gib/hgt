import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicRenewalMassHasItsExactNormalization
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicCausalKernelHasItsFourierMultiplier

/-!
# Exact boundary readout by the logarithmic renewal average

The cumulative causal density is positive on every boundary interval. Dividing
causal convolution by that mass gives a positive average, whose local error
is bounded by the local error of its input. Right continuity therefore gives
a boundary limit. The exact renewal normalization converts it to multiplication
by `sqrt(log(1/x))`, with constant one.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- Every positive boundary interval contains strictly positive causal mass. -/
theorem logarithmicRenewalMass_pos {x : ℝ} (hx : 0 < x) : 0 < logarithmicRenewalMass x := by
  have hlow : x * logarithmicCausalKernel x ≤ logarithmicRenewalMass x := by
    calc
      _ = ∫ t in Ioc (0 : ℝ) x, logarithmicCausalKernel x := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hx.le, sub_zero, smul_eq_mul]
      _ ≤ ∫ t in Ioc (0 : ℝ) x, logarithmicCausalKernel t := by
        apply setIntegral_mono_on (integrableOn_const (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
          logarithmicCausalKernel_mass_one.1.integrableOn measurableSet_Ioc
        intro t ht
        exact antitoneOn_logarithmicCausalKernel ht.1 hx ht.2
  exact (mul_pos hx (logarithmicCausalKernel_pos hx)).trans_le hlow

/-- Causal convolution divided by the exact cumulative boundary mass. -/
def logarithmicBoundaryAverage (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  (∫ t in Ioc (0 : ℝ) x, (logarithmicCausalKernel t : ℂ) * h (x - t)) /
    (logarithmicRenewalMass x : ℂ)

/-- A positive causal average cannot increase the local error from the boundary value. -/
theorem norm_logarithmicBoundaryAverage_sub_le {h : ℝ → ℂ} (hm : Measurable h)
    {x C : ℝ} (hx : 0 < x)
    (hb : ∀ s ∈ Icc (0 : ℝ) x, ‖h s - h 0‖ ≤ C) :
    ‖logarithmicBoundaryAverage h x - h 0‖ ≤ C := by
  let d : ℝ → ℂ := fun t => (logarithmicCausalKernel t : ℂ) * (h (x - t) - h 0)
  have hdm : Measurable d :=
    (Complex.continuous_ofReal.measurable.comp measurable_logarithmicCausalKernel).mul
      ((hm.comp (measurable_const.sub measurable_id)).sub measurable_const)
  have hdBound (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) x) : ‖d t‖ ≤ logarithmicCausalKernel t * C := by
    have hs : x - t ∈ Icc (0 : ℝ) x := ⟨sub_nonneg.mpr ht.2, by linarith only [ht.1]⟩
    dsimp only [d]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg t)]
    exact mul_le_mul_of_nonneg_left (hb _ hs) (logarithmicCausalKernel_nonneg t)
  have hd : IntegrableOn d (Ioc (0 : ℝ) x) := by
    apply (logarithmicCausalKernel_mass_one.1.mul_const C).integrableOn.mono' hdm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hdBound t ht
  have hc : IntegrableOn (fun t : ℝ => (logarithmicCausalKernel t : ℂ) * h 0) (Ioc (0 : ℝ) x) :=
    (integrable_complex_logarithmicCausalKernel.mul_const (h 0)).integrableOn
  have hsplit : (∫ t in Ioc (0 : ℝ) x, (logarithmicCausalKernel t : ℂ) * h (x - t)) =
      (∫ t in Ioc (0 : ℝ) x, d t) + (logarithmicRenewalMass x : ℂ) * h 0 := by
    calc
      _ = ∫ t in Ioc (0 : ℝ) x, d t + (logarithmicCausalKernel t : ℂ) * h 0 := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [d]
        ring
      _ = (∫ t in Ioc (0 : ℝ) x, d t) +
          ∫ t in Ioc (0 : ℝ) x, (logarithmicCausalKernel t : ℂ) * h 0 := integral_add hd hc
      _ = _ := by rw [integral_mul_const, integral_complex_ofReal]; rfl
  have hnum : ‖∫ t in Ioc (0 : ℝ) x, d t‖ ≤ logarithmicRenewalMass x * C := by
    calc
      _ ≤ ∫ t in Ioc (0 : ℝ) x, ‖d t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc (0 : ℝ) x, logarithmicCausalKernel t * C := by
        apply integral_mono_ae hd.norm (logarithmicCausalKernel_mass_one.1.mul_const C).integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hdBound t ht
      _ = _ := integral_mul_const _ _
  have hV := logarithmicRenewalMass_pos hx
  have hVne : (logarithmicRenewalMass x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have he : logarithmicBoundaryAverage h x - h 0 =
      (∫ t in Ioc (0 : ℝ) x, d t) / (logarithmicRenewalMass x : ℂ) := by
    rw [logarithmicBoundaryAverage, hsplit]
    field_simp [hVne]
    ring
  rw [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hV.le]
  apply (div_le_iff₀ hV).mpr
  simpa only [mul_comm C] using hnum

/-- The exact positive renewal average reads the right boundary value. -/
theorem tendsto_logarithmicBoundaryAverage {h : ℝ → ℂ} (hm : Measurable h)
    (hc : ContinuousWithinAt h (Ici (0 : ℝ)) 0) :
    Tendsto (logarithmicBoundaryAverage h) (𝓝[>] (0 : ℝ)) (nhds (h 0)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousWithinAt_iff.mp hc (ε / 2) (by linarith only [hε])
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with x hx hxδ
  change (0 : ℝ) < x at hx
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (norm_logarithmicBoundaryAverage_sub_le hm hx ?_)
    (show ε / 2 < ε by linarith only [hε])
  intro s hs
  have hd : dist s (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt hxδ
  simpa only [dist_eq_norm] using (hb hs.1 hd).le

/-- The normalized causal convolution reads the boundary value with constant exactly one. -/
theorem tendsto_logarithmicCausalConvolution_normalized {h : ℝ → ℂ} (hm : Measurable h)
    (hc : ContinuousWithinAt h (Ici (0 : ℝ)) 0) :
    Tendsto (fun x : ℝ =>
      (∫ t in Ioc (0 : ℝ) x, (logarithmicCausalKernel t : ℂ) * h (x - t)) *
        (Real.sqrt (Real.log (1 / x)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds (h 0)) := by
  have hn := Complex.continuous_ofReal.tendsto (1 : ℝ) |>.comp
    tendsto_logarithmicRenewalMass_normalized
  have hl := (tendsto_logarithmicBoundaryAverage hm hc).mul hn
  simp only [Complex.ofReal_one, mul_one] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hVne : (logarithmicRenewalMass x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (logarithmicRenewalMass_pos hx).ne'
  change logarithmicBoundaryAverage h x *
    ((logarithmicRenewalMass x * Real.sqrt (Real.log (1 / x)) : ℝ) : ℂ) = _
  rw [logarithmicBoundaryAverage, Complex.ofReal_mul, ← mul_assoc, div_mul_cancel₀ _ hVne]

#print axioms logarithmicRenewalMass_pos
#print axioms tendsto_logarithmicBoundaryAverage
#print axioms tendsto_logarithmicCausalConvolution_normalized

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
