import GaloisForLFunctions.RHTower.ThetaIntegerLogGapWidth
import GaloisForLFunctions.RHTower.CCMSmoothSupportUncertainty

/-!
# Physical mass controls the cross interaction in complete integer-log gaps

The regular screw kernel grows at most like the polar exponential beyond its
sign threshold. Cauchy--Schwarz contributes the widths of two supporting balls.
When their entire difference interval avoids all integer logarithms, the resulting
interaction per unit physical mass decreases exponentially with the separation.
This is a quantitative estimate for actual smooth CCM sources, including signed
real parts of complex sources. No positivity of the full Weil quadratic is assumed.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.RHTower

theorem abs_screwRegularKernel_le_exp_of_threshold {t : ℝ}
    (ht : screwSignThreshold < t) : |screwRegularKernel t| ≤ Real.exp (t / 2) := by
  have hp := screwSignThreshold_pos.trans ht
  rw [abs_of_pos ((screwRegularKernel_pos_iff hp).mpr ht), screwRegularKernel]
  have := div_nonneg (Real.exp_pos (-(5 * t / 2))).le
    (one_sub_exp_neg_two_mul_pos hp).le
  linarith

theorem ccmSmoothSupportMeasure_le_ball {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {c r : ℝ} (hr : 0 ≤ r)
    (hu : Function.support u ⊆ Metric.ball c r) :
    ccmSmoothSupportMeasure u ≤ 2 * r := by
  have h := ENNReal.toReal_mono (by rw [Real.volume_ball]; exact ENNReal.ofReal_ne_top)
    (measure_mono hu : volume (Function.support u) ≤ volume (Metric.ball c r))
  rw [Real.volume_ball, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)] at h
  exact h

theorem ccmSmooth_l1_product_le_ball_mass_sum {a b : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (v : CCMComplexSmoothInteriorSource b)
    {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hu : Function.support u ⊆ Metric.ball c₁ r)
    (hv : Function.support v ⊆ Metric.ball c₂ r) :
    (∫ x : ℝ, ‖u x‖) * (∫ x : ℝ, ‖v x‖) ≤ r *
      (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
        ‖ccmArchimedeanFormEmbedding b v.toCCMFormVector‖ ^ 2) := by
  have hu' := (ccmSmooth_integral_norm_sq_le_supportMeasure u).trans
    (mul_le_mul_of_nonneg_right (ccmSmoothSupportMeasure_le_ball u hr hu) (sq_nonneg _))
  have hv' := (ccmSmooth_integral_norm_sq_le_supportMeasure v).trans
    (mul_le_mul_of_nonneg_right (ccmSmoothSupportMeasure_le_ball v hr hv) (sq_nonneg _))
  nlinarith [sq_nonneg ((∫ x : ℝ, ‖u x‖) - (∫ x : ℝ, ‖v x‖))]

theorem abs_screwRegularForm_ccm_le_l1 {a b : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (v : CCMComplexSmoothInteriorSource b)
    {D : ℝ}
    (hsep : ∀ x ∈ Function.support v, ∀ y ∈ Function.support u,
      screwSignThreshold < x - y ∧ x - y ≤ D) :
    |screwRegularForm (fun x => (u x).re) (fun x => (v x).re)| ≤
      Real.exp (D / 2) * ((∫ x : ℝ, ‖u x‖) * (∫ x : ℝ, ‖v x‖)) := by
  have hui : Integrable (fun x : ℝ => ‖u x‖) := u.continuous.norm.integrable_of_hasCompactSupport
    u.hasCompactSupport.norm
  have hvi : Integrable (fun x : ℝ => ‖v x‖) := v.continuous.norm.integrable_of_hasCompactSupport
    v.hasCompactSupport.norm
  have hmajor := (hvi.mul_prod hui).const_mul (Real.exp (D / 2))
  have hpoint (p : ℝ × ℝ) :
      |screwRegularKernel (p.1 - p.2) * (u p.2).re * (v p.1).re| ≤
        Real.exp (D / 2) * (‖v p.1‖ * ‖u p.2‖) := by
    by_cases hu : u p.2 = 0
    · simp only [hu, Complex.zero_re, norm_zero, mul_zero, zero_mul, abs_zero, le_refl]
    by_cases hv : v p.1 = 0
    · simp only [hv, Complex.zero_re, norm_zero, mul_zero, zero_mul, abs_zero, le_refl]
    have hs := hsep p.1 hv p.2 hu
    have hk := (abs_screwRegularKernel_le_exp_of_threshold hs.1).trans
      (Real.exp_le_exp.mpr (show (p.1 - p.2) / 2 ≤ D / 2 by linarith [hs.2]))
    calc
      _ = |screwRegularKernel (p.1 - p.2)| * |(u p.2).re| * |(v p.1).re| := by
        rw [abs_mul, abs_mul]
      _ ≤ Real.exp (D / 2) * ‖u p.2‖ * ‖v p.1‖ := by
        gcongr <;> exact Complex.abs_re_le_norm _
      _ = _ := by ring
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      screwRegularKernel (p.1 - p.2) * (u p.2).re * (v p.1).re) := by
    have hu := u.continuous.measurable
    have hv := v.continuous.measurable
    unfold screwRegularKernel
    fun_prop
  have hi := hmajor.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hpoint p)
  calc
    _ ≤ ∫ p : ℝ × ℝ, |screwRegularKernel (p.1 - p.2) * (u p.2).re * (v p.1).re| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p : ℝ × ℝ, Real.exp (D / 2) * (‖v p.1‖ * ‖u p.2‖) :=
      integral_mono hi.abs hmajor hpoint
    _ = _ := by
      rw [integral_const_mul, Measure.volume_eq_prod,
        integral_prod_mul (fun x : ℝ => ‖v x‖) (fun x : ℝ => ‖u x‖)]
      ring

/-- A bound on actual source interaction, normalized by total physical mass. -/
theorem abs_screwRegularForm_ccm_integerLogGap_le {a b : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (v : CCMComplexSmoothInteriorSource b)
    {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hu : Function.support u ⊆ Metric.ball c₁ r)
    (hv : Function.support v ⊆ Metric.ball c₂ r)
    (hgap : screwSignThreshold ≤ c₂ - c₁ - 2 * r)
    (hfree : ∀ n : ℕ, 2 ≤ n → Real.log n ∉
      Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r)) :
    |screwRegularForm (fun x => (u x).re) (fun x => (v x).re)| ≤
      Real.exp (1 / 2) / 4 * Real.exp (-(c₂ - c₁ - 2 * r) / 2) *
        (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
          ‖ccmArchimedeanFormEmbedding b v.toCCMFormVector‖ ^ 2) := by
  have hs : ∀ x ∈ Function.support v, ∀ y ∈ Function.support u,
      screwSignThreshold < x - y ∧ x - y ≤ c₂ - c₁ + 2 * r := by
    intro x hx y hy
    have hx' := hv hx
    have hy' := hu hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have hc := integerLogFree_equalRadius_coupling_le
    (screwSignThreshold_pos.le.trans hgap) hfree
  have hm := ccmSmooth_l1_product_le_ball_mass_sum u v hr hu hv
  have h := (abs_screwRegularForm_ccm_le_l1 u v hs).trans
    (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp ((c₂ - c₁ + 2 * r) / 2) * (r *
        (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
          ‖ccmArchimedeanFormEmbedding b v.toCCMFormVector‖ ^ 2)) := h
    _ ≤ _ := by
      have hc' : Real.exp ((c₂ - c₁ + 2 * r) / 2) * r ≤
          Real.exp (1 / 2) / 4 * Real.exp (-(c₂ - c₁ - 2 * r) / 2) := by linarith only [hc]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc'
        (add_nonneg (sq_nonneg _) (sq_nonneg _))

end RHTower
