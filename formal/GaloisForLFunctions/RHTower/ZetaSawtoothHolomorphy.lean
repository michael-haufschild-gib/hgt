import GaloisForLFunctions.RHTower.ZetaTruncatedRepresentation

/-!
# Holomorphy of the sawtooth tail

`s ↦ ∫_N^∞ {u}·u^{-s-1} du` is complex-differentiable on `Re s > 0`:
differentiation under the integral with the local dominating bound
`log u·u^{-σ₁-1}` on the ball of radius `Re s₀ / 2`, the logarithm
absorbed into a smaller power by `log u ≤ u^ε/ε`.  Hence the truncated
representation of `ζ` is analytic off the pole on the right half-plane —
the continuation carrying the vertical growth bounds.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Metric

variable {N : ℕ}

/-- Measurability of the sawtooth integrand at every parameter. -/
theorem aestronglyMeasurable_sawtooth (hN : 1 ≤ N) (z : ℂ) :
    AEStronglyMeasurable
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))
      (volume.restrict (Set.Ioi (N : ℝ))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply AEStronglyMeasurable.mul
  · exact (Complex.measurable_ofReal.comp
      measurable_fract).aestronglyMeasurable
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
    have h2 : Continuous fun v : ℝ => (v, (-z - 1 : ℂ)) := by fun_prop
    exact ((Complex.continuousAt_ofReal_cpow u (-z - 1)
      (Or.inr (ne_of_gt hu0))).comp
        (f := fun v : ℝ => (v, (-z - 1 : ℂ)))
        h2.continuousAt).continuousWithinAt

set_option maxHeartbeats 1600000 in
/-- **Differentiability of the sawtooth tail** on `Re s > 0`. -/
theorem differentiableAt_zetaSawtoothTail (hN : 1 ≤ N) {s₀ : ℂ}
    (hs : 0 < s₀.re) :
    DifferentiableAt ℂ (zetaSawtoothTail N) s₀ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- the half-real-part floor on the ball
  have hball : ∀ z ∈ ball s₀ (s₀.re / 2), s₀.re / 2 ≤ z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
    have h2 : (z - s₀).re = z.re - s₀.re := by
      simp [Complex.sub_re]
    rw [h2] at h1
    have h3 := abs_le.1 h1
    linarith [h3.1]
  -- the derivative candidate and its domination
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z : ℂ => fun u : ℝ =>
      ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))
    (F' := fun z : ℂ => fun u : ℝ =>
      ((Int.fract u : ℝ) : ℂ)
        * (-(Complex.log u) * (u : ℂ) ^ (-z - 1)))
    (x₀ := s₀)
    (bound := fun u : ℝ => Real.log u * u ^ (-(s₀.re / 2) - 1))
    (μ := volume.restrict (Set.Ioi (N : ℝ)))
    (ball_mem_nhds s₀ (show (0 : ℝ) < s₀.re / 2 by positivity))
    (Eventually.of_forall fun z => aestronglyMeasurable_sawtooth hN z)
    (integrableOn_sawtooth_cpow hs hN)
    ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · -- measurability of the derivative integrand
    apply AEStronglyMeasurable.mul
    · exact (Complex.measurable_ofReal.comp
        measurable_fract).aestronglyMeasurable
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
      apply ContinuousWithinAt.mul
      · apply ContinuousWithinAt.congr
          (f := fun v : ℝ => -((Real.log v : ℝ) : ℂ))
        · apply ContinuousWithinAt.neg
          exact (Complex.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_log (ne_of_gt hu0))).continuousWithinAt
        · intro v hv
          have hv0 : (0 : ℝ) < v := lt_trans hN0 hv
          rw [Complex.ofReal_log hv0.le]
        · rw [Complex.ofReal_log hu0.le]
      · have h2 : Continuous fun v : ℝ => (v, (-s₀ - 1 : ℂ)) := by fun_prop
        exact ((Complex.continuousAt_ofReal_cpow u (-s₀ - 1)
          (Or.inr (ne_of_gt hu0))).comp
            (f := fun v : ℝ => (v, (-s₀ - 1 : ℂ)))
            h2.continuousAt).continuousWithinAt
  · -- the uniform bound on the ball
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    intro z hz
    have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
    have hu1 : (1 : ℝ) ≤ u := le_trans hNR1 (le_of_lt hu)
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hzre := hball z hz
    have h1 : ‖((Int.fract u : ℝ) : ℂ)
        * (-(Complex.log u) * (u : ℂ) ^ (-z - 1))‖
        = Int.fract u * (Real.log u * u ^ ((-z - 1).re)) := by
      rw [norm_mul, norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos hu0,
        ← Complex.ofReal_log hu0.le, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg u), abs_of_nonneg hlog0]
    rw [h1]
    have h2 : u ^ ((-z - 1).re) ≤ u ^ (-(s₀.re / 2) - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hu1
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
    have h3 : Int.fract u ≤ 1 := le_of_lt (Int.fract_lt_one u)
    have h4 : (0 : ℝ) ≤ u ^ ((-z - 1).re) := Real.rpow_nonneg hu0.le _
    have h5 : Int.fract u * (Real.log u * u ^ ((-z - 1).re))
        ≤ Real.log u * u ^ ((-z - 1).re) := by
      nlinarith [mul_nonneg hlog0 h4]
    have h6 : Real.log u * u ^ ((-z - 1).re)
        ≤ Real.log u * u ^ (-(s₀.re / 2) - 1) :=
      mul_le_mul_of_nonneg_left h2 hlog0
    linarith
  · -- integrability of the dominating bound
    have hcomp : IntegrableOn
        (fun u : ℝ => (2 / (s₀.re / 2)) * u ^ (s₀.re / 4 - (s₀.re / 2) - 1))
        (Set.Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul _
    apply Integrable.mono hcomp
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
      apply ContinuousWithinAt.mul
      · exact (Real.continuousAt_log (ne_of_gt hu0)).continuousWithinAt
      · exact (Real.continuousAt_rpow_const u _
          (Or.inl (ne_of_gt hu0))).continuousWithinAt
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with u hu
      have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
      have hu1 : (1 : ℝ) ≤ u := le_trans hNR1 (le_of_lt hu)
      have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
      have h1 : Real.log u ≤ u ^ (s₀.re / 4) / (s₀.re / 4) :=
        Real.log_le_rpow_div hu0.le (by positivity)
      have h2 : ‖Real.log u * u ^ (-(s₀.re / 2) - 1)‖
          = Real.log u * u ^ (-(s₀.re / 2) - 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hlog0 (Real.rpow_nonneg hu0.le _))]
      have h3 : ‖(2 / (s₀.re / 2)) * u ^ (s₀.re / 4 - (s₀.re / 2) - 1)‖
          = (2 / (s₀.re / 2)) * u ^ (s₀.re / 4 - (s₀.re / 2) - 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (by positivity) (Real.rpow_nonneg hu0.le _))]
      rw [h2, h3]
      have h4 : u ^ (s₀.re / 4) * u ^ (-(s₀.re / 2) - 1)
          = u ^ (s₀.re / 4 - (s₀.re / 2) - 1) := by
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      have h5 : (0 : ℝ) ≤ u ^ (-(s₀.re / 2) - 1) :=
        Real.rpow_nonneg hu0.le _
      have h6 := mul_le_mul_of_nonneg_right h1 h5
      rw [div_mul_eq_mul_div, h4] at h6
      have h7 : u ^ (s₀.re / 4 - (s₀.re / 2) - 1) / (s₀.re / 4)
          = (4 / s₀.re) * u ^ (s₀.re / 4 - (s₀.re / 2) - 1) := by
        field_simp
      rw [h7] at h6
      have h8 : (0 : ℝ) ≤ u ^ (s₀.re / 4 - (s₀.re / 2) - 1) :=
        Real.rpow_nonneg hu0.le _
      have h9 : (4 : ℝ) / s₀.re = 2 / (s₀.re / 2) := by
        field_simp
        norm_num
      linarith [h9 ▸ h6]
  · -- pointwise differentiability in the parameter
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    intro z _
    have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
    have hg : HasDerivAt (fun w : ℂ => -w - 1) (-1) z := by
      simpa using ((hasDerivAt_id z).neg.sub_const 1)
    have hpow := hg.const_cpow (c := (u : ℂ))
      (Or.inl (by exact_mod_cast ne_of_gt hu0))
    have hmul := hpow.const_mul ((Int.fract u : ℝ) : ℂ)
    convert hmul using 1
    ring

/-- The sawtooth tail is analytic on the right half-plane. -/
theorem analyticOnNhd_zetaSawtoothTail (hN : 1 ≤ N) :
    AnalyticOnNhd ℂ (zetaSawtoothTail N) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (differentiableAt_zetaSawtoothTail hN hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end RHTower
