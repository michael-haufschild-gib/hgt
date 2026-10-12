import GaloisForLFunctions.RHTower.ThetaQuantileTwoEndedSelector

/-! # The original theta mode's logarithmic admission cost

The double-exponential source cusp makes the logarithmic cost of the original
quantile pullback nonintegrable whenever its left connection coefficient is nonzero.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

namespace PaperThetaEndpoint

/-- Spectral parameters in the native two-ended selector's upper strip. -/
abbrev Point := {z : ℂ // 0 < z.im ∧ z.im < 1}

/-- The logarithmic density after the exact theta CDF change of variables. -/
def density (z : ℂ) (x : ℝ) : ℝ :=
  ‖flatMode z x‖ * Real.log (2 + ‖flatMode z x‖ / thetaSource.normalized x)

theorem density_nonneg (z : ℂ) (x : ℝ) : 0 ≤ density z x := by
  apply mul_nonneg (norm_nonneg _)
  apply Real.log_nonneg
  have := div_nonneg (norm_nonneg (flatMode z x)) (thetaSource.normalized_pos x).le
  linarith

theorem continuous_density (z : Point) : Continuous (density z) := by
  have hu := (continuous_flatMode (abs_im_lt_one_of_flat z.property.1 z.property.2)).norm
  exact hu.mul ((continuous_const.add
    (hu.div continuous_normalized_theta fun x => (thetaSource.normalized_pos x).ne')).log
      fun x => by
        change 2 + ‖flatMode z x‖ / thetaSource.normalized x ≠ 0
        have := thetaSource.normalized_pos x
        positivity)

/-- A logarithm of the actual source density still grows exponentially at the cusp. -/
theorem eventually_log_normalized_le :
    ∀ᶠ x : ℝ in atBot, Real.log (thetaSource.normalized x) ≤ -2 * Real.exp (-x) := by
  let U := thetaEnvelopeUpper / thetaSource.mass
  have hU : 0 < U := div_pos thetaEnvelopeUpper_pos thetaSource.mass_pos
  filter_upwards [eventually_le_atBot (-(max 5 (Real.log U)))] with x hx
  have ht : 5 ≤ -x := by have := le_max_left (5 : ℝ) (Real.log U); linarith
  have hlog : Real.log U ≤ -x := by have := le_max_right (5 : ℝ) (Real.log U); linarith
  have hk : thetaSource.k x ≤ thetaEnvelopeUpper * thetaEnvelope (-x) := by
    rw [← thetaSource_even x]
    exact thetaCuspFullSource_le_envelope (by linarith)
  have hρ : thetaSource.normalized x ≤ U * thetaEnvelope (-x) := by
    change thetaSource.k x / thetaSource.mass ≤ _
    calc
      _ ≤ (thetaEnvelopeUpper * thetaEnvelope (-x)) / thetaSource.mass :=
        div_le_div_of_nonneg_right hk thetaSource.mass_pos.le
      _ = _ := by dsimp [U]; ring
  have hbound := Real.log_le_log (thetaSource.normalized_pos x) hρ
  rw [thetaEnvelope, Real.log_mul hU.ne' (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp] at hbound
  have he := Real.add_one_le_exp (-x)
  have he0 := Real.exp_pos (-x)
  have he2 : Real.exp (2 * (-x)) = Real.exp (-x) ^ 2 := by
    rw [show 2 * (-x) = -x + -x by ring, Real.exp_add, sq]
  rw [he2] at hbound
  have hs : (-x + 1) ^ 2 ≤ Real.exp (-x) ^ 2 :=
    pow_le_pow_left₀ (by linarith) he 2
  nlinarith [Real.pi_gt_three, sq_nonneg (Real.exp (-x) - 1)]

/-- A nonzero Xi connection coefficient gives a quantitative left tail. -/
theorem exists_eventually_norm_lower (z : Point) (hXi : XiC z ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atBot,
      c * Real.exp (z.val.im * x) ≤ ‖flatMode z x‖ := by
  have hC : flatConnection z ≠ 0 := by
    rw [flatConnection_eq (abs_im_lt_one_of_flat z.property.1 z.property.2)]
    exact div_ne_zero hXi (by exact_mod_cast thetaSource.mass_ne_zero)
  have hz0 : z.val ≠ 0 := fun h => by
    have := z.property.1
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this
  let c := ‖z.val‖ * ‖flatConnection z‖ / 2
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hlim := tendsto_sourceChar_mul_flatMode_atBot z.property.1 z.property.2
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually
    (gt_mem_nhds hc)] with x hx
  have hn : ‖-(Complex.I * z.val) * flatConnection z‖ = 2 * c := by
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul]
    dsimp [c]; ring
  have hlow := norm_sub_norm_le (-(Complex.I * z.val) * flatConnection z)
    (sourceChar z x * flatMode z x)
  rw [norm_sub_rev, hn] at hlow
  have hl : c ≤ ‖sourceChar z x * flatMode z x‖ := by linarith
  rw [norm_mul, norm_sourceChar] at hl
  have he : Real.exp (-z.val.im * x) * Real.exp (z.val.im * x) = 1 := by
    rw [← Real.exp_add, show -z.val.im * x + z.val.im * x = 0 by ring, Real.exp_zero]
  calc
    c * Real.exp (z.val.im * x) ≤
        Real.exp (-z.val.im * x) * ‖flatMode z x‖ * Real.exp (z.val.im * x) :=
      mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
    _ = ‖flatMode z x‖ := by
      rw [mul_comm (Real.exp _) ‖_‖, mul_assoc, he, mul_one]

end PaperThetaEndpoint
end RHTower
