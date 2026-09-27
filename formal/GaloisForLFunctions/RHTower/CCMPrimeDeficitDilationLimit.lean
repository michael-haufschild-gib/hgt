import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationUniformBound
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exponential settling of the complete centered dilation source

The limiting constant is the integral of the actual corrected force.
The full remainder differs from this constant by at most
`exp (-T) * (T + 14) / 4`. Both the periodic endpoint and the infinite
tail of the corrected force are retained in the identity.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

def ccmPrimeDeficitDilationLimit : ℝ :=
  ∫ t in Ioi (0 : ℝ), ccmPrimeDeficitDilationForceError t -
    ccmPrimeDeficitDilationSawtoothCorrection t

private def errorCorrection (t : ℝ) : ℝ :=
  ccmPrimeDeficitDilationForceError t - ccmPrimeDeficitDilationSawtoothCorrection t

private def envelope (t : ℝ) : ℝ := Real.exp (-t) * (t + 26) / 8

private theorem envelope_derivative (t : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.exp (-t) * (t + 27) / 8)) (envelope t) t := by
  convert! (((((hasDerivAt_id t).neg).exp).mul ((hasDerivAt_id t).add_const 27)).div_const 8).neg using 1
  simp only [envelope, id_eq, Pi.neg_apply]
  ring

private theorem affine_exp_tendsto (c : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-t) * (t + c)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).mul_const c)
  simpa only [pow_one, pow_zero, one_mul, zero_mul, mul_zero, zero_add,
    mul_add, add_mul, mul_comm] using h

private theorem envelope_primitive_tendsto :
    Tendsto (fun t : ℝ => -(Real.exp (-t) * (t + 27) / 8)) atTop (𝓝 0) := by
  simpa only [zero_div, neg_zero] using ((affine_exp_tendsto 27).div_const 8).neg

private theorem envelope_integrable {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn envelope (Ioi T) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t _ => envelope_derivative t)
    (fun t ht => by dsimp only [envelope]; have : 0 ≤ t := hT.trans ht.le; positivity)
    envelope_primitive_tendsto

private theorem envelope_integral {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Ioi T, envelope t) = Real.exp (-T) * (T + 27) / 8 := by
  simpa only [zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => envelope_derivative t)
      (fun t ht => by dsimp only [envelope]; have : 0 ≤ t := hT.trans ht.le; positivity)
      envelope_primitive_tendsto

theorem integrableOn_ccmPrimeDeficitDilationErrorCorrection :
    IntegrableOn (fun t => ccmPrimeDeficitDilationForceError t -
      ccmPrimeDeficitDilationSawtoothCorrection t) (Ioi (0 : ℝ)) := by
  change IntegrableOn errorCorrection (Ioi (0 : ℝ))
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (27 / 8) 0
    (b := fun b : ℝ => b) (l := atTop) ?_ tendsto_id ?_
  · intro b
    exact (intervalIntegrable_ccmPrimeDeficitDilationErrorCorrection (le_max_left 0 b)).1.mono_set
      (fun t ht => ⟨ht.1, ht.2.trans (le_max_right 0 b)⟩)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    have hi := intervalIntegrable_ccmPrimeDeficitDilationErrorCorrection hb
    have he : IntervalIntegrable envelope volume 0 b := by
      exact (show Continuous envelope by unfold envelope; fun_prop).intervalIntegrable 0 b
    calc
      _ ≤ ∫ t in (0 : ℝ)..b, envelope t :=
        intervalIntegral.integral_mono_on hb hi.norm he (fun t ht => by
          simpa only [Real.norm_eq_abs, envelope] using abs_ccmPrimeDeficitDilationErrorCorrection_le ht.1)
      _ = 27 / 8 - Real.exp (-b) * (b + 27) / 8 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => envelope_derivative t) he]
        simp only [neg_zero, Real.exp_zero, zero_add, one_mul]
        ring
      _ ≤ _ := by
        have : 0 ≤ Real.exp (-b) * (b + 27) / 8 := by positivity
        linarith only [this]

/-- Exact limiting-constant subtraction, including the terminal periodic
term and the complete infinite corrected-force tail. -/
theorem ccmPrimeDeficitDilationRemainder_sub_limit {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitDilationRemainder T - ccmPrimeDeficitDilationLimit =
      ccmPrimeDeficitDilationSawtoothPrimitive T -
        ∫ t in Ioi T, ccmPrimeDeficitDilationForceError t -
          ccmPrimeDeficitDilationSawtoothCorrection t := by
  have hi := integrableOn_ccmPrimeDeficitDilationErrorCorrection
  have hs := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hT))
  rw [ccmPrimeDeficitDilationRemainder_eq_periodic_correction hT, ccmPrimeDeficitDilationLimit]
  linarith only [hs]

/-- The complete centered source settles exponentially, without any
estimate on a Möbius partial sum or prime deficit as a premise. -/
theorem abs_ccmPrimeDeficitDilationRemainder_sub_limit_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationRemainder T - ccmPrimeDeficitDilationLimit| ≤
      Real.exp (-T) * (T + 14) / 4 := by
  have hi : |∫ t in Ioi T, errorCorrection t| ≤ Real.exp (-T) * (T + 27) / 8 := by
    have h := norm_integral_le_of_norm_le (f := errorCorrection) (envelope_integrable hT) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [Real.norm_eq_abs, errorCorrection, envelope] using
        abs_ccmPrimeDeficitDilationErrorCorrection_le (hT.trans ht.le))
    rw [Real.norm_eq_abs, envelope_integral hT] at h
    exact h
  rw [ccmPrimeDeficitDilationRemainder_sub_limit hT]
  have h := (abs_sub _ _).trans
    (add_le_add (abs_ccmPrimeDeficitDilationSawtoothPrimitive_le_decay hT) hi)
  exact h.trans_eq (by ring)

theorem tendsto_ccmPrimeDeficitDilationRemainder :
    Tendsto ccmPrimeDeficitDilationRemainder atTop (𝓝 ccmPrimeDeficitDilationLimit) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ T : ℝ in atTop, ‖ccmPrimeDeficitDilationRemainder T - ccmPrimeDeficitDilationLimit‖ ≤
      Real.exp (-T) * (T + 14) / 4 from ?_)
  · simpa only [zero_div] using (affine_exp_tendsto 14).div_const 4
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs] using abs_ccmPrimeDeficitDilationRemainder_sub_limit_le hT

end RHTower
