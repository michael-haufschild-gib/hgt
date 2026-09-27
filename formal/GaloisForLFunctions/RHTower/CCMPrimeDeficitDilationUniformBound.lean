import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationOscillation
import GaloisForLFunctions.RHTower.ArithmeticClockFirstVariation

/-!
# A uniform bound for the complete centered dilation source

The growing sawtooth force has a bounded primitive after its exact
periodic correction is retained. Combining that correction with the
decaying force error bounds the complete centered source by `7/2`.
The signed Möbius reconstruction has not been bounded by this argument.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitDilationSawtoothPrimitive (T : ℝ) : ℝ :=
  Real.exp (-T) * (T - 1) * bernoulliPeriodic (Real.exp T)

def ccmPrimeDeficitDilationSawtoothCorrection (T : ℝ) : ℝ :=
  Real.exp (-T) * (2 - T) * bernoulliPeriodic (Real.exp T)

private theorem bernoulli_continuous : Continuous bernoulliPeriodic :=
  (show Continuous (fun x : ℝ => (x ^ 2 - x) / 2) by fun_prop).continuousOn.comp_fract''
    (by norm_num)

private theorem oscillation_integrable (T : ℝ) :
    IntervalIntegrable ccmPrimeDeficitDilationOscillation volume 0 T := by
  have hi : IntervalIntegrable (fun t : ℝ => Int.fract (Real.exp t) - 1 / 2) volume 0 T := by
    apply (intervalIntegrable_const (c := (1 : ℝ)) (a := 0) (b := T)).mono_fun'
      ((measurable_fract.comp Real.measurable_exp).sub_const (1 / 2)).aestronglyMeasurable.restrict
    filter_upwards with t
    rw [Real.norm_eq_abs]
    change |Int.fract (Real.exp t) - 1 / 2| ≤ 1
    exact abs_le.mpr (by constructor <;> linarith [Int.fract_nonneg (Real.exp t), Int.fract_lt_one (Real.exp t)])
  exact hi.mul_continuousOn (by fun_prop)

private theorem correction_continuous : Continuous ccmPrimeDeficitDilationSawtoothCorrection :=
  ((Real.continuous_exp.comp continuous_neg).mul (continuous_const.sub continuous_id)).mul
    (bernoulli_continuous.comp Real.continuous_exp)

theorem hasDerivWithinAt_ccmPrimeDeficitDilationSawtoothPrimitive (T : ℝ) :
    HasDerivWithinAt ccmPrimeDeficitDilationSawtoothPrimitive
      (ccmPrimeDeficitDilationOscillation T + ccmPrimeDeficitDilationSawtoothCorrection T) (Ioi T) T := by
  have hb := (DeletionMixedRefinement.bernoulliPeriodic_hasDerivWithinAt_right (Real.exp T)).comp_of_eq T
    (Real.hasDerivAt_exp T).hasDerivWithinAt
    (show MapsTo Real.exp (Ioi T) (Ici (Real.exp T)) from
      fun _ ht => Real.exp_le_exp.mpr ht.le) rfl
  have he := (((hasDerivAt_id T).neg).exp).hasDerivWithinAt (s := Ioi T)
  have ht := ((hasDerivAt_id T).sub_const 1).hasDerivWithinAt (s := Ioi T)
  convert! (he.mul ht).mul hb using 1
  simp only [ccmPrimeDeficitDilationOscillation, ccmPrimeDeficitDilationSawtoothCorrection,
    Function.comp_apply, id_eq, Pi.neg_apply, Pi.mul_apply]
  have hc : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hm := congrArg (fun x : ℝ => x * ((Int.fract (Real.exp T) - 1 / 2) * (T - 1))) hc
  nlinarith only [hm]

private theorem integral_oscillation {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitDilationOscillation t) +
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitDilationSawtoothCorrection t) =
        ccmPrimeDeficitDilationSawtoothPrimitive T := by
  have hc : Continuous ccmPrimeDeficitDilationSawtoothPrimitive :=
    ((Real.continuous_exp.comp continuous_neg).mul (continuous_id.sub continuous_const)).mul
      (bernoulli_continuous.comp Real.continuous_exp)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hc.continuousOn
    (fun t _ => hasDerivWithinAt_ccmPrimeDeficitDilationSawtoothPrimitive t)
    ((oscillation_integrable T).add (correction_continuous.intervalIntegrable 0 T))
  rw [intervalIntegral.integral_add (oscillation_integrable T)
    (correction_continuous.intervalIntegrable 0 T)] at h
  simpa [ccmPrimeDeficitDilationSawtoothPrimitive, bernoulliPeriodic] using h

private theorem forceError_integrable {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable ccmPrimeDeficitDilationForceError volume 0 T :=
  (((intervalIntegrable_ccmPrimeDeficitDilationForce hT).sub
    ((Real.continuous_exp.const_mul _).intervalIntegrable 0 T)).add intervalIntegrable_const).sub
      (oscillation_integrable T)

theorem intervalIntegrable_ccmPrimeDeficitDilationErrorCorrection {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => ccmPrimeDeficitDilationForceError t -
      ccmPrimeDeficitDilationSawtoothCorrection t) volume 0 T :=
  (forceError_integrable hT).sub (correction_continuous.intervalIntegrable 0 T)

/-- The full centered remainder is a small terminal periodic value plus
an absolutely controlled error integral. -/
theorem ccmPrimeDeficitDilationRemainder_eq_periodic_correction {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitDilationRemainder T = ccmPrimeDeficitDilationSawtoothPrimitive T +
      ∫ t in (0 : ℝ)..T, ccmPrimeDeficitDilationForceError t -
        ccmPrimeDeficitDilationSawtoothCorrection t := by
  have hs : ccmPrimeDeficitDilationRemainder T =
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitDilationOscillation t) +
        ∫ t in (0 : ℝ)..T, ccmPrimeDeficitDilationForceError t := by
    rw [ccmPrimeDeficitDilationRemainder_eq_integral hT,
      ← intervalIntegral.integral_add (oscillation_integrable T) (forceError_integrable hT)]
    apply intervalIntegral.integral_congr
    intro t _
    unfold ccmPrimeDeficitDilationForceError
    ring
  rw [intervalIntegral.integral_sub (forceError_integrable hT)
    (correction_continuous.intervalIntegrable 0 T)]
  linarith only [hs, integral_oscillation hT]

theorem abs_ccmPrimeDeficitDilationSawtoothPrimitive_le_decay {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationSawtoothPrimitive T| ≤ Real.exp (-T) * (T + 1) / 8 := by
  have ht : |T - 1| ≤ T + 1 := abs_le.mpr (by constructor <;> linarith only [hT])
  rw [ccmPrimeDeficitDilationSawtoothPrimitive, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-T))]
  calc
    _ ≤ (Real.exp (-T) * (T + 1)) * (1 / 8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht (Real.exp_pos (-T)).le)
        (abs_bernoulliPeriodic_le _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem abs_ccmPrimeDeficitDilationSawtoothPrimitive_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationSawtoothPrimitive T| ≤ 1 / 8 := by
  have he : Real.exp (-T) * (T + 1) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp T) (Real.exp_pos (-T)).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  exact (abs_ccmPrimeDeficitDilationSawtoothPrimitive_le_decay hT).trans (by linarith only [he])

private theorem correction_bound {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationSawtoothCorrection T| ≤ Real.exp (-T) * (T + 2) / 8 := by
  have ht : |2 - T| ≤ T + 2 := abs_le.mpr (by constructor <;> linarith only [hT])
  rw [ccmPrimeDeficitDilationSawtoothCorrection, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-T))]
  calc
    _ ≤ (Real.exp (-T) * (T + 2)) * (1 / 8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht (Real.exp_pos (-T)).le)
        (abs_bernoulliPeriodic_le _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem abs_ccmPrimeDeficitDilationErrorCorrection_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationForceError T - ccmPrimeDeficitDilationSawtoothCorrection T| ≤
      Real.exp (-T) * (T + 26) / 8 := by
  have h := (abs_sub (ccmPrimeDeficitDilationForceError T)
    (ccmPrimeDeficitDilationSawtoothCorrection T)).trans
      (add_le_add (abs_ccmPrimeDeficitDilationForceError_le hT) (correction_bound hT))
  linarith only [h]

/-- Uniform unconditional control of the entire centered dilation source.
No bound for the signed Möbius inverse is used or inferred. -/
theorem abs_ccmPrimeDeficitDilationRemainder_le_uniform {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationRemainder T| ≤ 7 / 2 := by
  let f : ℝ → ℝ := fun t => ccmPrimeDeficitDilationForceError t - ccmPrimeDeficitDilationSawtoothCorrection t
  let b : ℝ → ℝ := fun t => Real.exp (-t) * (t + 26) / 8
  have hi : IntervalIntegrable f volume 0 T :=
    intervalIntegrable_ccmPrimeDeficitDilationErrorCorrection hT
  have hia : IntervalIntegrable (fun t => |f t|) volume 0 T := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hb : IntervalIntegrable b volume 0 T := by
    apply Continuous.intervalIntegrable
    dsimp only [b]
    fun_prop
  have hp (t : ℝ) (ht : 0 ≤ t) : |f t| ≤ b t := by
    exact abs_ccmPrimeDeficitDilationErrorCorrection_le ht
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -(Real.exp (-t) * (t + 27) / 8)) (b t) t := by
    convert! (((((hasDerivAt_id t).neg).exp).mul ((hasDerivAt_id t).add_const 27)).div_const 8).neg using 1
    simp only [b, id_eq, Pi.neg_apply]
    ring
  have hbi : (∫ t in (0 : ℝ)..T, b t) ≤ 27 / 8 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hb]
    simp only [neg_zero, Real.exp_zero, zero_add, one_mul]
    have hh : 0 ≤ Real.exp (-T) * (T + 27) / 8 := by positivity
    linarith only [hh]
  have hfi : |∫ t in (0 : ℝ)..T, f t| ≤ 27 / 8 :=
    (intervalIntegral.abs_integral_le_integral_abs hT).trans
      ((intervalIntegral.integral_mono_on hT hia hb (fun t ht => hp t ht.1)).trans hbi)
  rw [ccmPrimeDeficitDilationRemainder_eq_periodic_correction hT]
  have h := (abs_add_le (ccmPrimeDeficitDilationSawtoothPrimitive T)
    (∫ t in (0 : ℝ)..T, f t)).trans
      (add_le_add (abs_ccmPrimeDeficitDilationSawtoothPrimitive_le hT) hfi)
  exact h.trans_eq (by ring)

/-- Uniform cancellation in the full signed dilation aggregate of the
original deficit, with both explicit main terms retained. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_dilation_centered_le {T : ℝ} (hT : 0 ≤ T) :
    |(∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        ccmLogChebyshevDeficitPrimitive (T - Real.log n)) -
      (Real.eulerMascheroniConstant + 1) * (Real.exp T - 1) +
        Real.log (2 * Real.pi) / 2 * T| ≤ 7 / 2 := by
  rw [ccmLogChebyshevDeficitPrimitive_dilation_conservation]
  exact abs_ccmPrimeDeficitDilationRemainder_le_uniform hT

end RHTower
