import GaloisForLFunctions.RHTower.LogarithmicSawtoothCorrelation
import GaloisForLFunctions.RHTower.ArithmeticClockFirstVariation

/-!
# Signed tail bounds for the logarithmic sawtooth

A continuous periodic Bernoulli primitive retains the jumps' signs.
Exponential weighting gives a tail bound at the initial clock scale,
uniformly in the terminal point.
-/

noncomputable section
open MeasureTheory Set

namespace RHTower

private def tailPrimitive (k t : ℝ) : ℝ :=
  Real.exp (-k * t) * bernoulliPeriodic (Real.exp t)

private theorem primitive_continuous (k : ℝ) : Continuous (tailPrimitive k) := by
  have hb : Continuous bernoulliPeriodic :=
    (show Continuous (fun x : ℝ => (x ^ 2 - x) / 2) by fun_prop).continuousOn.comp_fract''
      (by norm_num)
  exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-k * t))).mul
    (hb.comp Real.continuous_exp)

private theorem primitive_bound (k t : ℝ) :
    |tailPrimitive k t| ≤ Real.exp (-k * t) / 8 := by
  rw [tailPrimitive, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-k * t) * (1 / 8) :=
      mul_le_mul_of_nonneg_left (abs_bernoulliPeriodic_le _) (Real.exp_pos _).le
    _ = _ := by ring

private theorem primitive_derivative (k t : ℝ) :
    HasDerivWithinAt (tailPrimitive k)
      (Real.exp ((1 - k) * t) * logarithmicCenteredSawtooth t - k * tailPrimitive k t)
      (Ioi t) t := by
  have hb := (DeletionMixedRefinement.bernoulliPeriodic_hasDerivWithinAt_right
    (Real.exp t)).comp_of_eq t (Real.hasDerivAt_exp t).hasDerivWithinAt
      (show MapsTo Real.exp (Ioi t) (Ici (Real.exp t)) from
        fun _ ht => Real.exp_le_exp.mpr ht.le) rfl
  have he := (((hasDerivAt_id t).const_mul (-k)).exp).hasDerivWithinAt (s := Ioi t)
  convert! he.mul hb using 1
  dsimp only [tailPrimitive, logarithmicCenteredSawtooth, id_eq, Function.comp_apply]
  have hex : Real.exp ((1 - k) * t) = Real.exp (-k * t) * Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hex]
  ring

theorem abs_integral_exp_mul_logarithmicCenteredSawtooth_le
    {k a b : ℝ} (hk : 0 ≤ k) (hab : a ≤ b) :
    |∫ t in a..b, Real.exp ((1 - k) * t) * logarithmicCenteredSawtooth t| ≤
      Real.exp (-k * a) / 4 := by
  have hq := (primitive_continuous k).intervalIntegrable (μ := volume) a b
  have hw : IntervalIntegrable
      (fun t => Real.exp ((1 - k) * t) * logarithmicCenteredSawtooth t) volume a b :=
    (intervalIntegrable_logarithmicCenteredSawtooth a b).continuousOn_mul (by fun_prop)
  have hid := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (primitive_continuous k).continuousOn (fun t _ => primitive_derivative k t)
      (hw.sub (hq.const_mul k))
  rw [intervalIntegral.integral_sub hw (hq.const_mul k),
    intervalIntegral.integral_const_mul] at hid
  have henv : IntervalIntegrable (fun t : ℝ => k * Real.exp (-k * t) / 8) volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-k * t) / 8)
      (k * Real.exp (-k * t) / 8) t := by
    convert! ((((hasDerivAt_id t).const_mul (-k)).exp).neg).div_const 8 using 1
    dsimp only [id_eq]
    ring
  have hqi : |k * ∫ t in a..b, tailPrimitive k t| ≤
      Real.exp (-k * a) / 8 - Real.exp (-k * b) / 8 := by
    rw [← intervalIntegral.integral_const_mul]
    calc
      _ ≤ ∫ t in a..b, |k * tailPrimitive k t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, k * Real.exp (-k * t) / 8 := by
        apply intervalIntegral.integral_mono_on hab (hq.const_mul k).abs henv
        intro t _
        rw [abs_mul, abs_of_nonneg hk]
        calc
          _ ≤ k * (Real.exp (-k * t) / 8) :=
            mul_le_mul_of_nonneg_left (primitive_bound k t) hk
          _ = _ := by ring
      _ = _ := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) henv]
        ring
  have heq : (∫ t in a..b, Real.exp ((1 - k) * t) * logarithmicCenteredSawtooth t) =
      tailPrimitive k b - tailPrimitive k a + k * ∫ t in a..b, tailPrimitive k t := by
    linarith only [hid]
  rw [heq]
  calc
    _ ≤ |tailPrimitive k b| + |tailPrimitive k a| + |k * ∫ t in a..b, tailPrimitive k t| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ Real.exp (-k * b) / 8 + Real.exp (-k * a) / 8 +
        (Real.exp (-k * a) / 8 - Real.exp (-k * b) / 8) :=
      add_le_add (add_le_add (primitive_bound k b) (primitive_bound k a)) hqi
    _ = _ := by ring

theorem abs_integral_logarithmicCenteredSawtooth_le {a b : ℝ} (hab : a ≤ b) :
    |∫ t in a..b, logarithmicCenteredSawtooth t| ≤ Real.exp (-a) / 4 := by
  simpa only [sub_self, zero_mul, Real.exp_zero, one_mul, neg_mul, one_mul] using
    (abs_integral_exp_mul_logarithmicCenteredSawtooth_le (k := 1) zero_le_one hab)

theorem abs_integral_exp_neg_mul_logarithmicCenteredSawtooth_le
    {a b : ℝ} (hab : a ≤ b) :
    |∫ t in a..b, Real.exp (-t) * logarithmicCenteredSawtooth t| ≤
      Real.exp (-(2 * a)) / 4 := by
  simpa only [show (1 : ℝ) - 2 = -1 by ring, neg_mul, one_mul] using
    (abs_integral_exp_mul_logarithmicCenteredSawtooth_le (k := 2) (by positivity) hab)

end RHTower
