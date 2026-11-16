import GaloisForLFunctions.RHTower.MobiusCriticalFisherSteinContact

/-!
# Factorial remainder law for the critical exponential resolvent

The existing critical Möbius density is exponential. Its Stieltjes
resolvent has the Euler factorial expansion. Positive moment remainders
give an exact recurrence, alternating truncations, and a factorial error
bound at every order and every positive coupling `exp t`.
-/

open MeasureTheory Set
open scoped BigOperators
open RHTower
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section

/-- Resolvent-weighted moments of the critical exponential density. -/
def criticalResolventMoment (t : ℝ) (N : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ N * mobiusCriticalExponentialDensity x / (1 + Real.exp t * x)

private theorem integrable_resolventMoment (t : ℝ) (N : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ N * mobiusCriticalExponentialDensity x /
      (1 + Real.exp t * x)) (Ioi 0) := by
  have hc : ContinuousOn (fun x : ℝ => x ^ N * mobiusCriticalExponentialDensity x /
      (1 + Real.exp t * x)) (Ioi 0) := by
    apply ContinuousOn.div
    · unfold mobiusCriticalExponentialDensity
      fun_prop
    · fun_prop
    · intro x hx
      have hx0 : 0 < x := hx
      have hpos : 0 < 1 + Real.exp t * x := by positivity
      exact hpos.ne'
  apply (integrableOn_pow_mul_mobiusCriticalExponentialDensity N).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have hn : 0 ≤ x ^ N * mobiusCriticalExponentialDensity x := by
    unfold mobiusCriticalExponentialDensity
    positivity
  have hd : 1 ≤ 1 + Real.exp t * x := by
    have := mul_nonneg (Real.exp_pos t).le hx.le
    linarith only [this]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (by linarith only [hd]))]
  exact div_le_self hn hd

/-- Resolvent damping places each positive moment between zero and its factorial moment. -/
theorem criticalResolventMoment_bounds (t : ℝ) (N : ℕ) :
    0 ≤ criticalResolventMoment t N ∧ criticalResolventMoment t N ≤ (N.factorial : ℝ) := by
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    unfold mobiusCriticalExponentialDensity
    positivity
  · calc
      _ ≤ ∫ x in Ioi (0 : ℝ), x ^ N * mobiusCriticalExponentialDensity x := by
        apply integral_mono_ae (integrable_resolventMoment t N)
          (integrableOn_pow_mul_mobiusCriticalExponentialDensity N)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := hx
        apply div_le_self
        · unfold mobiusCriticalExponentialDensity
          positivity
        · have := mul_nonneg (Real.exp_pos t).le hx.le
          linarith only [this]
      _ = _ := integral_Ioi_pow_mul_mobiusCriticalExponentialDensity N

/-- The denominator gives an exact adjacent-moment recurrence. -/
theorem criticalResolventMoment_recurrence (t : ℝ) (N : ℕ) :
    criticalResolventMoment t N + Real.exp t * criticalResolventMoment t (N + 1) =
      (N.factorial : ℝ) := by
  unfold criticalResolventMoment
  rw [← integral_const_mul,
    ← integral_add (integrable_resolventMoment t N)
      ((integrable_resolventMoment t (N + 1)).const_mul (Real.exp t))]
  calc
    _ = ∫ x in Ioi (0 : ℝ), x ^ N * mobiusCriticalExponentialDensity x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hx
      dsimp only
      have hd : 1 + Real.exp t * x ≠ 0 := ne_of_gt (by positivity)
      rw [pow_succ]
      field_simp [hd]
    _ = _ := integral_Ioi_pow_mul_mobiusCriticalExponentialDensity N

/-- Exact signed remainder after truncating the Euler factorial series. -/
theorem criticalResolventMoment_remainder (t : ℝ) (N : ℕ) :
    criticalResolventMoment t 0 -
      ∑ k ∈ Finset.range N, (-Real.exp t) ^ k * (k.factorial : ℝ) =
      (-Real.exp t) ^ N * criticalResolventMoment t N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ih, pow_succ]
    have h := criticalResolventMoment_recurrence t N
    linear_combination (-Real.exp t) ^ N * h

/-- The factorial Gevrey bound follows from the positive remainder representation. -/
theorem criticalResolventMoment_factorial_bound (t : ℝ) (N : ℕ) :
    |criticalResolventMoment t 0 -
      ∑ k ∈ Finset.range N, (-Real.exp t) ^ k * (k.factorial : ℝ)| ≤
      (Real.exp t) ^ N * (N.factorial : ℝ) := by
  rw [criticalResolventMoment_remainder, abs_mul, abs_pow, abs_neg,
    abs_of_pos (Real.exp_pos t), abs_of_nonneg (criticalResolventMoment_bounds t N).1]
  exact mul_le_mul_of_nonneg_left (criticalResolventMoment_bounds t N).2 (by positivity)

#print axioms criticalResolventMoment_bounds
#print axioms criticalResolventMoment_recurrence
#print axioms criticalResolventMoment_remainder
#print axioms criticalResolventMoment_factorial_bound

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
