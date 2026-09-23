import GaloisForLFunctions.RHTower.Sieve.GallagherSobolev

/-!
# Orthogonality of the characters on the unit interval

`∫_0^(1 : ℕ) e(kt) dt = 1` if `k = 0` and `0` otherwise, for integral `k`.

For `k ≠ 0` the integrand has the explicit antiderivative `e(kt)/(2πik)`, which is one-periodic, so
the two endpoint values cancel.  Nothing beyond the fundamental theorem of calculus is used; in
particular this avoids the measure-space subtleties of the additive circle, working throughout on
the interval `[0,1]` with Lebesgue measure.

This is the orthogonality that turns `∫_0^(1 : ℕ) |S|²` into `∑_n |a_n|²` for a trigonometric polynomial,
the last analytic input Gallagher's route to the sharp large sieve needs.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- The antiderivative of a nonzero character. -/
noncomputable def circleAnti (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) * (t : ℂ))
    / (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I)

/-- The characters take the value `1` at the integers. -/
theorem circleFreq_intCast (k : ℤ) : circleFreq (k : ℝ) = 1 := by
  rw [circleFreq]
  have hrw : ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hrw, Complex.exp_int_mul_two_pi_mul_I]

/-- The frequency scale is nonzero. -/
theorem two_pi_mul_ne_zero {k : ℤ} (hk : k ≠ 0) :
    (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨⟨two_ne_zero, hpi⟩, hk'⟩, Complex.I_ne_zero⟩

/-- The antiderivative differentiates to the character. -/
theorem hasDerivAt_circleAnti {k : ℤ} (hk : k ≠ 0) (t : ℝ) :
    HasDerivAt (circleAnti k) (circleFreq ((k : ℝ) * t)) t := by
  have hne := two_pi_mul_ne_zero hk
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) ((1 : ℝ) : ℂ) t :=
    (hasDerivAt_id t).ofReal_comp
  have hg := (hid.const_mul (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I)).cexp
  have hdiv := hg.div_const (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I)
  have hrw : Complex.exp ((2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) * (t : ℂ))
      * ((2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) * ((1 : ℝ) : ℂ))
      / (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I)
      = circleFreq ((k : ℝ) * t) := by
    rw [circleFreq]
    have harg : ((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I
        = (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) * (t : ℂ) := by
      push_cast
      ring
    rw [harg]
    push_cast
    field_simp
  rw [← hrw]
  exact hdiv

/-- The character is continuous, hence interval-integrable. -/
theorem intervalIntegrable_circleFreq_mul (c : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => circleFreq (c * t)) volume a b := by
  refine Continuous.intervalIntegrable ?_ a b
  unfold circleFreq
  fun_prop

/-- **Orthogonality of the characters on the unit interval.** -/
theorem integral_circleFreq_intCast (k : ℤ) :
    (∫ t in (0 : ℝ)..1, circleFreq ((k : ℝ) * t)) = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [if_pos rfl]
    have hzero : ∀ t : ℝ, circleFreq (((0 : ℤ) : ℝ) * t) = 1 := by
      intro t
      simp [circleFreq]
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℂ)) (fun t _ => hzero t)]
    simp
  · rw [if_neg hk]
    have hFTC : (∫ t in (0 : ℝ)..1, circleFreq ((k : ℝ) * t))
        = circleAnti k 1 - circleAnti k 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_circleAnti hk t)
        (intervalIntegrable_circleFreq_mul (k : ℝ) 0 1)
    rw [hFTC, circleAnti, circleAnti]
    have hone : Complex.exp ((2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) * ((1 : ℝ) : ℂ)) = 1 := by
      have := circleFreq_intCast k
      rw [circleFreq] at this
      have harg : ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I
          = (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) * ((1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg] at this
      exact this
    have hzero : Complex.exp ((2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) * ((0 : ℝ) : ℂ)) = 1 := by
      simp
    rw [hone, hzero, sub_self]

end RHTower.Sieve
