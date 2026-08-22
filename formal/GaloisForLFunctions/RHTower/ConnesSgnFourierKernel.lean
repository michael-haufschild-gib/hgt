import GaloisForLFunctions.RHTower.ConnesDirichletSineIntegral

/-!
# The truncated Fourier kernel of the sign function

Step 1 of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Truncating the sign function to `|x| ≤ X` makes its Fourier pairing an honest double integral, and
the truncated kernel is

  `∫_{-X}^{X} sgn(x) e^{2πixu} dx = 2i (1 − cos 2πXu)/(2πu)`.

The factor `1 − cos 2πXu` vanishes to second order at `u = 0`, so the pairing with `𝓕g` splits
without any principal value; and it is *even* in `u`, so its pairing with the odd `1/u` over a
symmetric set drops out - the reason no Euler-Mascheroni constant enters the final identification.
-/

open MeasureTheory Set Filter Topology Real
open scoped Interval

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The character used throughout, as a function of the space variable. -/
def connesSpaceChar (u x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x * u : ℝ) : ℂ) * Complex.I)

theorem connesSpaceChar_norm (u x : ℝ) : ‖connesSpaceChar u x‖ = 1 := by
  rw [connesSpaceChar]
  exact Complex.norm_exp_ofReal_mul_I _

theorem connesSpaceChar_continuous (u : ℝ) : Continuous (connesSpaceChar u) := by
  unfold connesSpaceChar
  fun_prop

theorem connes_abs_sign_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h]
    norm_num
  · rw [h, Real.sign_zero]
    norm_num
  · rw [Real.sign_of_pos h]
    norm_num

theorem connes_measurable_sign : Measurable Real.sign := by
  unfold Real.sign
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

/-- A bounded measurable function is interval integrable. -/
theorem connes_bounded_intervalIntegrable {f : ℝ → ℂ}
    (hm : AEStronglyMeasurable f volume) (hb : ∀ x : ℝ, ‖f x‖ ≤ 1) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := (1 : ℝ)) measure_Ioc_lt_top.ne hm ?_
  filter_upwards with x
  exact hb x

/-- The truncated sign–character integrand is interval integrable. -/
theorem connes_sgnChar_intervalIntegrable (u a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (Real.sign x : ℂ) * connesSpaceChar u x) volume a b := by
  refine connes_bounded_intervalIntegrable ?_ ?_ a b
  · refine AEStronglyMeasurable.mul ?_ ((connesSpaceChar_continuous u).aestronglyMeasurable)
    exact (Complex.measurable_ofReal.comp connes_measurable_sign).aestronglyMeasurable
  · intro x
    rw [norm_mul, connesSpaceChar_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact connes_abs_sign_le_one x

/-- The reflected integrand is interval integrable too. -/
theorem connes_sgnChar_neg_intervalIntegrable (u a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (Real.sign (-x) : ℂ) * connesSpaceChar u (-x))
      volume a b := by
  refine connes_bounded_intervalIntegrable ?_ ?_ a b
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.measurable_ofReal.comp
        (connes_measurable_sign.comp measurable_neg)).aestronglyMeasurable
    · exact ((connesSpaceChar_continuous u).comp continuous_neg).aestronglyMeasurable
  · intro x
    rw [norm_mul, connesSpaceChar_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact connes_abs_sign_le_one (-x)

/-- The scaled sine primitive. -/
theorem connes_intervalIntegral_sin_scaled {u : ℝ} (hu : u ≠ 0) (X : ℝ) :
    (∫ x in (0 : ℝ)..X, Real.sin (2 * Real.pi * x * u))
      = (1 - Real.cos (2 * Real.pi * X * u)) / (2 * Real.pi * u) := by
  have hpu : (2 : ℝ) * Real.pi * u ≠ 0 := by
    have hpi := Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) hu
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) X,
      HasDerivAt (fun x : ℝ => -Real.cos (2 * Real.pi * x * u) / (2 * Real.pi * u))
        (Real.sin (2 * Real.pi * x * u)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => 2 * Real.pi * x * u) (2 * Real.pi * u) x := by
      have h := ((hasDerivAt_id x).const_mul (2 * Real.pi)).mul_const u
      refine h.congr_deriv ?_
      ring
    have h2 : HasDerivAt (fun x : ℝ => Real.cos (2 * Real.pi * x * u))
        (-Real.sin (2 * Real.pi * x * u) * (2 * Real.pi * u)) x :=
      (Real.hasDerivAt_cos _).comp x h1
    have h3 := (h2.neg).div_const (2 * Real.pi * u)
    refine h3.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => Real.sin (2 * Real.pi * x * u)) volume 0 X := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, zero_mul, Real.cos_zero]
  field_simp
  ring

/-- The character difference is twice `i sin`. -/
theorem connes_spaceChar_sub_neg (u x : ℝ) :
    connesSpaceChar u x - connesSpaceChar u (-x)
      = 2 * Complex.I * ((Real.sin (2 * Real.pi * x * u) : ℝ) : ℂ) := by
  have hneg : (2 * Real.pi * (-x) * u : ℝ) = -(2 * Real.pi * x * u) := by ring
  rw [connesSpaceChar, connesSpaceChar, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **The truncated sign kernel.**  `∫_{-X}^{X} sgn(x) e^{2πixu} dx = 2i(1 − cos 2πXu)/(2πu)`. -/
theorem connes_sgn_truncated_kernel {u : ℝ} (hu : u ≠ 0) {X : ℝ} (hX : 0 ≤ X) :
    (∫ x in (-X : ℝ)..X, (Real.sign x : ℂ) * connesSpaceChar u x)
      = 2 * Complex.I * (((1 - Real.cos (2 * Real.pi * X * u)) / (2 * Real.pi * u) : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun x : ℝ => (Real.sign x : ℂ) * connesSpaceChar u x with hF
  have hsplit : (∫ x in (-X : ℝ)..X, F x)
      = (∫ x in (-X : ℝ)..(0 : ℝ), F x) + ∫ x in (0 : ℝ)..X, F x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (connes_sgnChar_intervalIntegrable u (-X) 0)
      (connes_sgnChar_intervalIntegrable u 0 X)).symm
  have hrefl : (∫ x in (-X : ℝ)..(0 : ℝ), F x) = ∫ x in (0 : ℝ)..X, F (-x) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := X) F
    simpa using h.symm
  have hpt : ∀ x ∈ Ι (0 : ℝ) X, F (-x) + F x
      = 2 * Complex.I * ((Real.sin (2 * Real.pi * x * u) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : 0 < x := by
      rw [Set.uIoc_of_le hX] at hx
      exact hx.1
    have hs1 : Real.sign x = 1 := Real.sign_of_pos hx0
    have hs2 : Real.sign (-x) = -1 := Real.sign_of_neg (neg_neg_iff_pos.mpr hx0)
    simp only [hF, hs1, hs2]
    rw [← connes_spaceChar_sub_neg u x]
    push_cast
    ring
  have hcomb : (∫ x in (0 : ℝ)..X, F (-x)) + ∫ x in (0 : ℝ)..X, F x
      = ∫ x in (0 : ℝ)..X, 2 * Complex.I * ((Real.sin (2 * Real.pi * x * u) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_add
      (connes_sgnChar_neg_intervalIntegrable u 0 X)
      (connes_sgnChar_intervalIntegrable u 0 X)]
    exact intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun x hx => hpt x hx)
  rw [hsplit, hrefl, hcomb, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, connes_intervalIntegral_sin_scaled hu X]

end

end GaloisForLFunctions.RHTower
