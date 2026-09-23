import GaloisForLFunctions.RHTower.ConnesSgnFubiniPairing

/-!
# Substituting the truncated kernel and dropping the constant term

Step 1b (continued) of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`connes_sgn_pairing_truncated` expresses the truncated sign pairing as a frequency integral
against `∫_{-X}^{X} sgn(x) e^{2πixu} dx`, and `connes_sgn_truncated_kernel` evaluates that kernel
as `2i(1 − cos 2πXu)/(2πu)`.  Substituting and splitting off the constant part of the
principal-value integrand gives

  `∫_{-X}^{X} sgn(x) g(x) dx = (i/π) ∫ H(u) (1 − cos 2πXu) du`,

because the constant part pairs with the *odd* `1/u` over the symmetric unit ball and vanishes -
`connes_integral_odd_symmetric`.  This is the step at which the Euler-Mascheroni constant would
have appeared had the cut-off not been symmetric.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap FourierTransform Interval

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- `0 ≤ 1 − cos t ≤ t²/2`. -/
theorem connes_one_sub_cos_bounds (t : ℝ) :
    0 ≤ 1 - Real.cos t ∧ 1 - Real.cos t ≤ t ^ (2 : ℕ) / 2 := by
  have hhalf : Real.sin (t / 2) ^ (2 : ℕ) = (1 - Real.cos t) / 2 := by
    have hpyth := Real.sin_sq_add_cos_sq (t / 2)
    have hdouble : Real.cos t = 2 * Real.cos (t / 2) ^ (2 : ℕ) - 1 := by
      have h := Real.cos_two_mul (t / 2)
      rwa [show 2 * (t / 2) = t by ring] at h
    nlinarith [hpyth, hdouble]
  refine ⟨by nlinarith [sq_nonneg (Real.sin (t / 2))], ?_⟩
  have habs : |Real.sin (t / 2)| ≤ |t / 2| := Real.abs_sin_le_abs
  have hsq : Real.sin (t / 2) ^ (2 : ℕ) ≤ (t / 2) ^ (2 : ℕ) := by
    have h1 : |Real.sin (t / 2)| ^ (2 : ℕ) ≤ |t / 2| ^ (2 : ℕ) :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    rwa [sq_abs, sq_abs] at h1
  nlinarith [hhalf, hsq]

/-- A measurable function bounded on the interval is interval integrable. -/
theorem connes_boundedM_intervalIntegrable {f : ℝ → ℂ} {M : ℝ} {a b : ℝ}
    (hm : AEStronglyMeasurable f volume) (hb : ∀ x ∈ Ι a b, ‖f x‖ ≤ M) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne hm ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  exact hb x hx

/-- The oscillating quotient is bounded on the whole line for a fixed cut-off. -/
theorem connes_oscQuotient_bound (X u : ℝ) :
    ‖(((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)‖
      ≤ 2 * Real.pi ^ (2 : ℕ) * X ^ (2 : ℕ) * |u| := by
  obtain ⟨hnn, hle⟩ := connes_one_sub_cos_bounds (2 * Real.pi * X * u)
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu]
  · have hu0 : (0 : ℝ) < |u| := abs_pos.mpr hu
    rw [abs_div, abs_of_nonneg hnn, div_le_iff₀ hu0]
    calc 1 - Real.cos (2 * Real.pi * X * u)
        ≤ (2 * Real.pi * X * u) ^ (2 : ℕ) / 2 := hle
      _ = 2 * Real.pi ^ (2 : ℕ) * X ^ (2 : ℕ) * u ^ (2 : ℕ) := by ring
      _ = 2 * Real.pi ^ (2 : ℕ) * X ^ (2 : ℕ) * |u| * |u| := by
          rw [← sq_abs u]
          ring

/-- The oscillating quotient is odd. -/
theorem connes_oscQuotient_odd (X u : ℝ) :
    (((1 - Real.cos (2 * Real.pi * X * -u)) / (-u) : ℝ) : ℂ)
      = -(((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ) := by
  have hcos : Real.cos (2 * Real.pi * X * -u) = Real.cos (2 * Real.pi * X * u) := by
    rw [show 2 * Real.pi * X * -u = -(2 * Real.pi * X * u) by ring, Real.cos_neg]
  rw [hcos, div_neg]
  push_cast
  ring

/-- **The constant term of the principal-value integrand drops out**, by oddness. -/
theorem connes_oscQuotient_ball_vanishes (X : ℝ) :
    (∫ u in (-1 : ℝ)..1, (((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)) = 0 := by
  refine connes_integral_odd_symmetric (a := (1 : ℝ)) zero_le_one
    (fun u => connes_oscQuotient_odd X u) ?_
  refine connes_boundedM_intervalIntegrable (M := 2 * Real.pi ^ (2 : ℕ) * X ^ (2 : ℕ)) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Complex.measurable_ofReal.comp ?_
    exact (measurable_const.sub
      (Real.measurable_cos.comp (measurable_const.mul measurable_id))).div measurable_id
  · intro u hu
    have hu1 : |u| ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
      rw [abs_le]
      exact ⟨hu.1.le, hu.2⟩
    have hM0 : (0 : ℝ) ≤ 2 * Real.pi ^ (2 : ℕ) * X ^ (2 : ℕ) := by positivity
    calc ‖(((1 - Real.cos (2 * Real.pi * X * u)) / u : ℝ) : ℂ)‖
        ≤ 2 * Real.pi ^ (2 : ℕ) * X ^ (2 : ℕ) * |u| := connes_oscQuotient_bound X u
      _ ≤ 2 * Real.pi ^ (2 : ℕ) * X ^ (2 : ℕ) * 1 := by
          exact mul_le_mul_of_nonneg_left hu1 hM0
      _ = 2 * Real.pi ^ (2 : ℕ) * X ^ (2 : ℕ) := mul_one _

end

end GaloisForLFunctions.RHTower
