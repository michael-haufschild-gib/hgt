import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Moment bounds from an odd observation budget

For a nonnegative density and a nonnegative observation coordinate, integral Cauchy--Schwarz
makes the second observation log-convex between the first and third.  If an independent odd
observation bounds `M₁ + M₃ / 24`, elementary polarization then bounds `M₂²` by six times the
square of that budget.

The `sinh` truncation at the end supplies this odd budget whenever opposite exponential channels
are known.  These are static observation relations; no temporal evolution is assumed.
-/

open Real MeasureTheory

namespace HTGeometry

noncomputable section

/-- The second moment of a nonnegative observation is log-convex between its first and third
moments. -/
theorem sq_second_observation_le_first_mul_third
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {X ρ : α → ℝ}
    (hX : AEStronglyMeasurable X μ)
    (hρ : AEStronglyMeasurable ρ μ)
    (hXnonneg : ∀ᵐ x ∂μ, 0 ≤ X x)
    (hρnonneg : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hfirst : Integrable (fun x => X x * ρ x) μ)
    (hthird : Integrable (fun x => X x ^ 3 * ρ x) μ) :
    (∫ x, X x ^ 2 * ρ x ∂μ) ^ 2 ≤
      (∫ x, X x * ρ x ∂μ) * ∫ x, X x ^ 3 * ρ x ∂μ := by
  let f : α → ℝ := fun x => Real.sqrt (X x * ρ x)
  let g : α → ℝ := fun x => X x * Real.sqrt (X x * ρ x)
  have hsqrt : AEStronglyMeasurable (fun x => Real.sqrt (X x * ρ x)) μ :=
    (hX.mul hρ).aemeasurable.sqrt.aestronglyMeasurable
  have hfmeas : AEStronglyMeasurable f μ := hsqrt
  have hgmeas : AEStronglyMeasurable g μ := hX.mul hsqrt
  have hf : Integrable (fun x => f x ^ 2) μ := by
    apply hfirst.congr
    filter_upwards [hXnonneg, hρnonneg] with x hx hρx
    dsimp only [f]
    rw [Real.sq_sqrt (mul_nonneg hx hρx)]
  have hg : Integrable (fun x => g x ^ 2) μ := by
    apply hthird.congr
    filter_upwards [hXnonneg, hρnonneg] with x hx hρx
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hx hρx)]
    ring
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq
    hfmeas hgmeas hf hg
  have hfg : (∫ x, f x * g x ∂μ) = ∫ x, X x ^ 2 * ρ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hXnonneg, hρnonneg] with x hx hρx
    dsimp only [f, g]
    rw [show Real.sqrt (X x * ρ x) *
          (X x * Real.sqrt (X x * ρ x)) =
        X x * Real.sqrt (X x * ρ x) ^ 2 by ring,
      Real.sq_sqrt (mul_nonneg hx hρx)]
    ring
  have hfsq : (∫ x, f x ^ 2 ∂μ) = ∫ x, X x * ρ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hXnonneg, hρnonneg] with x hx hρx
    dsimp only [f]
    rw [Real.sq_sqrt (mul_nonneg hx hρx)]
  have hgsq : (∫ x, g x ^ 2 ∂μ) = ∫ x, X x ^ 3 * ρ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hXnonneg, hρnonneg] with x hx hρx
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hx hρx)]
    ring
  rwa [hfg, hfsq, hgsq] at hcs

/-- Combining adjacent moment log-convexity with the first two terms of an odd observation budget
gives a closed square bound for the second moment. -/
theorem sq_second_observation_le_six_budget_sq
    {m₁ m₂ m₃ S : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₃ : 0 ≤ m₃)
    (hlog : m₂ ^ 2 ≤ m₁ * m₃)
    (hbudget : m₁ + m₃ / 24 ≤ S) :
    m₂ ^ 2 ≤ 6 * S ^ 2 := by
  have hsum0 : 0 ≤ m₁ + m₃ / 24 := by positivity
  have hS0 : 0 ≤ S := hsum0.trans hbudget
  have hprod : m₁ * m₃ ≤ 6 * (m₁ + m₃ / 24) ^ 2 := by
    nlinarith [sq_nonneg (m₁ - m₃ / 24)]
  have hsquare : (m₁ + m₃ / 24) ^ 2 ≤ S ^ 2 :=
    (sq_le_sq₀ hsum0 hS0).2 hbudget
  nlinarith

/-- The first two positive terms in the `sinh` series. -/
theorem self_add_cube_div_six_le_sinh {u : ℝ} (hu : 0 ≤ u) :
    u + u ^ 3 / 6 ≤ Real.sinh u := by
  rw [Real.sinh_eq_tsum]
  have hsum := (u.hasSum_sinh.summable).sum_le_tsum
    (Finset.range 2) (fun n _hn => by positivity)
  norm_num [Finset.sum_range_succ] at hsum ⊢
  simpa using hsum

/-- Half-density scaling of the first two positive `sinh` terms. -/
theorem self_add_cube_div_twenty_four_le_two_sinh_half
    {x : ℝ} (hx : 0 ≤ x) :
    x + x ^ 3 / 24 ≤ 2 * Real.sinh (x / 2) := by
  have h := self_add_cube_div_six_le_sinh (u := x / 2) (by positivity)
  nlinarith

/-- The first three nonnegative terms of the even exponential observation. -/
theorem one_add_sq_div_two_add_fourth_div_twenty_four_le_cosh (u : ℝ) :
    1 + u ^ 2 / 2 + u ^ 4 / 24 ≤ Real.cosh u := by
  rw [Real.cosh_eq_tsum]
  have hsum := (Real.hasSum_cosh u).summable.sum_le_tsum
    (Finset.range 3) (fun n _hn => by
      rw [show 2 * n = n + n by omega, pow_add]
      exact div_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _))
  norm_num [Finset.sum_range_succ] at hsum ⊢
  simpa [pow_two] using hsum

/-- Half-density scaling of the first three nonnegative `cosh` terms. -/
theorem one_add_sq_div_eight_add_fourth_div_384_le_cosh_half (x : ℝ) :
    1 + x ^ 2 / 8 + x ^ 4 / 384 ≤ Real.cosh (x / 2) := by
  have h := one_add_sq_div_two_add_fourth_div_twenty_four_le_cosh (x / 2)
  convert h using 1
  ring

end

end HTGeometry
