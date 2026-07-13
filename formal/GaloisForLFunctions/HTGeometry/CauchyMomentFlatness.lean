import Mathlib

/-!
# Moment-fiber Cauchy-transform flatness

Two finite measures with the same moments through order `N` have Cauchy transforms that agree to
order `N+1` at infinity: this is the all-order flatness underlying the indeterminate-moment fiber
(`indeterminate-moment-fiber-maximal-translation-ht`, eq. (9)).  The mechanism is the finite
geometric expansion of the Cauchy kernel

`(z − x)⁻¹ = ∑_{k=0}^{N} xᵏ / z^{k+1} + x^{N+1} / z^{N+1} · (z − x)⁻¹`,

whose polynomial part is annihilated by the equal moments, leaving an `O(z^{-(N+1)})` remainder.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

/-- **Finite geometric expansion of the Cauchy kernel.** For `z ≠ 0` and `x ≠ z`,
`(z − x)⁻¹` splits into a degree-`N` polynomial tail in `1/z` plus a remainder of order `z^{-(N+1)}`. -/
theorem cauchy_kernel_finite_expansion (x z : ℂ) (hz : z ≠ 0) (hxz : x ≠ z) (N : ℕ) :
    (z - x)⁻¹ = (∑ k ∈ Finset.range (N + 1), x ^ k / z ^ (k + 1))
      + x ^ (N + 1) / z ^ (N + 1) * (z - x)⁻¹ := by
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  have htel : (z - x) * (∑ k ∈ Finset.range (N + 1), x ^ k / z ^ (k + 1))
      = 1 - x ^ (N + 1) / z ^ (N + 1) := by
    have hsum : ∀ k, (z - x) * (x ^ k / z ^ (k + 1))
        = x ^ k / z ^ k - x ^ (k + 1) / z ^ (k + 1) := by
      intro k; field_simp; ring
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hsum k),
      Finset.sum_range_sub' (fun k => x ^ k / z ^ k) (N + 1)]
    simp
  have key : (z - x) * ((∑ k ∈ Finset.range (N + 1), x ^ k / z ^ (k + 1))
      + x ^ (N + 1) / z ^ (N + 1) * (z - x)⁻¹) = 1 := by
    rw [mul_add, htel,
      show (z - x) * (x ^ (N + 1) / z ^ (N + 1) * (z - x)⁻¹) = x ^ (N + 1) / z ^ (N + 1) by
        rw [mul_comm (x ^ (N + 1) / z ^ (N + 1)) ((z - x)⁻¹), ← mul_assoc,
          mul_inv_cancel₀ hzx, one_mul]]
    ring
  exact inv_eq_of_mul_eq_one_right key

theorem cauchy_integral_expansion {ρ : Measure ℝ} (z : ℂ) (hz : z ≠ 0) (himz : z.im ≠ 0) (N : ℕ)
    (hInt : ∀ k ∈ Finset.range (N + 1), Integrable (fun x : ℝ => (x : ℂ) ^ k) ρ)
    (hIntR : Integrable (fun x : ℝ => (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹) ρ) :
    ∫ x, (z - (x : ℂ))⁻¹ ∂ρ
      = (∑ k ∈ Finset.range (N + 1), (∫ x, (x : ℂ) ^ k ∂ρ) / z ^ (k + 1))
        + (∫ x, (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹ ∂ρ) / z ^ (N + 1) := by
  have hxne : ∀ x : ℝ, (x : ℂ) ≠ z := by
    intro x h; apply himz; rw [← h]; simp
  have hreassoc : ∀ x : ℝ, (x : ℂ) ^ (N + 1) / z ^ (N + 1) * (z - (x : ℂ))⁻¹
      = (z ^ (N + 1))⁻¹ * ((x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹) := by
    intro x; rw [div_eq_mul_inv]; ring
  have hpoint : (fun x : ℝ => (z - (x : ℂ))⁻¹)
      = fun x : ℝ => (∑ k ∈ Finset.range (N + 1), (x : ℂ) ^ k / z ^ (k + 1))
        + (z ^ (N + 1))⁻¹ * ((x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹) := by
    funext x
    have he := cauchy_kernel_finite_expansion (x : ℂ) z hz (hxne x) N
    rw [hreassoc x] at he
    exact he
  rw [hpoint]
  have hIntSum : Integrable
      (fun x : ℝ => ∑ k ∈ Finset.range (N + 1), (x : ℂ) ^ k / z ^ (k + 1)) ρ :=
    integrable_finsetSum _ (fun k hk => ((hInt k hk).div_const _))
  have hIntRem : Integrable
      (fun x : ℝ => (z ^ (N + 1))⁻¹ * ((x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹)) ρ :=
    hIntR.const_mul _
  rw [integral_add hIntSum hIntRem]
  congr 1
  · rw [integral_finsetSum _ (fun k hk => ((hInt k hk).div_const _))]
    exact Finset.sum_congr rfl (fun k _ => integral_div _ _)
  · rw [integral_const_mul, ← div_eq_inv_mul]

/-- **Moment-fiber Cauchy flatness.** Two finite measures with equal moments through order `N` have
Cauchy transforms differing only by the order-`z^{-(N+1)}` remainder. -/
theorem cauchy_transform_sub_of_moments_eq {mu nu : Measure ℝ} (z : ℂ) (hz : z ≠ 0)
    (himz : z.im ≠ 0) (N : ℕ)
    (hIntMu : ∀ k ∈ Finset.range (N + 1), Integrable (fun x : ℝ => (x : ℂ) ^ k) mu)
    (hIntRMu : Integrable (fun x : ℝ => (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹) mu)
    (hIntNu : ∀ k ∈ Finset.range (N + 1), Integrable (fun x : ℝ => (x : ℂ) ^ k) nu)
    (hIntRNu : Integrable (fun x : ℝ => (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹) nu)
    (hmom : ∀ k ∈ Finset.range (N + 1), (∫ x, (x : ℂ) ^ k ∂mu) = ∫ x, (x : ℂ) ^ k ∂nu) :
    (∫ x, (z - (x : ℂ))⁻¹ ∂mu) - ∫ x, (z - (x : ℂ))⁻¹ ∂nu
      = ((∫ x, (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹ ∂mu)
          - ∫ x, (x : ℂ) ^ (N + 1) * (z - (x : ℂ))⁻¹ ∂nu) / z ^ (N + 1) := by
  rw [cauchy_integral_expansion z hz himz N hIntMu hIntRMu,
    cauchy_integral_expansion z hz himz N hIntNu hIntRNu]
  have hsum : (∑ k ∈ Finset.range (N + 1), (∫ x, (x : ℂ) ^ k ∂mu) / z ^ (k + 1))
      = ∑ k ∈ Finset.range (N + 1), (∫ x, (x : ℂ) ^ k ∂nu) / z ^ (k + 1) :=
    Finset.sum_congr rfl (fun k hk => by rw [hmom k hk])
  rw [hsum]
  ring

end HTGeometry
