import GaloisForLFunctions.HTGeometry.PowerMomentSupport

/-!
# Transferring a support bound across representatives

Let `g x = ((x - c)/r)²`.  It is a polynomial, so all its powers are, and every power is bounded by
`1` on a set where `|x - c| ≤ r`.  A representative carried by such a set therefore has
`∫ gⁿ ≤ s₀` for every `n`, and any other representative inherits the bound because the moments
agree.

Using the *square* rather than the absolute value keeps every power polynomial; the parity split
that
`|x - c|` would force does not arise.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The powers of `((x - c)/r)²` are polynomial evaluations. -/
theorem eval_scaled_sq_pow (c r : ℝ) (hr : r ≠ 0) (n : ℕ) (x : ℝ) :
    ((Polynomial.C (1 / r) * (X - Polynomial.C c)) ^ (2 * n)).eval x
      = (((x - c) / r) ^ (2 : ℕ)) ^ n := by
  simp only [eval_pow, eval_mul, eval_sub, eval_C, eval_X]
  rw [pow_mul]
  congr 1
  field_simp

/-- **The power bound transfers to any other representative.** -/
theorem integral_scaled_sq_pow_le {mu nu : Measure ℝ} [IsFiniteMeasure mu]
    {c r : ℝ} (hr : r ≠ 0) {S : Set ℝ} (hmus : mu Sᶜ = 0)
    (hSb : ∀ x ∈ S, ((x - c) / r) ^ (2 : ℕ) ≤ 1)
    (hsmu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hintmu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) mu)
    (hsnu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂nu)
    (hintnu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu) (n : ℕ) :
    ∫ x, (((x - c) / r) ^ (2 : ℕ)) ^ n ∂nu ≤ s 0 := by
  set P : Polynomial ℝ := (Polynomial.C (1 / r) * (X - Polynomial.C c)) ^ (2 * n) with hP
  have hev : ∀ x : ℝ, P.eval x = (((x - c) / r) ^ (2 : ℕ)) ^ n := fun x =>
    eval_scaled_sq_pow c r hr n x
  have htrans : ∫ x, (((x - c) / r) ^ (2 : ℕ)) ^ n ∂nu = ∫ x, (((x - c) / r) ^ (2 : ℕ)) ^ n ∂mu := by
    have h1 : ∫ x, P.eval x ∂mu = ∫ x, P.eval x ∂nu :=
      integral_eval_eq_of_moments_eq hsmu hintmu hsnu hintnu P
    simp only [hev] at h1
    exact h1.symm
  rw [htrans]
  -- on the carrying set the integrand is at most one
  have hae : ∀ᵐ x ∂mu, (((x - c) / r) ^ (2 : ℕ)) ^ n ≤ 1 := by
    have hS : ∀ᵐ x ∂mu, x ∈ S := by
      rw [ae_iff]; simpa using! hmus
    filter_upwards [hS] with x hx
    exact pow_le_one₀ (sq_nonneg _) (hSb x hx)
  have hintg : Integrable (fun x : ℝ => (((x - c) / r) ^ (2 : ℕ)) ^ n) mu := by
    have := integrable_eval hintmu P
    simpa only [hev] using this
  have hmass : ∫ _x : ℝ, (1 : ℝ) ∂mu = s 0 := by
    have h0 := hsmu 0
    simpa using h0.symm
  calc ∫ x, (((x - c) / r) ^ (2 : ℕ)) ^ n ∂mu
      ≤ ∫ _x : ℝ, (1 : ℝ) ∂mu := integral_mono_ae hintg (integrable_const 1) hae
    _ = s 0 := hmass

end HTGeometry
