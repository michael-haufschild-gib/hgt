import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# A positive involution is the identity

If `A` is a positive operator on a complex Hilbert space with `A² = I`, then `A = I`: the operator
`A + I` is bounded below by one, so `(A + I)(A - I) = A² - I = 0` forces `A - I = 0`.
-/

open scoped InnerProductSpace ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-- **No-go.**  A positive involution of a Hilbert space is the identity. -/
theorem eq_one_of_isPositive_of_mul_self_eq_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →L[ℂ] H} (hA : A.IsPositive)
    (h2 : A * A = 1) : A = 1 := by
  have hlow : ∀ y, ‖y‖ ^ 2 ≤ ‖(A + 1) y‖ * ‖y‖ := by
    intro y
    have hp : 0 ≤ (inner ℂ (A y) y).re :=
      (Complex.le_def.1 (((ContinuousLinearMap.isPositive_iff A).1 hA).2 y)).1
    have hself : (inner ℂ y y).re = ‖y‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    calc ‖y‖ ^ 2 ≤ (inner ℂ (A y) y).re + (inner ℂ y y).re := by rw [hself]; linarith
      _ = (inner ℂ ((A + 1) y) y).re := by
        have h1 : (A + 1) y = A y + y := rfl
        rw [h1, inner_add_left, Complex.add_re]
      _ ≤ ‖inner ℂ ((A + 1) y) y‖ := Complex.re_le_norm _
      _ ≤ ‖(A + 1) y‖ * ‖y‖ := norm_inner_le_norm _ _
  ext x
  set y := (A - 1) x with hy
  have hzero : (A + 1) y = 0 := by
    have : (A + 1) * (A - 1) = A * A - 1 := by noncomm_ring
    change ((A + 1) * (A - 1)) x = 0
    rw [this, h2, sub_self]
    rfl
  have hy0 : y = 0 := by
    have h := hlow y
    rw [hzero, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg y])
  have : A x - x = 0 := by
    rw [← hy0, hy]
    rfl
  exact sub_eq_zero.1 this

end GaloisForLFunctions.HTGeometry
