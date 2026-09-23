import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Kernel detection for positive operators

For a positive operator on a complex Hilbert space, the quadratic form detects its kernel.
The proof uses only positivity and symmetry: applying positivity to
`y + t • T y` gives a real quadratic polynomial whose constant term vanishes.  Its linear
coefficient is `2 ‖T y‖²`, so nonnegativity for every real `t` forces `T y = 0`.
-/

open Complex
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ContinuousLinearMap

/-- A zero of the quadratic form of a positive complex operator lies in its kernel. -/
theorem IsPositive.apply_eq_zero_of_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →L[ℂ] E} (hT : T.IsPositive) {y : E}
    (hy : ⟪y, T y⟫_ℂ = 0) :
    T y = 0 := by
  have hcross : ⟪y, T (T y)⟫_ℂ = ⟪T y, T y⟫_ℂ := by
    exact (hT.inner_left_eq_inner_right y (T y)).symm
  let a : ℝ := ‖T y‖ ^ (2 : ℕ)
  let c : ℝ := re ⟪T y, T (T y)⟫_ℂ
  have ha : 0 ≤ a := sq_nonneg _
  have hc : 0 ≤ c := hT.re_inner_nonneg_right (T y)
  have hpoly (t : ℝ) : 0 ≤ 2 * t * a + t ^ (2 : ℕ) * c := by
    have hp := hT.re_inner_nonneg_right (y + (t : ℂ) • T y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, hy, hcross, zero_add,
      Complex.conj_ofReal] at hp
    have hp' : 0 ≤ t * a + t * (a + t * c) := by
      simpa [a, c, Complex.add_re, Complex.mul_re,
        inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using hp
    nlinarith
  have ha0 : a = 0 := by
    by_contra hane
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hane)
    have h := hpoly (-a / (c + 1))
    have hc1 : 0 < c + 1 := by linarith
    field_simp at h
    nlinarith
  apply norm_eq_zero.mp
  dsimp [a] at ha0
  nlinarith [norm_nonneg (T y)]

end ContinuousLinearMap
