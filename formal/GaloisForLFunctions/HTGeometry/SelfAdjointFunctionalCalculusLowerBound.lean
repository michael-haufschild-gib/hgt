import Mathlib

/-!
# Quadratic-form lower bounds from the continuous functional calculus

For a bounded self-adjoint operator `A` on a complex Hilbert space and a real continuous function `g`
on its spectrum bounded below by `c`, the operator `g(A) − c` is positive, hence

`c · ‖f‖² ≤ Re ⟪g(A) f, f⟫` for every `f`.

This is the abstract step by which a pointwise lower bound of a spectral kernel on the spectrum becomes a
lower bound of the associated quadratic form, with no spectral measure, eigenfunction expansion, or
discreteness of the spectrum required.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonnegative continuous function of a self-adjoint operator is a positive operator. -/
theorem isPositive_cfc_of_nonneg (A : H →L[ℂ] H) {g : ℝ → ℝ}
    (hg : ∀ x ∈ spectrum ℝ A, 0 ≤ g x) : (cfc g A).IsPositive := by
  rw [← ContinuousLinearMap.nonneg_iff_isPositive]
  exact cfc_nonneg hg

/-- **Quadratic-form lower bound.**  If `c ≤ g` on the spectrum of the self-adjoint operator `A`, then
`c · ‖f‖² ≤ Re ⟪g(A) f, f⟫` for every vector `f`. -/
theorem re_inner_cfc_self_ge (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {g : ℝ → ℝ}
    (hg : ContinuousOn g (spectrum ℝ A)) {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, c ≤ g x) (f : H) :
    c * ‖f‖ ^ 2 ≤ RCLike.re ⟪cfc g A f, f⟫_ℂ := by
  have hsub : cfc (fun x : ℝ => g x - c) A = cfc g A - algebraMap ℝ (H →L[ℂ] H) c := by
    rw [cfc_sub g (fun _ => c) A hg (continuousOn_const), cfc_const c A hA]
  have hpos : (cfc (fun x : ℝ => g x - c) A).IsPositive :=
    isPositive_cfc_of_nonneg A (fun x hx => sub_nonneg.mpr (hc x hx))
  have h0 := hpos.inner_nonneg_left f
  rw [hsub] at h0
  have hre : RCLike.re ⟪(cfc g A - algebraMap ℝ (H →L[ℂ] H) c) f, f⟫_ℂ =
      RCLike.re ⟪cfc g A f, f⟫_ℂ - c * ‖f‖ ^ 2 := by
    rw [sub_apply, inner_sub_left, map_sub, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
      inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have := (RCLike.nonneg_iff.mp h0).1
  rw [hre] at this
  linarith

end GaloisForLFunctions.HTGeometry
