import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.LatticeDirectionCapacity
import Mathlib

/-!
# The symmetric square root of a positive operator

A symmetric positive operator on a finite-dimensional real inner product space has a symmetric
square root, obtained by taking square roots of its eigenvalues in an orthonormal eigenbasis.
This supplies the factorization `A₀ = B ∘ B` with `B` symmetric that a Gram realization of a
capacity chart needs.
-/

open scoped RealInnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section SymmetricSqrt

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

variable {A : Y →ₗ[ℝ] Y} (hA : A.IsSymmetric)

/-- The orthonormal eigenbasis of a symmetric operator. -/
noncomputable def eigBasis : OrthonormalBasis (Fin (Module.finrank ℝ Y)) ℝ Y :=
  hA.eigenvectorBasis rfl

/-- The eigenvalues of a symmetric operator. -/
noncomputable def eigVal (i : Fin (Module.finrank ℝ Y)) : ℝ := hA.eigenvalues rfl i

theorem apply_eigBasis (i : Fin (Module.finrank ℝ Y)) :
    A (eigBasis hA i) = eigVal hA i • eigBasis hA i :=
  hA.apply_eigenvectorBasis rfl i

theorem eigVal_nonneg (hpos : ∀ x, 0 ≤ ⟪A x, x⟫) (i : Fin (Module.finrank ℝ Y)) :
    0 ≤ eigVal hA i := by
  have h := hpos (eigBasis hA i)
  rw [apply_eigBasis, real_inner_smul_left, real_inner_self_eq_norm_sq,
    (eigBasis hA).orthonormal.1 i] at h
  simpa using h

theorem eigVal_pos (hpos : ∀ x, x ≠ 0 → 0 < ⟪A x, x⟫) (i : Fin (Module.finrank ℝ Y)) :
    0 < eigVal hA i := by
  have hne : eigBasis hA i ≠ 0 := by
    intro hzero
    have := (eigBasis hA).orthonormal.1 i
    rw [hzero, norm_zero] at this
    exact zero_ne_one this
  have h := hpos (eigBasis hA i) hne
  rw [apply_eigBasis, real_inner_smul_left, real_inner_self_eq_norm_sq,
    (eigBasis hA).orthonormal.1 i] at h
  simpa using h

/-- The spectral expansion of a symmetric operator. -/
theorem apply_eq_sum (x : Y) :
    A x = ∑ i, (eigVal hA i * ⟪eigBasis hA i, x⟫) • eigBasis hA i := by
  conv_lhs => rw [← (eigBasis hA).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, apply_eigBasis, (eigBasis hA).repr_apply_apply, smul_smul, mul_comm]

/-- The **symmetric square root** of a symmetric operator. -/
noncomputable def symSqrt : Y →ₗ[ℝ] Y :=
  ∑ i, Real.sqrt (eigVal hA i) • rankOne (eigBasis hA i)

theorem symSqrt_apply (x : Y) :
    symSqrt hA x = ∑ i, (Real.sqrt (eigVal hA i) * ⟪eigBasis hA i, x⟫) • eigBasis hA i := by
  simp only [symSqrt, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, rankOne_apply,
    smul_smul]

theorem symSqrt_eigBasis (j : Fin (Module.finrank ℝ Y)) :
    symSqrt hA (eigBasis hA j) = Real.sqrt (eigVal hA j) • eigBasis hA j := by
  rw [symSqrt_apply hA]
  rw [Finset.sum_eq_single j]
  · have h1 : ⟪eigBasis hA j, eigBasis hA j⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, (eigBasis hA).orthonormal.1 j]
      norm_num
    rw [h1, mul_one]
  · intro i _ hij
    rw [(eigBasis hA).orthonormal.2 hij]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem symSqrt_symm : (symSqrt hA).IsSymmetric := by
  intro x y
  simp only [symSqrt, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, rankOne_symm]

/-- **The square root squares to the operator.** -/
theorem symSqrt_symSqrt (hpos : ∀ x, 0 ≤ ⟪A x, x⟫) (x : Y) :
    symSqrt hA (symSqrt hA x) = A x := by
  rw [symSqrt_apply hA x, map_sum, apply_eq_sum hA x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, symSqrt_eigBasis hA, smul_smul]
  congr 1
  have hsq : Real.sqrt (eigVal hA i) * Real.sqrt (eigVal hA i) = eigVal hA i :=
    Real.mul_self_sqrt (eigVal_nonneg hA hpos i)
  linear_combination (⟪eigBasis hA i, x⟫) * hsq

end SymmetricSqrt

end HTGeometry.ConstraintMotiveRelativity
