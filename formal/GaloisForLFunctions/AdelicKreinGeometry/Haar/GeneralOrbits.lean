import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicOrbits

/-!
# Cyclic Haar projections of arbitrary affine columns

Translation-orbit pairings depend only on slope. Every affine column therefore has the same reciprocal-denominator projection norm as its pure dilation column.
-/

open Module Finset
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- Translation-orbit pairings depend only on the column's slope. -/
theorem affine_column_translation_orbit_pairing {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (g : AffineGroupQ) (c : ℚ) (i j : ℕ) :
    kernelColumnPairing k
      (((kernelColumnRepresentation k (translation c)) ^ i) (kernelColumnPoint k g))
      (((kernelColumnRepresentation k (translation c)) ^ j) (kernelColumnPoint k g)) =
      k (translation (((j : ℚ) - (i : ℚ)) * (c / affSlope g))) := by
  rw [rational_affine_translation_pow, rational_affine_translation_pow,
    kernelColumnRepresentation_point, kernelColumnRepresentation_point,
    kernelColumnPairing_point_left hk]
  change k ((translation ((i : ℚ) * c) * g)⁻¹ *
    (translation ((j : ℚ) * c) * g)) = _
  rw [translation_mul_affine_eq, translation_mul_affine_eq, mul_inv_rev,
    mul_assoc, inv_mul_cancel_left, translation_inv_mul]
  congr 2
  ring

/-- Every affine column has the same cyclic Haar orthogonality as the dilation of its slope. -/
theorem integer_successor_affine_orbit_orthonormal {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k) (g : AffineGroupQ) (c : ℚ)
    {i j : ℕ} (hi : i < (c / affSlope g).den) (hj : j < (c / affSlope g).den) :
    kernelColumnPairing k
      (((kernelColumnRepresentation k (translation c)) ^ i) (kernelColumnPoint k g))
      (((kernelColumnRepresentation k (translation c)) ^ j) (kernelColumnPoint k g)) =
      if i = j then 1 else 0 := by
  let a : ℚˣ := Units.mk0 (affSlope g) (affSlope_ne_zero g)
  have h := integer_successor_translation_orbit_orthonormal hk hs a c hi hj
  rw [dilation_column_translation_orbit_pairing hk] at h
  rw [affine_column_translation_orbit_pairing hk]
  exact h

/-- The cyclic fixed component of any affine column has reciprocal orbit norm. -/
theorem integer_successor_affine_projection_pairing {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ) :
    kernelColumnPairing k
      (translationFixedProjection k hp b (kernelColumnPoint k g))
      (translationFixedProjection k hp b (kernelColumnPoint k g)) =
      ((b / affSlope g).den : ℂ)⁻¹ := by
  let a : ℚˣ := Units.mk0 (affSlope g) (affSlope_ne_zero g)
  have hm : (b / affSlope g).den ≠ 0 := Nat.ne_of_gt (b / affSlope g).den_pos
  have hg := kernelColumnPairing_projection_average hk (translation b)
    (kernel_translation_locally_periodic hp b) (kernelColumnPoint k g) (kernelColumnPoint k g)
    hm (kernel_translation_column_period hp b g)
  have ha := kernelColumnPairing_projection_average hk (translation b)
    (kernel_translation_locally_periodic hp b) (kernelColumnPoint k (dilation a))
    (kernelColumnPoint k (dilation a)) hm
    (by simpa only [affSlope_dilation, a, Units.val_mk0] using
      kernel_translation_column_period hp b (dilation a))
  have hterm (j : ℕ) : kernelColumnPairing k (kernelColumnPoint k g)
      (((kernelColumnRepresentation k (translation b)) ^ j) (kernelColumnPoint k g)) =
      kernelColumnPairing k (kernelColumnPoint k (dilation a))
        (((kernelColumnRepresentation k (translation b)) ^ j) (kernelColumnPoint k (dilation a))) := by
    have hg' := affine_column_translation_orbit_pairing hk g b 0 j
    have ha' := dilation_column_translation_orbit_pairing hk a b 0 j
    simpa only [pow_zero, Module.End.one_apply] using hg'.trans ha'.symm
  simp only [hterm] at hg
  exact hg.trans (ha.symm.trans (integer_successor_projection_pairing hk hs hp b a))

#print axioms integer_successor_affine_orbit_orthonormal
#print axioms integer_successor_affine_projection_pairing
end GaloisForLFunctions.AdelicKreinGeometry
