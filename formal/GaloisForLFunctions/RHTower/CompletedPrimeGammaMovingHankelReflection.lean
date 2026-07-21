import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingHankel
import GaloisForLFunctions.HTGeometry.ReflectionFoldedMomentGerm

/-!
# Reflection of the moving completed prime--Gamma Hankel family

The completed logarithmic derivative is anti-invariant under `s ↦ 1 - s`.  After translating at
an arbitrary base point and applying the normalized divided difference, that anti-invariance
becomes ordinary reflection of the moving moment germ:

`G_(1-sigma)(z) = G_sigma(-z)`.

Consequently every even Taylor moment, every finite moving Hankel matrix, and every leading
determinant is exactly invariant under `sigma ↦ 1 - sigma`.  This is an unconditional source-value
relation.  It does not assert determinant positivity or RH, but it reduces any continuation of the
positive far-right anchor to the center to one half of the real axis; every obstruction is paired
by reflection.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The translated completed relative trace is anti-reflected in its base and spectral variables. -/
theorem completedMovingRelativeTrace_one_sub (sigma z : ℂ) :
    completedMovingRelativeTrace (1 - sigma) z =
      -completedMovingRelativeTrace sigma (-z) := by
  change HTGeometry.affineRelativeTrace (logDeriv xi) (1 - sigma) z =
    -HTGeometry.affineRelativeTrace (logDeriv xi) sigma (-z)
  exact HTGeometry.affineRelativeTrace_reflection
    (logDeriv xi) 1 sigma z logDeriv_xi_reciprocity

/-- Exact reflection of the moving normalized moment germ. -/
theorem completedMovingMomentGerm_one_sub (sigma z : ℂ) :
    completedMovingMomentGerm (1 - sigma) z =
      completedMovingMomentGerm sigma (-z) := by
  change HTGeometry.reflectionFoldedMomentGerm (logDeriv xi) (1 - sigma) z =
    HTGeometry.reflectionFoldedMomentGerm (logDeriv xi) sigma (-z)
  exact HTGeometry.reflectionFoldedMomentGerm_reflection
    (logDeriv xi) 1 sigma z logDeriv_xi_reciprocity

/-- Every moving moment-germ jet has the parity forced by base reflection. -/
theorem iteratedDeriv_completedMovingMomentGerm_one_sub
    (k : ℕ) (sigma : ℂ) :
    iteratedDeriv k (completedMovingMomentGerm (1 - sigma)) 0 =
      (-1 : ℂ) ^ k * iteratedDeriv k (completedMovingMomentGerm sigma) 0 := by
  change iteratedDeriv k
      (HTGeometry.reflectionFoldedMomentGerm (logDeriv xi) (1 - sigma)) 0 =
    (-1 : ℂ) ^ k * iteratedDeriv k
      (HTGeometry.reflectionFoldedMomentGerm (logDeriv xi) sigma) 0
  exact HTGeometry.iteratedDeriv_reflectionFoldedMomentGerm_reflection
    (logDeriv xi) 1 sigma logDeriv_xi_reciprocity k

/-- All even Taylor moments of the moving source are invariant under base reflection. -/
theorem analyticTraceMoments_completedMovingMomentGerm_one_sub
    (k : ℕ) (sigma : ℂ) :
    analyticTraceMoments (completedMovingMomentGerm (1 - sigma)) k =
      analyticTraceMoments (completedMovingMomentGerm sigma) k := by
  rw [analyticTraceMoments, analyticTraceMoments,
    iteratedDeriv_completedMovingMomentGerm_one_sub]
  have heven : (-1 : ℂ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven, one_mul]

/-- The complete finite moving Hankel matrix is reflection invariant. -/
theorem completedMovingHankelMatrix_one_sub (n : ℕ) (sigma : ℂ) :
    completedMovingHankelMatrix n (1 - sigma) =
      completedMovingHankelMatrix n sigma := by
  ext i j
  exact analyticTraceMoments_completedMovingMomentGerm_one_sub
    ((i : ℕ) + (j : ℕ)) sigma

/-- **Moving determinant reflection law.** Every leading completed prime--Gamma Hankel determinant
is symmetric about the functional-equation center. -/
theorem completedMovingHankelDet_one_sub (n : ℕ) (sigma : ℂ) :
    completedMovingHankelDet n (1 - sigma) =
      completedMovingHankelDet n sigma := by
  rw [completedMovingHankelDet, completedMovingHankelDet,
    completedMovingHankelMatrix_one_sub]

end

end RHTower
