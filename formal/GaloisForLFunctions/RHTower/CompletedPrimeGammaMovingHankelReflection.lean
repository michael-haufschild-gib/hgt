import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingHankel

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
  rw [completedMovingRelativeTrace, completedMovingRelativeTrace]
  have hz := logDeriv_xi_reciprocity (sigma - z * Complex.I)
  have hs := logDeriv_xi_reciprocity sigma
  have harg : 1 - (sigma - z * Complex.I) =
      1 - sigma + z * Complex.I := by ring
  rw [harg] at hz
  have hnegarg : sigma + -z * Complex.I = sigma - z * Complex.I := by ring
  rw [hnegarg, hz, hs]
  ring

/-- Normalized divided difference converts the anti-reflection `-T(-z)` into reflection of the
evenized germ.  The center case uses the exact derivative convention built into `dslope`. -/
private theorem normalizedTraceMomentGerm_neg_comp_neg (T : ℂ → ℂ) (z : ℂ) :
    normalizedTraceMomentGerm (fun w => -T (-w)) z =
      normalizedTraceMomentGerm T (-z) := by
  rw [normalizedTraceMomentGerm, normalizedTraceMomentGerm]
  by_cases hz : z = 0
  · subst z
    rw [neg_zero, dslope_same, dslope_same]
    have hcomp := iteratedDeriv_comp_neg 1 T (0 : ℂ)
    have hneg := iteratedDeriv_neg 1 (fun w : ℂ => T (-w)) (0 : ℂ)
    rw [iteratedDeriv_one, iteratedDeriv_one, neg_zero] at hcomp
    rw [iteratedDeriv_one, iteratedDeriv_one] at hneg
    have hfun : (fun w : ℂ => -T (-w)) = -(fun w : ℂ => T (-w)) := rfl
    rw [hfun, hneg, hcomp]
    ring
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [dslope_of_ne _ hz, dslope_of_ne _ hnz,
      slope_def_module, slope_def_module]
    simp only [neg_zero]
    ring

/-- Exact reflection of the moving normalized moment germ. -/
theorem completedMovingMomentGerm_one_sub (sigma z : ℂ) :
    completedMovingMomentGerm (1 - sigma) z =
      completedMovingMomentGerm sigma (-z) := by
  have href : completedMovingRelativeTrace (1 - sigma) =
      fun w => -completedMovingRelativeTrace sigma (-w) := by
    funext w
    exact completedMovingRelativeTrace_one_sub sigma w
  rw [completedMovingMomentGerm, completedMovingMomentGerm, href]
  exact normalizedTraceMomentGerm_neg_comp_neg
    (completedMovingRelativeTrace sigma) z

/-- Every moving moment-germ jet has the parity forced by base reflection. -/
theorem iteratedDeriv_completedMovingMomentGerm_one_sub
    (k : ℕ) (sigma : ℂ) :
    iteratedDeriv k (completedMovingMomentGerm (1 - sigma)) 0 =
      (-1 : ℂ) ^ k * iteratedDeriv k (completedMovingMomentGerm sigma) 0 := by
  have href : completedMovingMomentGerm (1 - sigma) =
      fun z => completedMovingMomentGerm sigma (-z) := by
    funext z
    exact completedMovingMomentGerm_one_sub sigma z
  rw [href, iteratedDeriv_comp_neg]
  simp

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
