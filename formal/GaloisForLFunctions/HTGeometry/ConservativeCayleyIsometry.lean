import GaloisForLFunctions.HTGeometry.ConservativeDissipativeResolvent

/-!
# Reversible conservative Cayley transport

The existing conservative midpoint step is a surjective Hilbert isometry,
not merely norm preserving. Negating the original bounded operator supplies
its exact inverse. This promotes the conservative–dissipative resolvent API to
bundled isometric transport while retaining its constructed generator and
unconditional inverse, for every nonnegative step size.
-/

open scoped NNReal InnerProductSpace Ring

namespace GaloisForLFunctions.HTGeometry.SchafferExl

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The reverse conservative shift is the numerator of the forward midpoint step. -/
theorem implicitShift_neg_conservative (A : E →L[𝕜] E) (t : ℝ≥0) :
    implicitShift (-A) (0 : E →L[𝕜] E) t =
      1 + ((t : ℝ) : 𝕜) • generator A (0 : E →L[𝕜] E) := by
  simp [implicitShift, generator, conservative, damping, smul_sub]
  module

/-- Conservative transport is the ratio of the reverse and forward implicit shifts. -/
theorem cayleyStep_conservative_shift_ratio (A : E →L[𝕜] E) (t : ℝ≥0) :
    cayleyStep A (0 : E →L[𝕜] E) t =
      implicitShift (-A) (0 : E →L[𝕜] E) t *
        (implicitShift A (0 : E →L[𝕜] E) t)⁻¹ʳ := by
  rw [cayleyStep, implicitStep, implicitShift_neg_conservative]

/-- Every conservative step is invertible, including in infinite dimension. -/
theorem cayleyStep_conservative_isUnit (A : E →L[𝕜] E) (t : ℝ≥0) :
    IsUnit (cayleyStep A (0 : E →L[𝕜] E) t) := by
  rw [cayleyStep_conservative_shift_ratio]
  exact (implicitShift_isUnit (-A) (0 : E →L[𝕜] E) t).mul
    (implicitShift_isUnit A (0 : E →L[𝕜] E) t).ringInverse

/-- Reversing the conservative generator exactly reverses the midpoint step. -/
theorem cayleyStep_neg_mul_conservative (A : E →L[𝕜] E) (t : ℝ≥0) :
    cayleyStep (-A) (0 : E →L[𝕜] E) t * cayleyStep A (0 : E →L[𝕜] E) t = 1 := by
  simp only [cayleyStep_conservative_shift_ratio, neg_neg, mul_assoc]
  rw [Ring.inverse_mul_cancel_left _ _ (implicitShift_isUnit (-A) (0 : E →L[𝕜] E) t),
    Ring.mul_inverse_cancel _ (implicitShift_isUnit A (0 : E →L[𝕜] E) t)]

/-- The inverse identity also holds in the opposite order. -/
theorem cayleyStep_mul_neg_conservative (A : E →L[𝕜] E) (t : ℝ≥0) :
    cayleyStep A (0 : E →L[𝕜] E) t * cayleyStep (-A) (0 : E →L[𝕜] E) t = 1 := by
  simpa only [neg_neg] using cayleyStep_neg_mul_conservative (-A) t

/-- The already constructed conservative Cayley step as a Hilbert-space isometry. -/
def conservativeCayleyIsometry (A : E →L[𝕜] E) (t : ℝ≥0) : E ≃ₗᵢ[𝕜] E where
  toLinearEquiv :=
    (ContinuousLinearEquiv.ofUnit (cayleyStep_conservative_isUnit A t).unit).toLinearEquiv
  norm_map' x := by
    change ‖((cayleyStep_conservative_isUnit A t).unit : E →L[𝕜] E) x‖ = ‖x‖
    rw [(cayleyStep_conservative_isUnit A t).unit_spec]
    nlinarith [cayleyStep_conservative_energy (F := E) A t x,
      norm_nonneg (cayleyStep A (0 : E →L[𝕜] E) t x), norm_nonneg x]

@[simp]
theorem conservativeCayleyIsometry_apply (A : E →L[𝕜] E) (t : ℝ≥0) (x : E) :
    conservativeCayleyIsometry A t x = cayleyStep A (0 : E →L[𝕜] E) t x := by
  change ((cayleyStep_conservative_isUnit A t).unit : E →L[𝕜] E) x = _
  rw [(cayleyStep_conservative_isUnit A t).unit_spec]

/-- The inverse isometry is obtained by negating the original unrestricted operator. -/
theorem conservativeCayleyIsometry_symm (A : E →L[𝕜] E) (t : ℝ≥0) :
    (conservativeCayleyIsometry A t).symm = conservativeCayleyIsometry (-A) t := by
  ext x
  apply (conservativeCayleyIsometry A t).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp only [conservativeCayleyIsometry_apply]
  have h := congrArg (fun T : E →L[𝕜] E => T x) (cayleyStep_mul_neg_conservative A t)
  simpa only [mul_apply_eq_comp, one_apply_eq_self]
    using h.symm

/-- All Gram pairings are preserved by conservative midpoint transport. -/
theorem cayleyStep_conservative_inner (A : E →L[𝕜] E) (t : ℝ≥0) (x y : E) :
    inner 𝕜 (cayleyStep A (0 : E →L[𝕜] E) t x)
      (cayleyStep A (0 : E →L[𝕜] E) t y) = inner 𝕜 x y := by
  simpa only [conservativeCayleyIsometry_apply] using
    (conservativeCayleyIsometry A t).inner_map_map x y

end

end GaloisForLFunctions.HTGeometry.SchafferExl
