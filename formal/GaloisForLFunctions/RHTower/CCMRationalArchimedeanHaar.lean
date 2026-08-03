import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import GaloisForLFunctions.RHTower.CCMRationalAdelicScalingAction

/-!
# Archimedean Haar integration for the rational CCM source

This file bundles Lebesgue integration on `𝓢(ℝ, ℂ)` and proves its exact covariance under the
inverse rational pullback used by the adelic scaling action.  The scaling factor is the ordinary
absolute value of the rational unit; it will cancel the finite-adelic Haar modulus by the product
formula.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions
namespace RHTower

/-- Lebesgue integral on the actual rational archimedean Schwartz factor. -/
noncomputable def ccmRationalArchimedeanSchwartzIntegral :
    CCMRationalArchimedeanSchwartz →ₗ[ℂ] ℂ where
  toFun f := ∫ x : ℝ, f x
  map_add' f g := by
    simpa using integral_add f.integrable g.integrable
  map_smul' z f := by
    simpa using integral_smul z (f : ℝ → ℂ)

@[simp]
theorem ccmRationalArchimedeanSchwartzIntegral_apply
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanSchwartzIntegral f = ∫ x : ℝ, f x :=
  rfl

/-- Inverse rational pullback multiplies the archimedean integral by `|k|`. -/
theorem ccmRationalArchimedeanSchwartzIntegral_scaling
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanSchwartzIntegral
        (ccmRationalArchimedeanScaling k f) =
      |(((k.val : CCMRationalUnit) : ℚ) : ℝ)| •
        ccmRationalArchimedeanSchwartzIntegral f := by
  rw [ccmRationalArchimedeanSchwartzIntegral]
  change (∫ x : ℝ,
      f (((((k.val⁻¹ : CCMRationalUnit) : ℚ) : ℝ)) * x)) = _
  rw [Measure.integral_comp_mul_left]
  rw [abs_inv]
  congr 1
  norm_cast
  simp

end RHTower
end GaloisForLFunctions
