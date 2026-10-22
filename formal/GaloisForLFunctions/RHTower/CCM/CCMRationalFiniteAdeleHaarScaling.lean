import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleHaar
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicScalingAction

/-!
# Haar-character law for rational scaling on finite adeles

Diagonal inverse rational multiplication is bundled as an additive homeomorphism of the actual
finite adele ring.  Haar uniqueness then gives the exact, unconditional covariance equation for
the normalized Bruhat integral.  Computing this topological Haar character arithmetically is the
remaining product-formula theorem; it is not replaced here by a premise or proxy functional.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions
namespace RHTower

/-- Inverse diagonal rational multiplication on finite adeles as an additive homeomorphism. -/
def ccmRationalFiniteAdeleInverseScalingEquiv
    (k : CCMRationalAdelicScaling) :
    CCMRationalFiniteAdele ≃ₜ+ CCMRationalFiniteAdele :=
  ContinuousAddEquiv.mulLeft (ccmRationalUnitFiniteAdele k.val⁻¹)

@[simp]
theorem ccmRationalFiniteAdeleInverseScalingEquiv_apply
    (k : CCMRationalAdelicScaling) (x : CCMRationalFiniteAdele) :
    ccmRationalFiniteAdeleInverseScalingEquiv k x =
      algebraMap ℚ CCMRationalFiniteAdele
        ((k.val⁻¹ : CCMRationalUnit) : ℚ) * x :=
  rfl

/-- Exact finite-adelic covariance before arithmetic evaluation of the Haar character. -/
theorem ccmRationalFiniteBruhatIntegral_haarCharacter
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalFiniteBruhatSchwartz) :
    (MeasureTheory.addEquivAddHaarChar
        (ccmRationalFiniteAdeleInverseScalingEquiv k) : ℝ) •
        ccmRationalFiniteBruhatIntegral
          (ccmRationalFiniteBruhatScaling k f) =
      ccmRationalFiniteBruhatIntegral f := by
  rw [ccmRationalFiniteBruhatIntegral_apply,
    ccmRationalFiniteBruhatIntegral_apply]
  change (MeasureTheory.addEquivAddHaarChar
      (ccmRationalFiniteAdeleInverseScalingEquiv k) : ℝ) •
      (∫ x, f.1 (ccmRationalFiniteAdeleInverseScalingEquiv k x)
        ∂ccmRationalFiniteAdeleHaar) = _
  have hmap :
      (∫ x, f.1 (ccmRationalFiniteAdeleInverseScalingEquiv k x)
          ∂ccmRationalFiniteAdeleHaar) =
        ∫ y, f.1 y ∂(ccmRationalFiniteAdeleHaar.map
          (ccmRationalFiniteAdeleInverseScalingEquiv k)) :=
    (MeasureTheory.integral_map_equiv
      (ccmRationalFiniteAdeleInverseScalingEquiv k).toHomeomorph.toMeasurableEquiv
      f.1).symm
  rw [hmap]
  have hmeasure := MeasureTheory.addEquivAddHaarChar_smul_map
    ccmRationalFiniteAdeleHaar
    (ccmRationalFiniteAdeleInverseScalingEquiv k)
  have hint := congrArg
    (fun μ : Measure CCMRationalFiniteAdele ↦ ∫ x, f.1 x ∂μ) hmeasure
  change (∫ x, f.1 x ∂
      ((MeasureTheory.addEquivAddHaarChar
          (ccmRationalFiniteAdeleInverseScalingEquiv k) : ENNReal) •
        ccmRationalFiniteAdeleHaar.map
          (ccmRationalFiniteAdeleInverseScalingEquiv k))) = _ at hint
  rw [MeasureTheory.integral_smul_measure] at hint
  simpa using hint

end RHTower
end GaloisForLFunctions
