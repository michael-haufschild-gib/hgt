import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularTensorQuotient

/-! The full actual forced Einstein equation descends to the original modular tangent-pair quotient. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMMetricReconstruction
noncomputable section

/-- The full actual Einstein variation of the constructed metric at exterior radius. -/
def forcedEinsteinTensor (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ)
    (r : {r : ℝ // 1 < r}) (z : UpperHalfPlane) : Matrix (Fin 4) (Fin 4) ℂ :=
  CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r.val z.im)
    (ofMetricField (forcedMetricField q branch a) (spacetimePoint t r.val z)) (-3)

/-- The actual differential tensor equals the negative complete original source on every exterior chart. -/
theorem forcedEinsteinTensor_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ)
    (r : {r : ℝ // 1 < r}) (z : UpperHalfPlane) :
    forcedEinsteinTensor q branch a t r z = -spacetimeMixedSource q branch a t r.val z := by
  let p : D4BMBackground.ExteriorPoint := ⟨spacetimePoint t r.val z,⟨r.property,z.im_pos⟩⟩
  ext i j
  have h := forcedMetricField_einstein q branch a p i j
  change forcedEinsteinTensor q branch a t r z i j+spacetimeMixedSource q branch a t r.val z i j = 0 at h
  change forcedEinsteinTensor q branch a t r z i j = -spacetimeMixedSource q branch a t r.val z i j
  linear_combination h

/-- The actual Einstein variation transforms on the same modular geometry as its original source. -/
theorem forcedEinsteinTensor_modular (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ)
    (r : {r : ℝ // 1 < r}) (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    modularTensorPullback A z (forcedEinsteinTensor q branch a t r (A • z)) =
      forcedEinsteinTensor q branch a t r z := by
  rw [forcedEinsteinTensor_eq,forcedEinsteinTensor_eq]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => -M)
    (spacetimeMixedSource_modular q branch a t r.val A z)
  simpa only [modularTensorPullback,Matrix.mul_neg,Matrix.neg_mul] using h

/-- Evaluation of the actual differential Einstein tensor on the original modular tangent quotient. -/
def quotientForcedEinstein (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ)
    (r : {r : ℝ // 1 < r}) : ModularTangentQuotient → ℂ :=
  quotientTensorEvaluation (forcedEinsteinTensor q branch a t r)
    (forcedEinsteinTensor_modular q branch a t r)

/-- The descended Einstein variation is the original differential tensor on every representative. -/
theorem quotientForcedEinstein_mk (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ)
    (r : {r : ℝ // 1 < r}) (p : ModularTangentPair) :
    quotientForcedEinstein q branch a t r (Quotient.mk _ p) =
      tensorPair (forcedEinsteinTensor q branch a t r p.point) p.left p.right := rfl

/-- The complete forced mixed Einstein equation holds on every actual quotient tangent pair. -/
theorem quotientForcedEinstein_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ)
    (r : {r : ℝ // 1 < r}) (p : ModularTangentQuotient) :
    quotientForcedEinstein q branch a t r p+quotientMixedSource q branch a t r.val p = 0 := by
  induction p using Quotient.inductionOn with
  | h p =>
    rw [quotientForcedEinstein_mk,quotientMixedSource_mk,forcedEinsteinTensor_eq]
    simp [tensorPair]

end
end RHTower.D4BMModularCore
