import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaPhaseMonotonicity
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIFlowBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Quantitative phase-coordinate bounds

Sharp pointwise phase-slope bands integrate to global two-sided secant bounds.  Each physical
Jacobi phase is thus not merely injective: its distortion between any ordered arclength pair is
controlled explicitly by the curvature endpoint ratio.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

structure OrderedArclengthPair where
  left : ℝ
  right : ℝ
  ordered : left ≤ right

theorem regionINonnegativePhase_secant_bounds
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (I : OrderedArclengthPair) :
    (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2 * (I.right - I.left) ≤
        physicalJacobiPhase k₀ P.val J I.right - physicalJacobiPhase k₀ P.val J I.left ∧
      physicalJacobiPhase k₀ P.val J I.right - physicalJacobiPhase k₀ P.val J I.left ≤
        (k₀ : ℝ) *
          (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2 *
            (I.right - I.left) := by
  have hdiff : Differentiable ℝ (physicalJacobiPhase k₀ P.val J) := fun x =>
    (physicalJacobiPhase_hasDerivAt k₀ P.val J x).differentiableAt
  have hlow : ∀ x, (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2 ≤
      deriv (physicalJacobiPhase k₀ P.val J) x := by
    intro x
    rw [(physicalJacobiPhase_hasDerivAt k₀ P.val J x).deriv]
    exact regionINonnegativePhaseSlope_lower k₀ P J x
  have hupp : ∀ x, deriv (physicalJacobiPhase k₀ P.val J) x ≤
      (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2 := by
    intro x
    rw [(physicalJacobiPhase_hasDerivAt k₀ P.val J x).deriv]
    exact regionINonnegativePhaseSlope_upper k₀ P J x
  exact ⟨mul_sub_le_image_sub_of_le_deriv hdiff hlow I.ordered,
    image_sub_le_mul_sub_of_deriv_le hdiff hupp I.ordered⟩

theorem regionINegativePhase_secant_bounds
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (I : OrderedArclengthPair) :
    (k₀ : ℝ) *
          (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2 *
            (I.right - I.left) ≤
        physicalJacobiPhase k₀ P.val J I.right - physicalJacobiPhase k₀ P.val J I.left ∧
      physicalJacobiPhase k₀ P.val J I.right - physicalJacobiPhase k₀ P.val J I.left ≤
        (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2 *
          (I.right - I.left) := by
  have hdiff : Differentiable ℝ (physicalJacobiPhase k₀ P.val J) := fun x =>
    (physicalJacobiPhase_hasDerivAt k₀ P.val J x).differentiableAt
  have hlow : ∀ x, (k₀ : ℝ) *
        (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2 ≤
      deriv (physicalJacobiPhase k₀ P.val J) x := by
    intro x
    rw [(physicalJacobiPhase_hasDerivAt k₀ P.val J x).deriv]
    exact regionINegativePhaseSlope_lower k₀ P J x
  have hupp : ∀ x, deriv (physicalJacobiPhase k₀ P.val J) x ≤
      (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2 := by
    intro x
    rw [(physicalJacobiPhase_hasDerivAt k₀ P.val J x).deriv]
    exact regionINegativePhaseSlope_upper k₀ P J x
  exact ⟨mul_sub_le_image_sub_of_le_deriv hdiff hlow I.ordered,
    image_sub_le_mul_sub_of_deriv_le hdiff hupp I.ordered⟩

theorem regionIIPhase_secant_bounds
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (I : OrderedArclengthPair) :
    ((k₀ : ℝ) * regionIIGamma P / 2 +
          ((k₀ : ℝ) * regionIINu P / 2) / regionIIAmplitudeUpper P) *
          (I.right - I.left) ≤
        regionIIPhysicalPhase k₀ P J I.right - regionIIPhysicalPhase k₀ P J I.left ∧
      regionIIPhysicalPhase k₀ P J I.right - regionIIPhysicalPhase k₀ P J I.left ≤
        (k₀ : ℝ) * (regionIIGamma P + regionIINu P) / 2 *
          (I.right - I.left) := by
  have hdiff : Differentiable ℝ (regionIIPhysicalPhase k₀ P J) := fun x =>
    (regionIIPhysicalPhase_hasDerivAt k₀ P J x).differentiableAt
  have hlow : ∀ x, (k₀ : ℝ) * regionIIGamma P / 2 +
        ((k₀ : ℝ) * regionIINu P / 2) / regionIIAmplitudeUpper P ≤
      deriv (regionIIPhysicalPhase k₀ P J) x := by
    intro x
    rw [(regionIIPhysicalPhase_hasDerivAt k₀ P J x).deriv]
    exact regionIICompiledPhaseSlope_lower k₀ P J x
  have hupp : ∀ x, deriv (regionIIPhysicalPhase k₀ P J) x ≤
      (k₀ : ℝ) * (regionIIGamma P + regionIINu P) / 2 := by
    intro x
    rw [(regionIIPhysicalPhase_hasDerivAt k₀ P J x).deriv]
    exact regionIICompiledPhaseSlope_upper k₀ P J x
  exact ⟨mul_sub_le_image_sub_of_le_deriv hdiff hlow I.ordered,
    image_sub_le_mul_sub_of_deriv_le hdiff hupp I.ordered⟩

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
