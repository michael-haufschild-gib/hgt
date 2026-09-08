import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularMixedTensor

/-! The exact reconstructed metric endpoint values retain the full modular tensor law. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMIngoingCoordinates D4BMGlobalAngularResponse
noncomputable section

private theorem compact_blocks (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (u : ℂ) (z : Fin 2 → ℝ) :
    let s := physicalRate q branch
    let c := s*(s-1)/4
    let E := compactEnvelope (2*s) (a^2) v u
    compactForcedMetric q branch a v u z =
      covectorBlock (E*(2*s*u)) (E*(-2*s/(1+u))) (fullAngularCovector q branch) z+
      covectorBlock (E*(2*c*u*(1-(s+1)*u^2)))
        (E*(2*c*u*(1+(s+1)*u)/(1+u))) (fullSquareCovector q) z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactForcedMetric,covectorBlock] <;> ring

/-- The actual ingoing inverse-radius metric has the full modular tensor law at every radial parameter. -/
theorem compactForcedMetric_modular (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (u : ℂ) (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    modularTensorPullback A z (compactForcedMetric q branch a v u (coordinates (A • z))) =
      compactForcedMetric q branch a v u (coordinates z) := by
  rw [compact_blocks,modularTensorPullback_add,
    covectorBlock_modular A z _ (fullAngularCovector_modular q branch A z),
    covectorBlock_modular A z _ (fullSquareCovector_modular q A z),← compact_blocks]

/-- The exact horizon value transforms by the same actual modular differential. -/
theorem forcedHorizonMetric_modular (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    modularTensorPullback A z (forcedHorizonMetric q branch a v (coordinates (A • z))) =
      forcedHorizonMetric q branch a v (coordinates z) := by
  simpa only [compactForcedMetric_horizon_value] using compactForcedMetric_modular q branch a v 1 A z

/-- The exact radial-angular boundary term retains the full modular tensor law. -/
theorem forcedBoundaryMetric_modular (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    modularTensorPullback A z (forcedBoundaryMetric q branch a v (coordinates (A • z))) =
      forcedBoundaryMetric q branch a v (coordinates z) := by
  simpa only [compactForcedMetric_boundary_value] using compactForcedMetric_modular q branch a v 0 A z

end
end RHTower.D4BMModularCore
