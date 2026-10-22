import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewAdjointRange

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- Suzuki 2026, hard domain inclusion: after the Dirichlet phase, every compressed screw
output lies in the maximal Dirichlet-adjoint domain. -/
theorem I_smul_suzukiScrewZeroMeanOperator_mem_dirichletAdjointDomain
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a) :
    Complex.I •
        ((suzukiScrewZeroMeanOperator a f : SuzukiApertureZeroMean a) :
          SuzukiApertureIntervalL2 a.1) ∈
      (suzukiDirichletDerivative a).adjoint.domain := by
  rw [mem_suzukiDirichletDerivative_adjoint_domain_iff]
  refine ⟨suzukiRawScrewAdjointWitness a
    (f : SuzukiApertureIntervalL2 a.1), ?_⟩
  change suzukiDirichletInverseAdjointCLM a
      (suzukiRawScrewAdjointWitness a
        (f : SuzukiApertureIntervalL2 a.1)) = _
  rw [suzukiDirichletInverseAdjointCLM_adjointWitness_eq]
  rw [map_smul, suzukiApertureZeroMeanProjection_apply_of_mem]
  simp [smul_smul, Complex.I_mul_I]

end RHTower

end
