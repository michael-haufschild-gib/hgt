import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewAdjointDomainInclusion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDirichletScrewFactorization

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- Reverse inclusion in Suzuki's natural-domain identity: every Dirichlet-domain vector has
compressed screw derivative output in the maximal adjoint domain. -/
theorem suzukiDirichletDerivative_domain_le_screwNaturalDomain
    (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).domain ≤
      suzukiDirichletScrewNaturalDomain a := by
  intro v hv
  let vd : (suzukiDirichletDerivative a).domain := ⟨v, hv⟩
  let d : SuzukiApertureZeroMean a := suzukiDirichletZeroMeanOutputLM a vd
  let z : SuzukiApertureZeroMean a := (-Complex.I) • d
  have hzdom :=
    I_smul_suzukiScrewZeroMeanOperator_mem_dirichletAdjointDomain a z
  have heq0 : Complex.I • suzukiScrewZeroMeanOperator a z =
      suzukiScrewZeroMeanOperator a d := by
    dsimp only [z]
    rw [map_smul]
    simp [smul_smul, Complex.I_mul_I]
  have heq : Complex.I •
        ((suzukiScrewZeroMeanOperator a z : SuzukiApertureZeroMean a) :
          SuzukiApertureIntervalL2 a.1) =
      ((suzukiScrewZeroMeanOperator a d : SuzukiApertureZeroMean a) :
        SuzukiApertureIntervalL2 a.1) :=
    congrArg Subtype.val heq0
  have hafter : suzukiScrewAfterDirichletLM a vd ∈
      (suzukiDirichletDerivative a).adjoint.domain := by
    rw [suzukiScrewAfterDirichletLM_apply]
    rw [← heq]
    exact hzdom
  refine ⟨⟨vd, hafter⟩, ?_⟩
  rfl

/-- Suzuki 2026, Lemma 3.1 domain equality: the honest natural domain of
`D† Gₐ D` is exactly `H₀¹(-a,a)`, not merely contained in it. -/
theorem suzukiDirichletScrewNaturalDomain_eq_H01
    (a : SuzukiPositiveAperture) :
    suzukiDirichletScrewNaturalDomain a =
      (suzukiDirichletDerivative a).domain := by
  apply le_antisymm
  · exact suzukiDirichletScrewNaturalDomain_le_H01 a
  · exact suzukiDirichletDerivative_domain_le_screwNaturalDomain a

end RHTower

end
