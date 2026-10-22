import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewNaturalDomainEquality

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- Exact maximal-adjoint action on the phase-shifted compressed screw range. -/
theorem suzukiDirichletDerivative_adjoint_apply_I_smul_screw
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a) :
    (suzukiDirichletDerivative a).adjoint
        ⟨Complex.I •
            ((suzukiScrewZeroMeanOperator a f : SuzukiApertureZeroMean a) :
              SuzukiApertureIntervalL2 a.1),
          I_smul_suzukiScrewZeroMeanOperator_mem_dirichletAdjointDomain a f⟩ =
      suzukiRawScrewAdjointWitness a
        (f : SuzukiApertureIntervalL2 a.1) := by
  apply suzukiDirichletDerivative_adjoint_apply_of_inverseAdjoint_eq
  · rw [suzukiDirichletInverseAdjointCLM_adjointWitness_eq]
    rw [map_smul, suzukiApertureZeroMeanProjection_apply_of_mem]
    simp [smul_smul, Complex.I_mul_I]

/-- Exact action of Suzuki's literal natural product `D† Gₐ D` on its now-proved
`H₀¹(-a,a)` domain. -/
theorem suzukiDirichletScrewOperator_apply_eq_adjointWitness
    (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletScrewOperator a).domain) :
    suzukiDirichletScrewOperator a v =
      suzukiRawScrewAdjointWitness a
        (suzukiDirichletDomainDerivativeCoordinate a
          ⟨v.1, by
            rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a]
            exact v.property⟩ : SuzukiApertureIntervalL2 a.1) := by
  let vd : (suzukiDirichletDerivative a).domain :=
    ⟨v.1, by
      rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a]
      exact v.property⟩
  let d : SuzukiApertureZeroMean a :=
    (suzukiDirichletInverseRangeEquiv a).symm
      (suzukiDirichletDomainToH01 a vd)
  let w : suzukiDirichletScrewAdjointCore a :=
    (suzukiDirichletScrewNaturalDomainEquiv a).symm v
  have hw : (w.1 : (suzukiDirichletDerivative a).domain) = vd := by
    apply Subtype.ext
    change w.1.1 = v.1
    exact congrArg Subtype.val
      ((suzukiDirichletScrewNaturalDomainEquiv a).apply_symm_apply v)
  have hd : (d : SuzukiApertureIntervalL2 a.1) =
      suzukiDirichletDomainDerivativeCoordinate a vd := rfl
  have hzero : suzukiDirichletZeroMeanOutputLM a vd = Complex.I • d := by
    apply Subtype.ext
    change suzukiDirichletDerivative a vd =
      Complex.I • (d : SuzukiApertureIntervalL2 a.1)
    rw [suzukiDirichletDerivative_apply_eq_I_smul_coordinate, hd]
  have hafter : suzukiScrewAfterDirichletNatural a v =
      Complex.I •
        ((suzukiScrewZeroMeanOperator a d : SuzukiApertureZeroMean a) :
          SuzukiApertureIntervalL2 a.1) := by
    change suzukiScrewAfterDirichletLM a w = _
    rw [hw, suzukiScrewAfterDirichletLM_apply, hzero, map_smul]
    rfl
  change (suzukiDirichletDerivative a).adjoint
      ⟨suzukiScrewAfterDirichletNatural a v,
        suzukiScrewAfterDirichletNatural_mem_adjointDomain a v⟩ = _
  simpa only [vd, hd, hafter] using
    suzukiDirichletDerivative_adjoint_apply_I_smul_screw a d

end RHTower

end
