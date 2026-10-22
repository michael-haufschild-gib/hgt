import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalDistributionEquation

/-!
Full periodized chart tests belong to the actual modular Friedrichs operator domain, with its exact differential action.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
noncomputable section

/-- The actual value-minus-Laplacian vector represents the full modular form. -/
theorem PlanarChartTest.operator_form (g : PlanarChartTest) (h : energyDomain) :
    inner ℂ g.toChartTest.energyTest h =
      inner ℂ (embedding g.toChartTest.energyTest - g.laplaceVector) (embedding h) := by
  rw [energy_inner_decomposition,g.completed_green,inner_sub_left,sub_eq_add_neg]

private theorem PlanarChartTest.operator_adjoint (g : PlanarChartTest) :
    embedding.adjoint (embedding g.toChartTest.energyTest - g.laplaceVector) =
      g.toChartTest.energyTest := by
  apply ext_inner_right ℂ
  intro h
  rw [embedding.adjoint_inner_left,g.operator_form]

/-- Every actual periodized smooth compact planar test belongs to the original
Friedrichs operator domain, including tests crossing modular seams. -/
theorem PlanarChartTest.mem_energyOperator_domain (g : PlanarChartTest) :
    embedding g.toChartTest.energyTest ∈ energyOperator.domain := by
  have h := (friedrichsFormOperator_apply_covariance embedding embedding_injective
    embedding_dense (embedding g.toChartTest.energyTest - g.laplaceVector)).1
  simpa only [energyOperator,formEmbeddingCovariance,ContinuousLinearMap.comp_apply,
    g.operator_adjoint] using h

/-- The original operator acts on full periodized tests by the literal
`1-Delta_H`, with every modular translate retained. -/
theorem PlanarChartTest.energyOperator_apply (g : PlanarChartTest) :
    energyOperator ⟨embedding g.toChartTest.energyTest,g.mem_energyOperator_domain⟩ =
      embedding g.toChartTest.energyTest - g.laplaceVector := by
  have h := (friedrichsFormOperator_apply_covariance embedding embedding_injective
    embedding_dense (embedding g.toChartTest.energyTest - g.laplaceVector)).2
  have he : formEmbeddingCovariance embedding
      (embedding g.toChartTest.energyTest - g.laplaceVector) =
      embedding g.toChartTest.energyTest := by
    simp only [formEmbeddingCovariance,ContinuousLinearMap.comp_apply,g.operator_adjoint]
  convert h using 1
  congr 1
  exact Subtype.ext he.symm

end
end RHTower.D4BMModularCore
