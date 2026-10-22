import GaloisForLFunctions.HTGeometry.ClosedGraphTransformAdjoint
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDirichletDerivative

/-!
# Exact maximal adjoint domain of Suzuki's Dirichlet derivative

For Suzuki's literal realization

`D = (i ι) V⁻¹`,

where `V` is the zero-mean primitive and `ι : L²₀ → L²` is inclusion, this module specializes
the general closed-graph-transform adjoint theorem.  It proves, without declaring `H¹` by fiat,
that the maximal-adjoint domain is exactly the range equation

`-i P₀ y ∈ ran(V†)`.

This is the precise weak-Sobolev condition used in the product `D† G_a D`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- The bounded output coordinate `i ι` has adjoint `-i P₀`. -/
theorem suzukiDirichletOutputCLM_adjoint
    (a : SuzukiPositiveAperture) :
    (suzukiDirichletOutputCLM a).adjoint =
      (-Complex.I) • suzukiApertureZeroMeanProjection a := by
  rw [suzukiDirichletOutputCLM,
    ContinuousLinearMap.adjoint.map_smulₛₗ,
    (SuzukiApertureZeroMean a).adjoint_subtypeL]
  simp only [Complex.conj_I, suzukiApertureZeroMeanProjection]

/-- Exact weak-regularity characterization of Suzuki's maximal Dirichlet adjoint. -/
theorem mem_suzukiDirichletDerivative_adjoint_domain_iff
    (a : SuzukiPositiveAperture) (y : SuzukiApertureIntervalL2 a.1) :
    y ∈ (suzukiDirichletDerivative a).adjoint.domain ↔
      (-Complex.I) • suzukiApertureZeroMeanProjection a y ∈
        (suzukiDirichletInverseAdjointCLM a).range := by
  rw [suzukiDirichletDerivative,
    closedGraphTransform_mem_adjoint_domain_iff
      (SuzukiApertureZeroMean a)
      (suzukiDirichletInverseCLM a)
      (suzukiDirichletOutputCLM a)
      (suzukiDirichletInverseCLM_injective a)
      (dense_suzukiDirichletInverseCLM_range a),
    suzukiDirichletOutputCLM_adjoint,
    suzukiDirichletInverseAdjointCLM_eq_adjoint]
  simp only [smul_apply]

/-- Exact action of `D†`: solving the projected reverse-primitive equation determines its value. -/
theorem suzukiDirichletDerivative_adjoint_apply_of_inverseAdjoint_eq
    (a : SuzukiPositiveAperture) (y z : SuzukiApertureIntervalL2 a.1)
    (hz : suzukiDirichletInverseAdjointCLM a z =
      (-Complex.I) • suzukiApertureZeroMeanProjection a y)
    (hydom : y ∈ (suzukiDirichletDerivative a).adjoint.domain) :
    (suzukiDirichletDerivative a).adjoint ⟨y, hydom⟩ = z := by
  apply closedGraphTransform_adjoint_apply_of_eq_adjoint
    (SuzukiApertureZeroMean a)
    (suzukiDirichletInverseCLM a)
    (suzukiDirichletOutputCLM a)
    (suzukiDirichletInverseCLM_injective a)
    (dense_suzukiDirichletInverseCLM_range a)
  rw [← suzukiDirichletInverseAdjointCLM_eq_adjoint,
    suzukiDirichletOutputCLM_adjoint]
  simpa only [smul_apply] using hz

end RHTower

end
