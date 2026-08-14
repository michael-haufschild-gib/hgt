import GaloisForLFunctions.RHTower.SuzukiDirichletFormCore

/-!
# The honest unbounded product `D† G_a D`

Suzuki writes `B_a = D† G_a D` and declares its domain to be `H₀¹(-a,a)`.  For unbounded
operators the product domain is mathematical content, not notation.  This module constructs the
literal natural composition domain

`{v ∈ D(D) | G_a(Dv) ∈ D(D†)}`

and only then forms the `LinearPMap` composition.  Thus the later proof that this domain is all of
`H₀¹` cannot be hidden in a definition.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- On the exact graph domain, the closed Dirichlet operator is `i` times the derivative
coordinate recovered by the inverse primitive. -/
theorem suzukiDirichletDerivative_apply_eq_I_smul_coordinate
    (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    suzukiDirichletDerivative a v =
      Complex.I • suzukiDirichletDomainDerivativeCoordinate a v := by
  let e := suzukiDirichletInverseRangeEquiv a
  let w : SuzukiApertureH01 a := suzukiDirichletDomainToH01 a v
  let f0 : SuzukiApertureZeroMean a := e.symm w
  obtain ⟨hmem, happly⟩ := suzukiDirichletDerivative_apply_inverse a f0
  have he : suzukiDirichletInverseCLM a f0 = v.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply w)
  let vf : (suzukiDirichletDerivative a).domain :=
    ⟨suzukiDirichletInverseCLM a f0, hmem⟩
  have hvf : vf = v := Subtype.ext he
  rw [← hvf]
  have hcoord : suzukiDirichletDomainDerivativeCoordinate a vf =
      (f0 : SuzukiApertureIntervalL2 a.1) := by
    apply suzukiAperturePrimitiveCLM_injective a
    change suzukiAperturePrimitive a.1
        (suzukiDirichletDomainDerivativeCoordinate a vf) =
      suzukiAperturePrimitive a.1 (f0 : SuzukiApertureIntervalL2 a.1)
    rw [suzukiAperturePrimitive_dirichletDomainDerivativeCoordinate]
    rfl
  rw [hcoord]
  exact happly

/-- Dirichlet output with its proved zero-mean range retained as a subtype. -/
def suzukiDirichletZeroMeanOutputLM (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).domain →ₗ[ℂ] SuzukiApertureZeroMean a where
  toFun v := ⟨suzukiDirichletDerivative a v, by
    rw [← suzukiDirichletDerivative_range a]
    exact ⟨v, rfl⟩⟩
  map_add' v w := by
    apply Subtype.ext
    exact LinearPMap.map_add (suzukiDirichletDerivative a) v w
  map_smul' c v := by
    apply Subtype.ext
    exact LinearPMap.map_smul (suzukiDirichletDerivative a) c v

@[simp] theorem coe_suzukiDirichletZeroMeanOutputLM
    (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    (suzukiDirichletZeroMeanOutputLM a v : SuzukiApertureIntervalL2 a.1) =
      suzukiDirichletDerivative a v := rfl

/-- Bounded screw compression after the unbounded Dirichlet derivative, as a linear map on the
Dirichlet graph domain. -/
def suzukiScrewAfterDirichletLM (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).domain →ₗ[ℂ]
      SuzukiApertureIntervalL2 a.1 :=
  (SuzukiApertureZeroMean a).subtype.comp
    ((suzukiScrewZeroMeanOperator a).toLinearMap.comp
      (suzukiDirichletZeroMeanOutputLM a))

@[simp] theorem suzukiScrewAfterDirichletLM_apply
    (a : SuzukiPositiveAperture)
    (v : (suzukiDirichletDerivative a).domain) :
    suzukiScrewAfterDirichletLM a v =
      (suzukiScrewZeroMeanOperator a
        (suzukiDirichletZeroMeanOutputLM a v) : SuzukiApertureIntervalL2 a.1) := rfl

/-- Exact subtype of Dirichlet-domain vectors on which the screw output belongs to `D(D†)`. -/
def suzukiDirichletScrewAdjointCore (a : SuzukiPositiveAperture) :
    Submodule ℂ (suzukiDirichletDerivative a).domain :=
  (suzukiDirichletDerivative a).adjoint.domain.comap
    (suzukiScrewAfterDirichletLM a)

/-- Injective inclusion of the natural product core into ambient interval `L²`. -/
def suzukiDirichletScrewNaturalInclusionLM (a : SuzukiPositiveAperture) :
    suzukiDirichletScrewAdjointCore a →ₗ[ℂ] SuzukiApertureIntervalL2 a.1 :=
  (suzukiDirichletDerivative a).domain.subtype.comp
    (suzukiDirichletScrewAdjointCore a).subtype

theorem suzukiDirichletScrewNaturalInclusionLM_injective
    (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiDirichletScrewNaturalInclusionLM a) := by
  intro v w hvw
  exact Subtype.ext (Subtype.ext hvw)

/-- Natural domain of `D† G_a D`, embedded in ambient `L²(-a,a)`. -/
def suzukiDirichletScrewNaturalDomain (a : SuzukiPositiveAperture) :
    Submodule ℂ (SuzukiApertureIntervalL2 a.1) :=
  LinearMap.range (suzukiDirichletScrewNaturalInclusionLM a)

/-- The natural product core and its ambient range are linearly equivalent. -/
def suzukiDirichletScrewNaturalDomainEquiv (a : SuzukiPositiveAperture) :
    suzukiDirichletScrewAdjointCore a ≃ₗ[ℂ]
      suzukiDirichletScrewNaturalDomain a :=
  LinearEquiv.ofInjective (suzukiDirichletScrewNaturalInclusionLM a)
    (suzukiDirichletScrewNaturalInclusionLM_injective a)

/-- Bounded-middle factor on the ambient natural composition domain. -/
def suzukiScrewAfterDirichletNaturalLM (a : SuzukiPositiveAperture) :
    suzukiDirichletScrewNaturalDomain a →ₗ[ℂ]
      SuzukiApertureIntervalL2 a.1 :=
  (suzukiScrewAfterDirichletLM a).comp
    ((suzukiDirichletScrewAdjointCore a).subtype.comp
      (suzukiDirichletScrewNaturalDomainEquiv a).symm.toLinearMap)

/-- `G_a D` restricted to its honest adjoint-composition domain. -/
def suzukiScrewAfterDirichletNatural (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →ₗ.[ℂ] SuzukiApertureIntervalL2 a.1 where
  domain := suzukiDirichletScrewNaturalDomain a
  toFun := suzukiScrewAfterDirichletNaturalLM a

theorem suzukiScrewAfterDirichletNatural_mem_adjointDomain
    (a : SuzukiPositiveAperture)
    (v : (suzukiScrewAfterDirichletNatural a).domain) :
    suzukiScrewAfterDirichletNatural a v ∈
      (suzukiDirichletDerivative a).adjoint.domain := by
  let w : suzukiDirichletScrewAdjointCore a :=
    (suzukiDirichletScrewNaturalDomainEquiv a).symm v
  have happly : suzukiScrewAfterDirichletNatural a v =
      suzukiScrewAfterDirichletLM a w := rfl
  rw [happly]
  exact w.property

/-- **Literal natural unbounded product** `D† G_a D`.  No domain equality is assumed. -/
def suzukiDirichletScrewOperator (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →ₗ.[ℂ] SuzukiApertureIntervalL2 a.1 :=
  (suzukiDirichletDerivative a).adjoint.comp
    (suzukiScrewAfterDirichletNatural a)
    (suzukiScrewAfterDirichletNatural_mem_adjointDomain a)

@[simp] theorem suzukiDirichletScrewOperator_domain
    (a : SuzukiPositiveAperture) :
    (suzukiDirichletScrewOperator a).domain =
      suzukiDirichletScrewNaturalDomain a := by
  rfl

/-- The natural product domain is unconditionally contained in the literal Dirichlet domain. -/
theorem suzukiDirichletScrewNaturalDomain_le_H01
    (a : SuzukiPositiveAperture) :
    suzukiDirichletScrewNaturalDomain a ≤
      (suzukiDirichletDerivative a).domain := by
  rintro v ⟨w, hw⟩
  rw [← hw]
  exact w.1.property

end RHTower

end
