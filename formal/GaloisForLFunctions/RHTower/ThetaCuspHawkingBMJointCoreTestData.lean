import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCoreOperator
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointRadialFamilyData

/-! Actual second radial tests and the full native modular Green identity. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RHTower.D4BMModularCore
/-- Full modular Green identity for any original compact quotient test and completed energy field. -/
theorem CoreField.completed_green (g : CoreField) (u : energyDomain) :
    inner ℂ (derivativeVector g 1) ((u : EnergySpace) 1)+
      inner ℂ (derivativeVector g Complex.I) ((u : EnergySpace) 2) =
      -inner ℂ (fieldVector g.laplacian) (embedding u) := by
  have hcore : g.planarTest.toChartTest.coreField = g := by
    have he := g.planarTest_periodize
    change g.planarTest.toChartTest.coreField.field = g.field at he
    have ext (a b : CoreField) (h : a.field = b.field) : a = b := by
      cases a
      cases b
      cases h
      rfl
    exact ext _ _ he
  have hl : g.planarTest.laplaceVector = fieldVector g.laplacian := by
    apply Lp.ext
    have h := g.planarTest.laplaceVector_coe
    rw [g.planarTest_periodize] at h
    exact h.trans (core_field_memLp g.laplacian.field g.laplacian.smooth g.laplacian.compact).coeFn_toLp.symm
  have he := g.planarTest.completed_green u
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at he
  change inner ℂ (derivativeVector g.planarTest.toChartTest.coreField 1) ((u : EnergySpace) 1)+
    inner ℂ (derivativeVector g.planarTest.toChartTest.coreField Complex.I) ((u : EnergySpace) 2) = _ at he
  rwa [hcore,hl] at he
end RHTower.D4BMModularCore

namespace RHTower.D4BMJointWave
/-- Differentiation stays inside the original compact radial test domain. -/
def RadialCore.differentiate (f : RadialCore) : RadialCore where
  field := deriv f.field
  smooth := (contDiff_infty_iff_deriv.mp f.smooth).2
  compact := f.compact.deriv
  support := tsupport_deriv_subset.trans f.support

/-- Multiplication by the actual geometric angular weight preserves the radial core. -/
def RadialCore.angularWeighted (f : RadialCore) : RadialCore where
  field t := angularWeight t*f.field t
  smooth := angularWeight_smooth.mul f.smooth
  compact := f.compact.mul_left
  support := (tsupport_mul_subset_right).trans f.support

theorem RadialCore.differentiate_value (f : RadialCore) :
    radialValue f.differentiate = radialDerivative f := rfl

theorem RadialCore.angularWeighted_value (f : RadialCore) :
    radialValue f.angularWeighted = radialWeightedValue f := by
  apply Lp.ext
  exact (radialValue_ae _).trans (radialWeightedValue_ae f).symm

/-- The second geometric weight in the transposed angular term is the original squared coefficient. -/
theorem RadialCore.angularWeighted_twice_ae (f : RadialCore) :
    radialWeightedValue f.angularWeighted =ᵐ[radialMeasure]
      fun t => angularWeight t^(2 : ℕ)*f.field t := by
  apply (radialWeightedValue_ae _).trans
  filter_upwards with t
  change angularWeight t*(angularWeight t*f.field t) = _
  ring
end RHTower.D4BMJointWave
end
