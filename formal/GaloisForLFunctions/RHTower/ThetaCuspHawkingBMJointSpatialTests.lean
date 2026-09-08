import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointRadialGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointAngularTests
import GaloisForLFunctions.RHTower.L2HilbertTensorProduct

/-! Total separated tests for the actual joint spatial L² space, with no angular spectral substitution. -/
open MeasureTheory Set Filter Topology
open scoped TensorProduct
namespace RHTower.D4BMJointWave
noncomputable section

abbrev SpatialSpace := Lp ℂ 2 (radialMeasure.prod D4BMModularCore.measure)

private theorem separated_total (u : SpatialSpace)
    (hu : ∀ f : RadialSpace, ∀ g : D4BMModularCore.Space,
      inner ℂ (l2SeparatedProduct f g) u = 0) : u = 0 := by
  have hclosed : IsClosed {v : SpatialSpace | inner ℂ v u = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have ht : ∀ v : RadialSpace ⊗[ℂ] D4BMModularCore.Space,
      inner ℂ (l2TensorToProduct v) u = 0 := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => exact hu f g
    | add x y hx hy => simp only [map_add,inner_add_left,hx,hy,add_zero]
  have hr : Set.range (l2TensorToProduct (μ := radialMeasure)
      (ν := D4BMModularCore.measure)) ⊆ {v : SpatialSpace | inner ℂ v u = 0} := by
    rintro _ ⟨v,rfl⟩
    exact ht v
  exact inner_self_eq_zero.mp (closure_minimal hr hclosed (l2TensorToProduct_denseRange u))

private theorem restricted_separated_total {A : Type*} (T : A → D4BMModularCore.Space)
    (hT : ∀ v, (∀ a, inner ℂ (T a) v = 0) → v = 0) (u : SpatialSpace)
    (hu : ∀ f : RadialCore, ∀ a, inner ℂ (l2SeparatedProduct (radialValue f) (T a)) u = 0) :
    u = 0 := by
  have hright (f : RadialCore) (g : D4BMModularCore.Space) :
      inner ℂ (l2SeparatedProduct (radialValue f) g) u = 0 := by
    let L : D4BMModularCore.Space →L[ℂ] SpatialSpace :=
      l2SeparatedProductContinuousBilinear (radialValue f)
    have hz : L.adjoint u = 0 := hT _ (fun a => by
      rw [L.adjoint_inner_right]
      exact hu f a)
    change inner ℂ (L g) u = 0
    rw [← L.adjoint_inner_right,hz,inner_zero_right]
  apply separated_total u
  intro f g
  let L : RadialSpace →L[ℂ] SpatialSpace := l2SeparatedProductContinuousBilinear.flip g
  have hz : L.adjoint u = 0 := radialValue_total _ (fun a => by
    rw [L.adjoint_inner_right]
    exact hright a g)
  change inner ℂ (L f) u = 0
  rw [← L.adjoint_inner_right,hz,inner_zero_right]

/-- Smooth radial tests times full smooth modular fields separate the joint spatial space. -/
theorem spatialValue_total (u : SpatialSpace)
    (hu : ∀ f : RadialCore, ∀ g : D4BMModularCore.CoreField,
      inner ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.fieldVector g)) u = 0) :
    u = 0 :=
  restricted_separated_total _ angularValue_total u hu

/-- Smooth radial tests times actual local angular mass tests also separate the joint space. -/
theorem spatialMass_total (u : SpatialSpace)
    (hu : ∀ f : RadialCore, ∀ g : D4BMModularCore.InteriorTest,
      inner ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.massTest g)) u = 0) :
    u = 0 :=
  restricted_separated_total _ angularMass_total u hu

end
end RHTower.D4BMJointWave
