import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoreTransposition

/-! Literal differential action of the original joint Friedrichs operator on its full smooth core. -/
open MeasureTheory
namespace RHTower.D4BMJointWave
open D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original mass-minus-Laplacian expression on a separated compact radial/modular core field. -/
def jointCoreDifferential (f : RadialCore) (g : CoreField) : SpatialSpace :=
  l2SeparatedProduct (radialValue f) (fieldVector g)-
    l2SeparatedProduct (radialDerivative f.differentiate) (fieldVector g)-
    l2SeparatedProduct (radialWeightedValue f.angularWeighted) (fieldVector g.laplacian)

/-- The actual differential expression represents the full joint energy form on every completed field. -/
theorem jointCoreDifferential_inner (f : RadialCore) (g : CoreField) (u : jointDomain) :
    inner ℂ (jointCoreDifferential f g) (jointEmbedding u) =
      inner ℂ (⟨jointGraph f g,jointGraph_mem f g⟩ : jointDomain) u := by
  rw [joint_inner_decomposition]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,jointCoreDifferential,inner_sub_left]
  have hr := joint_radial_second_green f g u
  have ha := joint_angular_green f.angularWeighted g u
  rw [RadialCore.angularWeighted_value] at ha
  change inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) (jointEmbedding u)-
    inner ℂ (l2SeparatedProduct (radialDerivative f.differentiate) (fieldVector g)) (jointEmbedding u)-
    inner ℂ (l2SeparatedProduct (radialWeightedValue f.angularWeighted) (fieldVector g.laplacian)) (jointEmbedding u) =
    inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) (jointEmbedding u)+
    (inner ℂ (l2SeparatedProduct (radialDerivative f) (fieldVector g)) ((u : JointEnergySpace) 1)+
      (inner ℂ (l2SeparatedProduct (radialWeightedValue f) (derivativeVector g 1)) ((u : JointEnergySpace) 2)+
        inner ℂ (l2SeparatedProduct (radialWeightedValue f) (derivativeVector g Complex.I)) ((u : JointEnergySpace) 3)))
  linear_combination -hr-ha

/-- Every original separated smooth core field lies in the actual unbounded operator domain,
and the operator returns its literal mass-minus-radial-and-modular-Laplacian expression. -/
theorem jointEnergyOperator_core (f : RadialCore) (g : CoreField) :
    ∃ hmem : l2SeparatedProduct (radialValue f) (fieldVector g) ∈ jointEnergyOperator.domain,
      jointEnergyOperator ⟨l2SeparatedProduct (radialValue f) (fieldVector g),hmem⟩ =
        jointCoreDifferential f g := by
  let x : jointDomain := ⟨jointGraph f g,jointGraph_mem f g⟩
  let y := jointCoreDifferential f g
  have hadj : jointEmbedding.adjoint y = x := by
    apply ext_inner_right ℂ
    intro u
    rw [jointEmbedding.adjoint_inner_left]
    exact jointCoreDifferential_inner f g u
  have hc : formEmbeddingCovariance jointEmbedding y = jointEmbedding x := congrArg jointEmbedding hadj
  have h := friedrichsFormOperator_apply_covariance jointEmbedding jointEmbedding_injective jointEmbedding_dense y
  have hmem : jointEmbedding x ∈ jointEnergyOperator.domain := hc ▸ h.1
  refine ⟨hmem,?_⟩
  change jointEnergyOperator ⟨jointEmbedding x,hmem⟩ = y
  have hx : (⟨jointEmbedding x,hmem⟩ : jointEnergyOperator.domain) =
      ⟨formEmbeddingCovariance jointEmbedding y,h.1⟩ := Subtype.ext hc.symm
  exact (congrArg jointEnergyOperator hx).trans h.2

end
end RHTower.D4BMJointWave
