import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoreTestData

/-! Transposition of the full original joint wave onto actual compact modular tests. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointWave
open D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def angularGreenConstraint (f : RadialCore) (g : CoreField) : JointEnergySpace →L[ℂ] ℂ :=
  (innerSL ℂ (l2SeparatedProduct (radialValue f) (derivativeVector g 1))).comp
    (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 2)+
  (innerSL ℂ (l2SeparatedProduct (radialValue f) (derivativeVector g Complex.I))).comp
    (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 3)+
  (innerSL ℂ (l2SeparatedProduct (radialWeightedValue f) (fieldVector g.laplacian))).comp
    (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 0)

private theorem angularGreenConstraint_core (f h : RadialCore) (g k : CoreField) :
    angularGreenConstraint f g (jointGraph h k) = 0 := by
  change inner ℂ (l2SeparatedProduct (radialValue f) (derivativeVector g 1))
      (l2SeparatedProduct (radialWeightedValue h) (derivativeVector k 1))+
    inner ℂ (l2SeparatedProduct (radialValue f) (derivativeVector g Complex.I))
      (l2SeparatedProduct (radialWeightedValue h) (derivativeVector k Complex.I))+
    inner ℂ (l2SeparatedProduct (radialWeightedValue f) (fieldVector g.laplacian))
      (l2SeparatedProduct (radialValue h) (fieldVector k)) = 0
  rw [l2SeparatedProduct_inner,l2SeparatedProduct_inner,l2SeparatedProduct_inner,
    radialWeightedValue_symmetric]
  have he := g.completed_green ⟨frameGraph k,frameGraph_mem k⟩
  change inner ℂ (derivativeVector g 1) (derivativeVector k 1)+
    inner ℂ (derivativeVector g Complex.I) (derivativeVector k Complex.I) =
      -inner ℂ (fieldVector g.laplacian) (fieldVector k) at he
  linear_combination (inner ℂ (radialWeightedValue f) (radialValue h))*he

/-- Both angular derivatives transfer to every original smooth compact modular test after graph completion. -/
theorem joint_angular_green (f : RadialCore) (g : CoreField) (u : jointDomain) :
    inner ℂ (l2SeparatedProduct (radialValue f) (derivativeVector g 1)) ((u : JointEnergySpace) 2)+
      inner ℂ (l2SeparatedProduct (radialValue f) (derivativeVector g Complex.I)) ((u : JointEnergySpace) 3)+
      inner ℂ (l2SeparatedProduct (radialWeightedValue f) (fieldVector g.laplacian)) (jointEmbedding u) = 0 := by
  have hs : jointDomain ≤ (angularGreenConstraint f g).toLinearMap.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨h,k⟩,rfl⟩
      exact angularGreenConstraint_core f h g k
    · exact (angularGreenConstraint f g).isClosed_ker
  exact hs u.property

/-- The second radial derivative transfers to the original test, with its physical compact support retained. -/
theorem joint_radial_second_green (f : RadialCore) (g : CoreField) (u : jointDomain) :
    inner ℂ (l2SeparatedProduct (radialDerivative f) (fieldVector g)) ((u : JointEnergySpace) 1)+
      inner ℂ (l2SeparatedProduct (radialDerivative f.differentiate) (fieldVector g)) (jointEmbedding u) = 0 := by
  have h := radialConstraint_completed f.differentiate g u
  change inner ℂ (l2SeparatedProduct (radialValue f.differentiate) (fieldVector g)) ((u : JointEnergySpace) 1)+
    inner ℂ (l2SeparatedProduct (radialDerivative f.differentiate) (fieldVector g)) (jointEmbedding u) = 0 at h
  rwa [RadialCore.differentiate_value] at h

/-- The full original forced wave equation with every derivative on an actual test.
The geometric squared weight, both modular derivatives and all source terms are retained. -/
theorem jointWaveSolution_transposed (w : ℂ) (F : SpatialSpace) (u : jointDomain)
    (hu : JointWaveSolution w F u) (f : RadialCore) (g : CoreField) :
    inner ℂ (l2SeparatedProduct (radialDerivative f.differentiate) (fieldVector g)) (jointEmbedding u)+
      inner ℂ (l2SeparatedProduct (radialWeightedValue f.angularWeighted) (fieldVector g.laplacian)) (jointEmbedding u)-
      w^(2 : ℕ)*inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) (jointEmbedding u) =
      -inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) F := by
  have he := (jointWaveSolution_gradient w F u).mp hu ⟨jointGraph f g,jointGraph_mem f g⟩
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at he
  change inner ℂ (l2SeparatedProduct (radialDerivative f) (fieldVector g)) ((u : JointEnergySpace) 1)+
    (inner ℂ (l2SeparatedProduct (radialWeightedValue f) (derivativeVector g 1)) ((u : JointEnergySpace) 2)+
    inner ℂ (l2SeparatedProduct (radialWeightedValue f) (derivativeVector g Complex.I)) ((u : JointEnergySpace) 3))+
    w^(2 : ℕ)*inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) (jointEmbedding u) =
    inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) F at he
  have ha := joint_angular_green f.angularWeighted g u
  rw [RadialCore.angularWeighted_value] at ha
  have hr := joint_radial_second_green f g u
  linear_combination hr+ha-he

/-- The actual causal response satisfies the complete transposed equation without a supplied PDE premise. -/
theorem jointWaveResponse_transposed (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace)
    (f : RadialCore) (g : CoreField) :
    inner ℂ (l2SeparatedProduct (radialDerivative f.differentiate) (fieldVector g))
        (jointEmbedding (jointWaveResponse w hw F))+
      inner ℂ (l2SeparatedProduct (radialWeightedValue f.angularWeighted) (fieldVector g.laplacian))
        (jointEmbedding (jointWaveResponse w hw F))-
      w^(2 : ℕ)*inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) (jointEmbedding (jointWaveResponse w hw F)) =
      -inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) F :=
  jointWaveSolution_transposed w F _ (jointWaveResponse_spec w hw F) f g

end
end RHTower.D4BMJointWave
