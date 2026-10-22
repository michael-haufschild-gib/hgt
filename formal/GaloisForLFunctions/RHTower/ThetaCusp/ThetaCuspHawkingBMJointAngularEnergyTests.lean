import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointResponse

/-! The original joint differential domain admits every completed angular energy leg. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointWave
noncomputable section

/-- Exact separated radial lift of all three angular graph components. -/
def radialAngularLift (f : RadialCore) : D4BMModularCore.EnergySpace →L[ℂ] JointEnergySpace :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => SpatialSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 4 => ![
      (l2SeparatedProductContinuousBilinear (radialValue f)).comp
        (PiLp.proj 2 (fun _ : Fin 3 => D4BMModularCore.Space) 0),
      (l2SeparatedProductContinuousBilinear (radialDerivative f)).comp
        (PiLp.proj 2 (fun _ : Fin 3 => D4BMModularCore.Space) 0),
      (l2SeparatedProductContinuousBilinear (radialWeightedValue f)).comp
        (PiLp.proj 2 (fun _ : Fin 3 => D4BMModularCore.Space) 1),
      (l2SeparatedProductContinuousBilinear (radialWeightedValue f)).comp
        (PiLp.proj 2 (fun _ : Fin 3 => D4BMModularCore.Space) 2)] i))

theorem radialAngularLift_apply (f : RadialCore) (g : D4BMModularCore.EnergySpace) :
    radialAngularLift f g = WithLp.toLp 2 ![
      l2SeparatedProduct (radialValue f) (g 0),
      l2SeparatedProduct (radialDerivative f) (g 0),
      l2SeparatedProduct (radialWeightedValue f) (g 1),
      l2SeparatedProduct (radialWeightedValue f) (g 2)] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

theorem radialAngularLift_core (f : RadialCore) (g : D4BMModularCore.CoreField) :
    radialAngularLift f (D4BMModularCore.frameGraph g) = jointGraph f g := by
  rw [radialAngularLift_apply]
  rfl

/-- Continuity in the actual angular graph norm supplies the completed energy leg. -/
theorem radialAngularLift_mem (f : RadialCore) (g : D4BMModularCore.energyDomain) :
    radialAngularLift f g ∈ jointDomain := by
  have hs : D4BMModularCore.energyDomain ≤
      jointDomain.comap (radialAngularLift f).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      change radialAngularLift f (D4BMModularCore.frameGraph a) ∈ jointDomain
      rw [radialAngularLift_core]
      exact jointGraph_mem f a
    · exact (Submodule.isClosed_topologicalClosure _).preimage (radialAngularLift f).continuous
  exact hs g.property

/-- A radial core test tensored with an arbitrary completed angular energy vector. -/
def angularEnergyTest (f : RadialCore) (g : D4BMModularCore.energyDomain) : jointDomain :=
  ⟨radialAngularLift f g,radialAngularLift_mem f g⟩

theorem angularEnergyTest_scalar (f : RadialCore) (g : D4BMModularCore.energyDomain) :
    jointEmbedding (angularEnergyTest f g) =
      l2SeparatedProduct (radialValue f) (D4BMModularCore.embedding g) := rfl

/-- The original joint response equation holds against every completed angular energy leg. -/
theorem jointWaveSolution_angularEnergyTest (w : ℂ) (F : SpatialSpace) (u : jointDomain)
    (hu : JointWaveSolution w F u) (f : RadialCore) (g : D4BMModularCore.energyDomain) :
    inner ℂ (l2SeparatedProduct (radialDerivative f) (D4BMModularCore.embedding g))
        ((u : JointEnergySpace) 1) +
      inner ℂ (l2SeparatedProduct (radialWeightedValue f) ((g : D4BMModularCore.EnergySpace) 1))
        ((u : JointEnergySpace) 2) +
      inner ℂ (l2SeparatedProduct (radialWeightedValue f) ((g : D4BMModularCore.EnergySpace) 2))
        ((u : JointEnergySpace) 3) +
      w^(2 : ℕ)*inner ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.embedding g))
        (jointEmbedding u) =
      inner ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.embedding g)) F := by
  have he := (jointWaveSolution_gradient w F u).mp hu (angularEnergyTest f g)
  simpa only [angularEnergyTest_scalar,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    add_assoc,angularEnergyTest,radialAngularLift_apply] using! he

end
end RHTower.D4BMJointWave
