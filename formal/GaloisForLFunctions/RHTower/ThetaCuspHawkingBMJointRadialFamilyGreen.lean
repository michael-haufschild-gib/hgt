import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointRadialFamilyAdmission

/-! Actual radial weak derivatives and the constructed joint response extend to nonseparated energy families. -/
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointWave
noncomputable section

/-- Radial integration by parts holds against every angular L² vector, without angular regularity. -/
theorem radialGreen_angularL2 (f : RadialCore) (g : D4BMModularCore.Space) (u : jointDomain) :
    inner ℂ (l2SeparatedProduct (radialValue f) g) ((u : JointEnergySpace) 1) +
      inner ℂ (l2SeparatedProduct (radialDerivative f) g) (jointEmbedding u) = 0 := by
  let L : D4BMModularCore.Space →L[ℂ] SpatialSpace :=
    l2SeparatedProductContinuousBilinear (radialValue f)
  let D : D4BMModularCore.Space →L[ℂ] SpatialSpace :=
    l2SeparatedProductContinuousBilinear (radialDerivative f)
  have hz : L.adjoint ((u : JointEnergySpace) 1)+D.adjoint (jointEmbedding u) = 0 := by
    apply angularValue_total
    intro k
    rw [inner_add_right,L.adjoint_inner_right,D.adjoint_inner_right]
    exact radialConstraint_completed f k u
  change inner ℂ (L g) ((u : JointEnergySpace) 1)+inner ℂ (D g) (jointEmbedding u) = 0
  rw [← L.adjoint_inner_right,← D.adjoint_inner_right,← inner_add_right,hz,inner_zero_right]

private def radialFamilyGreenMap (u : jointDomain) : FamilyPacketSpace →L[ℂ] ℂ :=
  (innerSL ℂ ((u : JointEnergySpace) 1)).comp
    ((radialFamilySlot 0).comp (PiLp.proj 2 (fun _ : Fin 3 => RadialAngularSpace) 0)) +
  (innerSL ℂ (jointEmbedding u)).comp
    ((radialFamilySlot 0).comp (PiLp.proj 2 (fun _ : Fin 3 => RadialAngularSpace) 1))

private theorem radialFamilyGreenMap_pure (u : jointDomain) (f : RadialCore) (g : AngularEnergy) :
    radialFamilyGreenMap u (radialAngularPacket f g) = 0 := by
  change inner ℂ ((u : JointEnergySpace) 1) (radialFamilySlot 0 (bochnerL2Product (radialValue f) g)) +
    inner ℂ (jointEmbedding u) (radialFamilySlot 0 (bochnerL2Product (radialDerivative f) g)) = 0
  rw [radialFamilySlot_pure,radialFamilySlot_pure]
  have hc := congrArg (starRingEnd ℂ)
    (radialGreen_angularL2 f (D4BMModularCore.embedding g) u)
  simpa only [map_add,map_zero,inner_conj_symm] using! hc

/-- The completed radial gradient is the actual weak derivative against every smooth compact
radial angular-energy family, with the original radial measure. -/
theorem radialGreen_radialEnergyFamily (h : RadialEnergyFamily) (u : jointDomain) :
    inner ℂ (radialFamilySlot 0 h.value) ((u : JointEnergySpace) 1) +
      inner ℂ (radialFamilySlot 0 h.radial) (jointEmbedding u) = 0 := by
  obtain ⟨ι,b,_⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := AngularEnergy)
  have he : radialFamilyGreenMap u h.packet = 0 := by
    have hmem : h.packet ∈ (radialFamilyGreenMap u).ker := by
      apply (radialFamilyGreenMap u).isClosed_ker.mem_of_tendsto (h.projectedPacket_tendsto b)
      apply Eventually.of_forall
      intro s
      change radialFamilyGreenMap u (h.projectedPacket b s) = 0
      rw [h.projectedPacket_sum,map_sum]
      simp only [radialFamilyGreenMap_pure,Finset.sum_const_zero]
    exact hmem
  have hc := congrArg (starRingEnd ℂ) he
  change (starRingEnd ℂ) (inner ℂ ((u : JointEnergySpace) 1) (radialFamilySlot 0 h.value) +
    inner ℂ (jointEmbedding u) (radialFamilySlot 0 h.radial)) = (starRingEnd ℂ) 0 at hc
  simpa only [map_add,map_zero,inner_conj_symm] using hc

/-- The actual constructed right-half-plane inverse obeys the extended original weak equation. -/
theorem jointWaveResponse_radialEnergyFamily (w : ℂ) (hw : 0 < w.re) (F : SpatialSpace)
    (h : RadialEnergyFamily) :
    let u := jointWaveResponse w hw F
    inner ℂ (radialFamilySlot 0 h.radial) ((u : JointEnergySpace) 1) +
      inner ℂ (radialFamilySlot 1 h.weighted) ((u : JointEnergySpace) 2) +
      inner ℂ (radialFamilySlot 2 h.weighted) ((u : JointEnergySpace) 3) +
      w^2*inner ℂ (radialFamilySlot 0 h.value) (jointEmbedding u) =
      inner ℂ (radialFamilySlot 0 h.value) F :=
  jointWaveSolution_radialEnergyFamily w F _ (jointWaveResponse_spec w hw F) h

end
end RHTower.D4BMJointWave
