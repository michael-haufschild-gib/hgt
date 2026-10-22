import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointRadialFamilyData
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointRadialFamilyLift
import GaloisForLFunctions.HTGeometry.HilbertFiniteProjectionL2

/-! Nonseparated smooth radial energy families belong to the original completed joint differential domain. -/
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointWave
noncomputable section

def RadialEnergyFamily.packet (h : RadialEnergyFamily) : FamilyPacketSpace :=
  WithLp.toLp 2 ![h.value,h.radial,h.weighted]

def RadialEnergyFamily.projectedPacket {ι : Type*} (h : RadialEnergyFamily)
    (b : HilbertBasis ι ℂ AngularEnergy) (s : Finset ι) : FamilyPacketSpace :=
  WithLp.toLp 2 ![(hilbertFiniteProjection b s).compLp h.value,
    (hilbertFiniteProjection b s).compLp h.radial,(hilbertFiniteProjection b s).compLp h.weighted]

def radialAngularPacket (f : RadialCore) (g : AngularEnergy) : FamilyPacketSpace :=
  WithLp.toLp 2 ![bochnerL2Product (radialValue f) g,bochnerL2Product (radialDerivative f) g,
    bochnerL2Product (radialWeightedValue f) g]

/-- The finite approximation is an exact finite sum of actual radial tests and angular energy legs. -/
theorem RadialEnergyFamily.projectedPacket_sum {ι : Type*} (h : RadialEnergyFamily)
    (b : HilbertBasis ι ℂ AngularEnergy) (s : Finset ι) :
    h.projectedPacket b s = ∑ i ∈ s, radialAngularPacket (h.coefficient b i) (b i) := by
  apply PiLp.ext
  intro j
  have hs : (∑ i ∈ s, radialAngularPacket (h.coefficient b i) (b i)) j =
      ∑ i ∈ s, radialAngularPacket (h.coefficient b i) (b i) j :=
    map_sum (PiLp.proj 2 (fun _ : Fin 3 => RadialAngularSpace) j :
      FamilyPacketSpace →L[ℂ] RadialAngularSpace) _ s
  rw [hs]
  fin_cases j
  · change (hilbertFiniteProjection b s).compLp h.value =
      ∑ i ∈ s, bochnerL2Product (radialValue (h.coefficient b i)) (b i)
    rw [hilbertFiniteProjection_compLp]
    simp_rw [h.coefficient_value]
  · change (hilbertFiniteProjection b s).compLp h.radial =
      ∑ i ∈ s, bochnerL2Product (radialDerivative (h.coefficient b i)) (b i)
    rw [hilbertFiniteProjection_compLp]
    simp_rw [h.coefficient_radial]
  · change (hilbertFiniteProjection b s).compLp h.weighted =
      ∑ i ∈ s, bochnerL2Product (radialWeightedValue (h.coefficient b i)) (b i)
    rw [hilbertFiniteProjection_compLp]
    simp_rw [h.coefficient_weighted]

/-- Approximation converges in all three Hilbert-valued L² components, including the actual derivative. -/
theorem RadialEnergyFamily.projectedPacket_tendsto {ι : Type*} (h : RadialEnergyFamily)
    (b : HilbertBasis ι ℂ AngularEnergy) :
    Tendsto (h.projectedPacket b) atTop (𝓝 h.packet) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => RadialAngularSpace)).tendsto _ |>.comp
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact hilbertFiniteProjection_compLp_tendsto b h.field h.smooth.continuous h.compact
  · exact hilbertFiniteProjection_compLp_tendsto b (deriv h.field)
      (h.smooth.continuous_deriv (by simp)) h.compact.deriv
  · exact hilbertFiniteProjection_compLp_tendsto b h.weightedField
      h.weightedField_smooth.continuous h.weightedField_compact

/-- The original domain, not an enlarged substitute, admits every smooth compact radial angular-energy family. -/
theorem RadialEnergyFamily.graph_mem (h : RadialEnergyFamily) :
    familyPacketLift h.packet ∈ jointDomain := by
  obtain ⟨ι,b,_⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := AngularEnergy)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (familyPacketLift.continuous.tendsto _ |>.comp (h.projectedPacket_tendsto b))
  apply Eventually.of_forall
  intro s
  change familyPacketLift (h.projectedPacket b s) ∈ jointDomain
  rw [h.projectedPacket_sum,map_sum]
  apply Submodule.sum_mem
  intro i _
  simpa only [radialAngularPacket,familyPacketLift_pure] using
    radialAngularLift_mem (h.coefficient b i) (b i)

/-- Constructed nonseparated test in the actual completed joint domain. -/
def RadialEnergyFamily.energyTest (h : RadialEnergyFamily) : jointDomain :=
  ⟨familyPacketLift h.packet,h.graph_mem⟩

/-- The original response satisfies its complete weak equation against every admitted radial energy family. -/
theorem jointWaveSolution_radialEnergyFamily (w : ℂ) (F : SpatialSpace) (u : jointDomain)
    (hu : JointWaveSolution w F u) (h : RadialEnergyFamily) :
    inner ℂ (radialFamilySlot 0 h.radial) ((u : JointEnergySpace) 1) +
      inner ℂ (radialFamilySlot 1 h.weighted) ((u : JointEnergySpace) 2) +
      inner ℂ (radialFamilySlot 2 h.weighted) ((u : JointEnergySpace) 3) +
      w^(2 : ℕ)*inner ℂ (radialFamilySlot 0 h.value) (jointEmbedding u) =
      inner ℂ (radialFamilySlot 0 h.value) F := by
  have he := (jointWaveSolution_gradient w F u).mp hu h.energyTest
  simpa only [RadialEnergyFamily.energyTest,RadialEnergyFamily.packet,familyPacketLift_apply,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,add_assoc] using! he

end
end RHTower.D4BMJointWave
