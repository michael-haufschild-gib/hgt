import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.UniformWindows
import Mathlib.Probability.ProductMeasure

/-! # Independent translated tests on finite groups of relative phases -/
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- Test each row of joint phases after adding its fixed phase origin. -/
def phaseRectangle (A : I→Set (UnitAddTorus J)) (z : I→UnitAddTorus J) :
    Set (UnitAddTorus (I×J)) := {x | ∀ i, z i+(fun j => x (i,j)) ∈ A i}

private theorem curry_preserves_haar :
    MeasurePreserving (MeasurableEquiv.curry I J UnitAddCircle) volume volume := by
  refine ⟨(MeasurableEquiv.curry ..).measurable,?_⟩
  simpa only [Measure.infinitePi_eq_pi,volume_pi] using
    Measure.infinitePi_map_curry (fun (_ : I) (_ : J) => (volume : Measure UnitAddCircle))

/-- The rectangle has product Haar mass and null boundary. Both
identities are unchanged by independent translations of its rows. -/
theorem phaseRectangle_spec (A : I→Set (UnitAddTorus J)) (z : I→UnitAddTorus J)
    (hm : ∀ i, MeasurableSet (A i)) (hb : ∀ i, volume (frontier (A i))=0) :
    MeasurableSet (phaseRectangle A z) ∧ volume (frontier (phaseRectangle A z))=0 ∧
      volume.real (phaseRectangle A z)=∏ i, volume.real (A i) := by
  classical
  let B (i : I) := (fun y : UnitAddTorus J => z i+y) ⁻¹' A i
  let e := MeasurableEquiv.curry I J UnitAddCircle
  let S := univ.pi B
  have hB i : MeasurableSet (B i) := (hm i).preimage (measurable_const.add measurable_id)
  have hmass i : volume (B i)=volume (A i) :=
    (measurePreserving_add_left volume (z i)).measure_preimage (hm i).nullMeasurableSet
  have hnull i : volume (frontier (B i))=0 := by
    apply measure_mono_null ((continuous_const.add continuous_id).frontier_preimage_subset (A i))
    exact ((measurePreserving_add_left volume (z i)).measure_preimage
      (s:=frontier (A i)) isClosed_frontier.measurableSet.nullMeasurableSet).trans (hb i)
  have hS : MeasurableSet S := MeasurableSet.univ_pi hB
  have he : phaseRectangle A z=e ⁻¹' S := by
    ext x
    simp only [phaseRectangle,S,mem_setOf_eq,mem_preimage,mem_univ_pi]
    rfl
  have hc : Continuous e := (Homeomorph.piCurry (X:=I) (Y:=J) (Z:=UnitAddCircle)).continuous
  have hp : MeasurePreserving e volume volume := curry_preserves_haar
  rw [he]
  refine ⟨hS.preimage hp.measurable,?_,?_⟩
  · apply measure_mono_null (hc.frontier_preimage_subset S)
    rw [hp.measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet,frontier,
      measure_sdiff interior_subset_closure isOpen_interior.measurableSet.nullMeasurableSet (measure_ne_top _ _)]
    change volume (closure (univ.pi B)) - volume (interior (univ.pi B))=0
    rw [closure_pi_set,interior_pi_set (finite_univ : (univ : Set I).Finite),volume_pi,
      Measure.pi_pi,Measure.pi_pi]
    simp only [measure_closure_of_null_frontier (hnull _),measure_interior_of_null_frontier (hnull _),tsub_self]
  · rw [hp.measureReal_preimage hS.nullMeasurableSet]
    change (volume (univ.pi B)).toReal=_
    rw [volume_pi,Measure.pi_pi,ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun i _ => congrArg ENNReal.toReal (hmass i)

#print axioms phaseRectangle_spec
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
