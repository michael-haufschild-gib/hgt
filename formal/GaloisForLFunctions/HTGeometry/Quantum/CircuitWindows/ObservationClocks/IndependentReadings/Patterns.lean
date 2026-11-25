import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ObservationClocks.IndependentReadings.Rates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.PhaseRectangles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.UniformWindows

/-! # Joint frequencies of successes and failures at translated phase clocks -/

open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.ObservationClocks.IndependentReadings
open SpectralJets.BoundaryField.NestedPrefixes
open GaloisForLFunctions.BiarithmeticGeometry.SigmaProductVolume
noncomputable section
variable {I : Type} [Fintype I] {n : ℕ}
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

private theorem rectangle_measurable (A : Fin n→Set (UnitAddTorus I)) (hm : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (rectangle (I:=fun _ => I) A) := by
  let P (j : Fin n) (z : Rows n I→UnitAddCircle) (i : I) := z ⟨j,i⟩
  have he : rectangle A=⋂ j, P j ⁻¹' A j := Set.ext fun _ => mem_iInter.symm
  rw [he]
  exact MeasurableSet.iInter fun j => (hm j).preimage (measurable_pi_lambda _ fun i => measurable_pi_apply ⟨j,i⟩)

/-- A success and a failure have the same boundary. The product argument
therefore applies to mixed records of closed targets and their complements. -/
private theorem rectangle_boundary (A : Fin n→Set (UnitAddTorus I))
    (hb : ∀ j, volume (frontier (A j))=0) : volume (frontier (rectangle (I:=fun _ => I) A))=0 := by
  classical
  let P (j : Fin n) (z : Rows n I→UnitAddCircle) (i : I) := z ⟨j,i⟩
  let X := fun (_ : Fin n) (_ : I) => UnitAddCircle
  have hP (j : Fin n) : MeasurePreserving (P j) volume volume :=
    (measurePreserving_eval (fun _ : Fin n => (volume : Measure (I→UnitAddCircle))) j).comp (volume_preserving_curry X)
  have hn (j : Fin n) : volume (P j ⁻¹' frontier (A j))=0 := by
    rw [(hP j).measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet,hb]
  apply measure_mono_null _ (measure_iUnion_null hn)
  intro z hz
  have hcl : z∈rectangle (fun j => closure (A j)) := closure_minimal
    (fun _ h j => subset_closure (h j)) (rectangle_closed _ fun _ => isClosed_closure) hz.1
  by_contra hnz
  let V := ⋂ j, P j ⁻¹' interior (A j)
  have ho : IsOpen V := isOpen_iInter_of_finite fun j =>
    isOpen_interior.preimage (continuous_pi fun i => continuous_apply (Sigma.mk (β:=fun _ : Fin n => I) j i))
  have hsub : V⊆rectangle A := fun _ h j => interior_subset (mem_iInter.mp h j)
  apply hz.2 (interior_maximal hsub ho ?_)
  apply mem_iInter.mpr
  intro j
  by_contra hj
  exact hnz (mem_iUnion.mpr ⟨j,hcl j,hj⟩)

/-- The fraction of time scales satisfying one prescribed test per row is
the product of their Haar probabilities. Each row can start at a different
point on the orbit, and the long observation window can move arbitrarily. -/
theorem joint_pattern_fraction (f : I→ℝ) (z : ℝ)
    (hi : RationallyIndependentFrequency (rowFrequency n f z))
    (o : Fin n→ℝ) (A : Fin n→Set (UnitAddTorus I))
    (hm : ∀ j, MeasurableSet (A j)) (hb : ∀ j, volume (frontier (A j))=0) (a : ℝ→ℝ) :
    let B := {t : ℝ | ∀ j, finiteClockPhasePoint f (o j+rate z j.val*t)∈A j}
    Tendsto (fun T => volume.real (B∩Icc (a T) (a T+T))/T) atTop (𝓝 (∏ j, volume.real (A j))) := by
  intro B
  let shift (j : Fin n) (x : UnitAddTorus I) := x+finiteClockPhasePoint f (o j)
  let V (j : Fin n) := shift j ⁻¹' A j
  have hc (j : Fin n) : Continuous (shift j) := continuous_id.add continuous_const
  have hp (j : Fin n) : MeasurePreserving (shift j) volume volume := measurePreserving_add_right _ _
  have hv (j : Fin n) : volume (frontier (V j))=0 := by
    apply measure_mono_null ((hc j).frontier_preimage_subset _) 
    rw [(hp j).measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet,hb]
  have mass (j : Fin n) : volume.real (V j)=volume.real (A j) := (hp j).measureReal_preimage (hm j).nullMeasurableSet
  have he : finiteClockPhasePoint (rowFrequency n f z) ⁻¹' rectangle V=B := by
    ext t
    change (∀ j : Fin n, shift j (fun i => finiteClockPhasePoint (rowFrequency n f z) t ⟨j,i⟩)∈A j) ↔ _
    have h (j : Fin n) : shift j (fun i => finiteClockPhasePoint (rowFrequency n f z) t ⟨j,i⟩)=
        finiteClockPhasePoint f (o j+rate z j.val*t) := by
      funext i
      change ((_:ℝ):UnitAddCircle)+((_:ℝ):UnitAddCircle)=((_:ℝ):UnitAddCircle)
      rw [←AddCircle.coe_add]
      congr 1
      dsimp only [rowFrequency]
      ring
    simp only [h,B,mem_setOf_eq]
  have h := PhaseBoundary.uniform_phase_fraction _ hi (rectangle V)
    (rectangle_measurable V fun j => (hm j).preimage (hc j).measurable) (rectangle_boundary V hv) a
  simpa only [he,rectangle_mass,mass] using h

#print axioms joint_pattern_fraction
end
end GaloisForLFunctions.HTGeometry.ObservationClocks.IndependentReadings
