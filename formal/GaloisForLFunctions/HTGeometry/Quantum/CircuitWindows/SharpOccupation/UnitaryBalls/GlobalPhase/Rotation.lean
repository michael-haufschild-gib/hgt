import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.GlobalPhase.PhaseCubes
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.CircularArcRange

/-! # The scalar-phase cost of projecting a fixed-unitary target -/
open Set MeasureTheory Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

variable {I : Type*} [Fintype I]

/-- Absolute packets admitting some common phase rotation into A. -/
def rotations (A : Set (UnitAddTorus I)) := {z : UnitAddTorus I | ∃ u : UnitAddCircle, z+(fun _ => u)∈A}

omit [Fintype I] in
theorem closed_rotations {A : Set (UnitAddTorus I)} (hA : IsClosed A) : IsClosed (rotations A) := by
  let B := (fun p : UnitAddTorus I × UnitAddCircle => p.1+(fun _ => p.2)) ⁻¹' A
  have hc : IsClosed B := hA.preimage (continuous_fst.add (continuous_pi fun _ => continuous_snd))
  have he : rotations A = Prod.fst '' B := by
    ext x
    exact ⟨fun ⟨u,hu⟩ => ⟨(x,u),hu,rfl⟩,fun ⟨⟨_,u⟩,hu,rfl⟩ => ⟨u,hu⟩⟩
  rw [he]
  exact (hc.isCompact.image continuous_fst).isClosed

/-- Every scalar orbit meeting A spends at least r of one turn in its
side-r thickening. Haar invariance turns this into a volume estimate. -/
theorem rotation_volume {A : Set (UnitAddTorus I)} (hA : IsClosed A) (r : Icc (0:ℝ) 1) :
    ENNReal.ofReal r*volume (rotations A) ≤ volume (phaseCube A r) := by
  let B := phaseCube A r
  let P := (fun p : UnitAddTorus I × UnitAddCircle => p.1+(fun _ => p.2)) ⁻¹' B
  have hP : MeasurableSet P := (closed_phaseCube hA r).measurableSet.preimage
    (continuous_fst.add (continuous_pi fun _ => continuous_snd)).measurable
  have hf (x : UnitAddTorus I) (hx : x∈rotations A) :
      ENNReal.ofReal r ≤ volume ((Prod.mk x) ⁻¹' P) := by
    obtain ⟨u,hu⟩ := hx
    let c : UnitAddCircle := ((r.val/2:ℝ):UnitAddCircle)-u
    have hm := (measurePreserving_add_right volume c).measure_preimage
      (isClosed_forwardUnitArc r).measurableSet.nullMeasurableSet
    rw [volume_forwardUnitArc_full r] at hm
    rw [←hm]
    apply measure_mono
    rintro t ⟨w,hw,he⟩
    change (w:UnitAddCircle)=t+(((r.val/2:ℝ):UnitAddCircle)-u) at he
    change x+(fun _ => t)∈phaseCube A r
    refine ⟨(x+(fun _ => u),fun _ => w-r.val/2),⟨hu,?_⟩,?_⟩
    · intro _ _
      exact ⟨by linarith only [hw.1],by linarith only [hw.2]⟩
    · funext i
      change (x i+u)+((w-r.val/2:ℝ):UnitAddCircle)=x i+t
      rw [AddCircle.coe_sub,he]
      abel
  have havg : (∫⁻ x : UnitAddTorus I, volume ((Prod.mk x) ⁻¹' P))=volume B := by
    rw [←Measure.prod_apply hP,Measure.prod_apply_symm hP]
    have ht (t : UnitAddCircle) : volume ((fun x : UnitAddTorus I => (x,t)) ⁻¹' P)=volume B :=
      (measurePreserving_add_right volume (fun _ : I => t)).measure_preimage
        (closed_phaseCube hA r).measurableSet.nullMeasurableSet
    simp only [ht,lintegral_const,UnitAddCircle.measure_univ,mul_one]
  rw [←havg,←Measure.restrict_apply_univ (s:=rotations A),←lintegral_const,←lintegral_indicator (closed_rotations hA).measurableSet]
  apply lintegral_mono
  intro x
  by_cases hx : x∈rotations A
  · simpa only [indicator_of_mem hx] using hf x hx
  · simp only [indicator_of_notMem hx,zero_le]

#print axioms rotation_volume
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
