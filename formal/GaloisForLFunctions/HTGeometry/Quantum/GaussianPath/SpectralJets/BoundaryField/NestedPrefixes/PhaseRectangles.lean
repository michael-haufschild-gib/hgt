import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaProductVolume
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateExactOccupation

/-! # Independent phase targets on finitely many registers -/

open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open GaloisForLFunctions.BiarithmeticGeometry.SigmaProductVolume
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
variable {L : Type} [Fintype L] {I : L → Type} [∀ j, Fintype (I j)]

/-- Simultaneous membership in one target per register. -/
def rectangle (A : ∀ j, Set (I j → UnitAddCircle)) : Set (Sigma I → UnitAddCircle) :=
  {z | ∀ j, (fun i => z ⟨j,i⟩) ∈ A j}

theorem rectangle_closed (A : ∀ j, Set (I j → UnitAddCircle)) (hA : ∀ j, IsClosed (A j)) :
    IsClosed (rectangle A) := by
  have he : rectangle A=⋂ j, (fun z i => z ⟨j,i⟩) ⁻¹' A j := Set.ext fun _ => mem_iInter.symm
  rw [he]
  exact isClosed_iInter fun j => (hA j).preimage (continuous_pi fun i => continuous_apply ⟨j,i⟩)

theorem rectangle_mass (A : ∀ j, Set (I j → UnitAddCircle)) :
    volume.real (rectangle A) = ∏ j, volume.real (A j) := by
  let X := fun (j : L) (_ : I j) => UnitAddCircle
  have he : rectangle A=(MeasurableEquiv.piCurry X) ⁻¹' univ.pi A :=
    Set.ext fun _ => ⟨fun h j _ => h j,fun h j => h j (mem_univ _)⟩
  rw [Measure.real,he,volume_preimage_curry,volume_pi_pi,ENNReal.toReal_prod]
  rfl

/-- At a boundary point at least one block is on its target boundary.
The Haar projection onto that block preserves its null measure. -/
theorem rectangle_null_frontier (A : ∀ j, Set (I j → UnitAddCircle))
    (hA : ∀ j, IsClosed (A j)) (hb : ∀ j, volume (frontier (A j))=0) :
    volume (frontier (rectangle A))=0 := by
  classical
  let P (j : L) (z : Sigma I → UnitAddCircle) (i : I j) := z ⟨j,i⟩
  let X := fun (j : L) (_ : I j) => UnitAddCircle
  have hP (j : L) : MeasurePreserving (P j) volume volume :=
    (measurePreserving_eval (fun j : L => (volume : Measure (I j → UnitAddCircle))) j).comp
      (volume_preserving_curry X)
  have hbad (j : L) : volume (P j ⁻¹' frontier (A j))=0 := by
    rw [(hP j).measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet,hb]
  apply measure_mono_null _ (measure_iUnion_null hbad)
  intro z hz
  have hmem := hz.1
  rw [(rectangle_closed A hA).closure_eq] at hmem
  by_contra hn
  let V := ⋂ j, P j ⁻¹' interior (A j)
  have ho : IsOpen V := isOpen_iInter_of_finite fun j =>
    isOpen_interior.preimage (continuous_pi fun i => continuous_apply ⟨j,i⟩)
  have hsub : V⊆rectangle A := fun z h j => interior_subset (mem_iInter.mp h j)
  apply hz.2 (interior_maximal hsub ho ?_)
  apply mem_iInter.mpr
  intro j
  by_contra hj
  exact hn (mem_iUnion.mpr ⟨j,subset_closure (hmem j),hj⟩)

#print axioms rectangle_mass
#print axioms rectangle_null_frontier
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
