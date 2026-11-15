import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Volume under regrouping of finite coordinate products

Flattening a finite dependent product preserves product measure. Rectangles
pull back to products of rectangles, and their volume identities determine
the measure. Both directions preserve outer measure on arbitrary sets.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.SigmaProductVolume
noncomputable section
variable {ι : Type*} {κ : ι → Type*} [Fintype ι] [∀ i, Fintype (κ i)]
variable (X : ∀ i, κ i → Type*) [∀ i j, MeasureSpace (X i j)]
variable [∀ i j, SigmaFinite (volume : Measure (X i j))]

/-- Flattening a dependent product preserves its product measure. -/
theorem volume_preserving_uncurry :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm volume volume := by
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩
  change Measure.map (MeasurableEquiv.piCurry X).symm volume =
    Measure.pi (fun p : Sigma κ => (volume : Measure (X p.1 p.2)))
  apply Eq.symm
  refine Measure.pi_eq ?_
  intro s _
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i, j⟩)) := by
    ext x
    constructor
    · intro hx i _ j _
      exact hx ⟨i, j⟩ (Set.mem_univ _)
    · intro hx p _
      exact hx p.1 (Set.mem_univ _) p.2 (Set.mem_univ _)
  rw [hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  exact (Fintype.prod_sigma (fun p : Sigma κ => volume (s p))).symm

/-- Regrouping scalar coordinates into finite blocks preserves product measure. -/
theorem volume_preserving_curry :
    MeasurePreserving (MeasurableEquiv.piCurry X) volume volume :=
  MeasurePreserving.symm (MeasurableEquiv.piCurry X).symm (volume_preserving_uncurry X)

/-- Flattening preserves outer volume of inverse images, with no measurability premise on the set. -/
theorem volume_preimage_uncurry (S : Set ((p : Sigma κ) → X p.1 p.2)) :
    volume ((MeasurableEquiv.piCurry X).symm ⁻¹' S) = volume S := by
  rw [← MeasurableEquiv.map_apply, (volume_preserving_uncurry X).map_eq]

/-- Regrouping preserves outer volume of inverse images in the same way. -/
theorem volume_preimage_curry (S : Set (∀ i j, X i j)) :
    volume ((MeasurableEquiv.piCurry X) ⁻¹' S) = volume S := by
  rw [← MeasurableEquiv.map_apply, (volume_preserving_curry X).map_eq]

#print axioms volume_preserving_uncurry
#print axioms volume_preserving_curry
#print axioms volume_preimage_uncurry
#print axioms volume_preimage_curry

end
end GaloisForLFunctions.BiarithmeticGeometry.SigmaProductVolume
