import GaloisForLFunctions.HTGeometry.DifferentialMatroid
import Mathlib.Logic.Equiv.Set

/-!
# Differential matroid represented by a family

Pulling the differential-transcendence matroid back along a family `x : ι → E` gives the genuine
matroid on the family indices.  Its independent subsets are exactly the differentially independent
subfamilies.  In particular, a differentially independent family represents the free matroid.
-/

open scoped Classical Differential

namespace GaloisForLFunctions

open Set

noncomputable section

universe u

/-- The differential matroid on the indices of a family. -/
def differentialFamilyMatroid
    {F E ι : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) : Matroid ι :=
  (differentialMatroid F E).comap x

/-- Independence in the family matroid is differential independence of the indexed subfamily. -/
theorem differentialFamilyMatroid_indep_iff
    {F E ι : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) (I : Set ι) :
    (differentialFamilyMatroid x).Indep I ↔
      DifferentialIndependent F (fun i : I => x i) := by
  rw [differentialFamilyMatroid, Matroid.comap_indep_iff,
    differentialMatroid_indep_iff]
  constructor
  · rintro ⟨himage, hinj⟩
    let e : I ≃ x '' I := Equiv.Set.imageOfInjOn x I hinj
    have h := (differentialIndependent_equiv e
      (Subtype.val : x '' I → E)).mpr himage
    simpa [e, Equiv.Set.imageOfInjOn] using h
  · intro h
    have hinjSubtype : Function.Injective (fun i : I => x i) := h.injective
    have hinj : Set.InjOn x I := fun _ hi _ hj hxy =>
      congrArg Subtype.val (hinjSubtype (a₁ := ⟨_, hi⟩) (a₂ := ⟨_, hj⟩) hxy)
    let e : I ≃ x '' I := Equiv.Set.imageOfInjOn x I hinj
    have himage := (differentialIndependent_equiv e
      (Subtype.val : x '' I → E)).mp (by
        simpa [e, Equiv.Set.imageOfInjOn] using h)
    exact ⟨himage, hinj⟩

/-- A fully differentially independent family represents the free matroid on its index set. -/
theorem differentialFamilyMatroid_eq_freeOn_of_differentialIndependent
    {F E ι : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} (hx : DifferentialIndependent F x) :
    differentialFamilyMatroid x = Matroid.freeOn Set.univ := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff, Matroid.freeOn_indep_iff]
    exact iff_of_true
      (hx.comp (fun i : I => i.1) Subtype.val_injective)
      (Set.subset_univ I)

end

end GaloisForLFunctions
