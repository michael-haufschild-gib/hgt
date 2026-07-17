import GaloisForLFunctions.HTGeometry.DifferentialMatroid
import GaloisForLFunctions.HTGeometry.AffineCollisionMatroid
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
    (differentialFamilyMatroid (F := F) x).Indep I ↔
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
    differentialFamilyMatroid (F := F) x = Matroid.freeOn Set.univ := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff, Matroid.freeOn_indep_iff]
    exact iff_of_true
      (hx.comp (fun i : I => i.1) Subtype.val_injective)
      (Set.subset_univ I)

/-- Exact collision classification for a represented differential matroid.  The family matroid is
the collision matroid of `frame` precisely when differential independence of every subfamily is
equivalent to injectivity of its frame labels. -/
theorem differentialFamilyMatroid_eq_affineCollisionMatroid_iff
    {F E ι Frame : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) (frame : ι → Frame) :
    differentialFamilyMatroid (F := F) x =
        HTGeometry.affineCollisionMatroid frame ↔
      ∀ I : Set ι,
        DifferentialIndependent F (fun i : I => x i) ↔ Set.InjOn frame I := by
  constructor
  · intro h I
    rw [← differentialFamilyMatroid_indep_iff x I,
      h, HTGeometry.affineCollisionMatroid_indep_iff]
  · intro h
    apply Matroid.ext_indep
    · simp [differentialFamilyMatroid]
    · intro I _
      rw [differentialFamilyMatroid_indep_iff,
        HTGeometry.affineCollisionMatroid_indep_iff]
      exact h I

/-- A family represents the free matroid exactly when the whole family is differentially
independent. -/
theorem differentialFamilyMatroid_eq_freeOn_iff
    {F E ι : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x : ι → E} :
    differentialFamilyMatroid (F := F) x = Matroid.freeOn Set.univ ↔
      DifferentialIndependent F x := by
  constructor
  · intro h
    have hI : (differentialFamilyMatroid (F := F) x).Indep Set.univ := by
      rw [h]
      simp
    have hu := (differentialFamilyMatroid_indep_iff x Set.univ).mp hI
    let e : ι ≃ (Set.univ : Set ι) := (Equiv.Set.univ ι).symm
    have he := (differentialIndependent_equiv e
      (fun i : (Set.univ : Set ι) => x i)).mpr hu
    simpa [e, Equiv.Set.univ] using he
  · exact differentialFamilyMatroid_eq_freeOn_of_differentialIndependent

end

end GaloisForLFunctions
