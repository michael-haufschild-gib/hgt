import Mathlib

/-!
# The tail of a finite-holonomy quotient

Taking the part fixed by a family of maps commutes with intersections, and — for an injective map
commuting with that family — with images.  Consequently the tail of a tower of pullbacks, computed
inside the fixed subfield of a finite holonomy group, is the fixed part of the ambient tail.

This is the descent step for an orbifold quotient: the tower is applied to the fixed field of the
holonomy, and the answer is the holonomy-fixed part of the answer for the ambient tower.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*}

/-- The part of a set fixed by every member of a family of maps. -/
def fixedSubset (F : Set (K → K)) (E : Set K) : Set K := {z | z ∈ E ∧ ∀ f ∈ F, f z = z}

theorem mem_fixedSubset_iff {F : Set (K → K)} {E : Set K} {z : K} :
    z ∈ fixedSubset F E ↔ z ∈ E ∧ ∀ f ∈ F, f z = z := Iff.rfl

theorem fixedSubset_subset (F : Set (K → K)) (E : Set K) : fixedSubset F E ⊆ E :=
  fun _ hz => hz.1

/-- **Fixed parts commute with intersections.** -/
theorem fixedSubset_iInter (F : Set (K → K)) {ι : Type*} [Nonempty ι] (E : ι → Set K) :
    fixedSubset F (⋂ n, E n) = ⋂ n, fixedSubset F (E n) := by
  ext z
  simp only [mem_fixedSubset_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hz, hfix⟩ n
    exact ⟨hz n, hfix⟩
  · intro hz
    exact ⟨fun n => (hz n).1, (hz (Classical.arbitrary ι)).2⟩

/-- **Fixed parts commute with images of injective commuting maps.** -/
theorem image_fixedSubset {F : Set (K → K)} {σ : K → K} (hinj : Function.Injective σ)
    (hcomm : ∀ f ∈ F, ∀ x, σ (f x) = f (σ x)) (E : Set K) :
    σ '' fixedSubset F E = fixedSubset F (σ '' E) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxE, hxfix⟩, rfl⟩
    refine ⟨⟨x, hxE, rfl⟩, fun f hf => ?_⟩
    rw [← hcomm f hf x, hxfix f hf]
  · rintro ⟨⟨x, hxE, rfl⟩, hyfix⟩
    refine ⟨x, ⟨hxE, fun f hf => ?_⟩, rfl⟩
    refine hinj ?_
    rw [hcomm f hf x]
    exact hyfix f hf

/-- **The finite-holonomy tail law.**  The tail of the tower restricted to the fixed subfield is the
fixed part of the ambient tail. -/
theorem iInter_image_fixedSubset (F : Set (K → K)) {ι : Type*} [Nonempty ι] (σ : ι → K → K)
    (hinj : ∀ n, Function.Injective (σ n))
    (hcomm : ∀ n, ∀ f ∈ F, ∀ x, σ n (f x) = f (σ n x)) (E : Set K) :
    (⋂ n, σ n '' fixedSubset F E) = fixedSubset F (⋂ n, σ n '' E) := by
  have hstep : ∀ n, σ n '' fixedSubset F E = fixedSubset F (σ n '' E) :=
    fun n => image_fixedSubset (hinj n) (hcomm n) E
  rw [Set.iInter_congr hstep, ← fixedSubset_iInter F fun n => σ n '' E]

/-- The same statement with the ambient tail named: the holonomy-quotient tail is the fixed part of
the ambient tail. -/
theorem iInter_image_fixedSubset_eq_fixedSubset_tail (F : Set (K → K)) {ι : Type*} [Nonempty ι]
    (σ : ι → K → K) (hinj : ∀ n, Function.Injective (σ n))
    (hcomm : ∀ n, ∀ f ∈ F, ∀ x, σ n (f x) = f (σ n x)) (E : Set K) {T : Set K}
    (hT : T = ⋂ n, σ n '' E) :
    (⋂ n, σ n '' fixedSubset F E) = fixedSubset F T := by
  rw [hT]
  exact iInter_image_fixedSubset F σ hinj hcomm E

end GaloisForLFunctions.HTGeometry
