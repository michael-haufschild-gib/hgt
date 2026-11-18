import GaloisForLFunctions.HTGeometry.BorsukUlam.CrossPolytope
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementCounts

/-!
# Point counts for the cross-polytope

Opposite vertices form the minimal nonfaces of the cross-polytope
boundary. The corresponding coordinate arrangement is therefore a
product of punctured planes. Using nonzero supports gives the union of
the two axes in each plane instead.
-/

namespace GaloisForLFunctions.BorsukUlam.CrossPolytope
open Finset ArithmeticHarmonicAnalysis.Codes
open scoped Classical
noncomputable section

variable {n : ℕ} {A : Type*} [Fintype A]

/-- Adjoining the empty face makes membership equivalent to avoiding
every antipodal pair. -/
theorem mem_augmented_faces (S : Finset (Vtx n)) :
    S ∈ insert ∅ faces ↔ ∀ i, ¬ ((i,false) ∈ S ∧ (i,true) ∈ S) := by
  rw [mem_insert, mem_faces]
  constructor
  · rintro (rfl | ⟨_,h⟩) i
    · simp
    · rintro ⟨hf,ht⟩
      exact Bool.false_ne_true (congrArg Prod.snd (h _ hf _ ht rfl))
  · intro h
    by_cases he : S = ∅
    · exact Or.inl he
    · refine Or.inr ⟨nonempty_iff_ne_empty.mpr he, ?_⟩
      rintro ⟨i,b⟩ hb ⟨j,c⟩ hc (hij : i = j)
      subst j
      cases b <;> cases c
      · rfl
      · exact (h i ⟨hb,hc⟩).elim
      · exact (h i ⟨hc,hb⟩).elim
      · rfl

/-- At each coordinate the allowable signed pairs are the complement
of a rectangle. Choices at different indices are independent. -/
def crossPolytopeRows (D : Vtx n → Finset A) :
    ↥(arrangementWords D (insert ∅ faces)) ≃
      ∀ i : Fin (n+1), ↥(((D (i,false)) ×ˢ (D (i,true)))ᶜ) where
  toFun x i := ⟨(x.val (i,false), x.val (i,true)), by
    have h := (mem_augmented_faces _).mp (mem_filter.mp x.property).2 i
    simpa [matchSet] using h⟩
  invFun p := ⟨fun v => if v.2 then (p v.1).val.2 else (p v.1).val.1, by
    refine mem_filter.mpr ⟨mem_univ _, (mem_augmented_faces _).mpr fun i => ?_⟩
    simpa [matchSet] using (p i).property⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    rcases v with ⟨i,b⟩
    cases b <;> rfl
  right_inv p := by
    funext i
    apply Subtype.ext
    rfl

/-- Independent alphabets of marked letters contribute one punctured rectangle per index. -/
theorem card_crossPolytopeArrangement (D : Vtx n → Finset A) :
    (arrangementWords D (insert ∅ faces)).card =
      ∏ i : Fin (n+1), (Fintype.card A ^ 2 - (D (i,false)).card * (D (i,true)).card) := by
  have h := Fintype.card_congr (crossPolytopeRows D)
  simpa [card_compl, Fintype.card_prod, pow_two] using h

/-- Over a finite field the complement is a product of punctured affine planes.
The same formula holds for an arbitrary finite alphabet with a chosen point. -/
theorem card_crossPolytope_zero_support (c : A) :
    (arrangementWords (fun _ : Vtx n => {c}) (insert ∅ faces)).card =
      (Fintype.card A ^ 2 - 1) ^ (n+1) := by
  simp [card_crossPolytopeArrangement]

/-- On the affine Stanley–Reisner locus each plane contributes its two axes,
which meet in one point. -/
theorem card_crossPolytope_nonzero_support (c : A) :
    (arrangementWords (fun _ : Vtx n => ({c} : Finset A)ᶜ) (insert ∅ faces)).card =
      (2 * (Fintype.card A - 1) + 1) ^ (n+1) := by
  have hp : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨c⟩
  have h : Fintype.card A ^ 2 - (Fintype.card A - 1) * (Fintype.card A - 1) =
      2 * (Fintype.card A - 1) + 1 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [hk, Nat.succ_sub_one, Nat.succ_eq_add_one, add_sq, pow_two]
    omega
  simp [card_crossPolytopeArrangement, card_compl, h]

#print axioms crossPolytopeRows
#print axioms card_crossPolytope_zero_support
#print axioms card_crossPolytope_nonzero_support

end
end GaloisForLFunctions.BorsukUlam.CrossPolytope
