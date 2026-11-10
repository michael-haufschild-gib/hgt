import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.InitialCompositions

/-!
# Adding and deleting digits in the last part

Adding a disjoint digit block to the last part preserves admissibility and
adds its value times the number of parts to the weight. Adding the same
block to two compositions also preserves their reverse-lexicographic order.

Deleting digits from a still nonempty last part is reversed by this operation.
Both optimality and greediness therefore pass to the reduced composition.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Disjoint collections of digit occurrences have additive values. -/
theorem digitValue_union {p : ℕ} {S T : Finset (Digit p)} (hdis : Disjoint S T) :
    digitValue p (S ∪ T) = digitValue p S + digitValue p T := sum_union hdis

namespace DigitComposition
variable {p s m : ℕ} {S T U : Finset (Digit p)}

/-- Adding disjoint digits to the last part preserves admissibility. -/
def extendLast (C : DigitComposition p s (m + 1) S) (hdis : Disjoint S T)
    (hcover : S ∪ T = U) : DigitComposition p s (m + 1) U := by
  apply C.initial.appendLast (L := C.parts (Fin.last m) ∪ T)
  · apply disjoint_left.mpr
    intro x hx hxU
    rcases mem_union.mp hxU with hxlast | hxT
    · exact disjoint_left.mp C.prefix_disjoint_last hx hxlast
    · exact disjoint_left.mp hdis (C.prefix_subset m hx) hxT
  · exact (C.nonempty (Fin.last m)).mono subset_union_left
  · intro i
    exact C.divisible i.castSucc (by simpa only [Fin.val_castSucc, Nat.add_lt_add_iff_right] using i.isLt)
  · rw [← union_assoc, C.prefix_union_last, hcover]

theorem extendLast_parts (C : DigitComposition p s (m + 1) S) (hdis : Disjoint S T)
    (hcover : S ∪ T = U) :
    (C.extendLast hdis hcover).parts = Fin.snoc C.initial.parts (C.parts (Fin.last m) ∪ T) := rfl

theorem extendLast_values (C : DigitComposition p s (m + 1) S) (hdis : Disjoint S T)
    (hcover : S ∪ T = U) :
    (C.extendLast hdis hcover).value =
      Fin.snoc C.initial.value (C.value (Fin.last m) + digitValue p T) := by
  have hL : Disjoint (C.parts (Fin.last m)) T :=
    disjoint_left.mpr fun x hx hxT => disjoint_left.mp hdis (C.subset _ hx) hxT
  unfold extendLast
  rw [appendLast_values, digitValue_union hL]
  rfl

theorem extendLast_last (C : DigitComposition p s (m + 1) S) (hdis : Disjoint S T)
    (hcover : S ∪ T = U) :
    (C.extendLast hdis hcover).value (Fin.last m) = C.value (Fin.last m) + digitValue p T := by
  rw [C.extendLast_values hdis hcover, Fin.snoc_last]

theorem extendLast_weight (C : DigitComposition p s (m + 1) S) (hdis : Disjoint S T)
    (hcover : S ∪ T = U) :
    (C.extendLast hdis hcover).weight = C.weight + ((m + 1 : ℕ) : ℤ) * digitValue p T := by
  have hL : Disjoint (C.parts (Fin.last m)) T :=
    disjoint_left.mpr fun x hx hxT => disjoint_left.mp hdis (C.subset _ hx) hxT
  unfold extendLast
  rw [appendLast_weight, digitValue_union hL, C.weight_eq_initial_add_last]
  change C.initial.weight + ((m + 1 : ℕ) : ℤ) * (C.value (Fin.last m) + digitValue p T) = _
  ring

/-- Adding the same final block preserves all reverse-lexicographic comparisons. -/
theorem extendLast_reverseValues_lt_iff (C D : DigitComposition p s (m + 1) S)
    (hdis : Disjoint S T) (hcover : S ∪ T = U) :
    (C.extendLast hdis hcover).reverseValues < (D.extendLast hdis hcover).reverseValues ↔
      C.reverseValues < D.reverseValues := by
  change Pi.Lex (· < ·) (· < ·)
      ((C.extendLast hdis hcover).value ∘ Fin.rev) ((D.extendLast hdis hcover).value ∘ Fin.rev) ↔
    Pi.Lex (· < ·) (· < ·) (C.value ∘ Fin.rev) (D.value ∘ Fin.rev)
  rw [C.extendLast_values, D.extendLast_values, C.values_eq_snoc_initial, D.values_eq_snoc_initial]
  simp only [Fin.snoc_comp_rev, Fin.snoc_last, Fin.pi_lex_lt_cons_cons,
    add_lt_add_iff_right, add_left_inj]

/-- Removing digits from a still nonempty last part preserves admissibility. -/
def removeLast (C : DigitComposition p s (m + 1) S) (hT : T ⊆ C.parts (Fin.last m))
    (hne : (C.parts (Fin.last m) \ T).Nonempty) : DigitComposition p s (m + 1) (S \ T) := by
  apply C.initial.appendLast (L := C.parts (Fin.last m) \ T)
  · exact disjoint_left.mpr fun x hx hxL =>
      disjoint_left.mp C.prefix_disjoint_last hx (mem_sdiff.mp hxL).1
  · exact hne
  · intro i
    exact C.divisible i.castSucc (by simpa only [Fin.val_castSucc, Nat.add_lt_add_iff_right] using i.isLt)
  · ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hxP | hxL
      · exact mem_sdiff.mpr ⟨C.prefix_subset m hxP,
          fun hxT => disjoint_left.mp C.prefix_disjoint_last hxP (hT hxT)⟩
      · exact mem_sdiff.mpr ⟨C.subset _ (mem_sdiff.mp hxL).1, (mem_sdiff.mp hxL).2⟩
    · intro hx
      have hxU : x ∈ C.prefixDigits m ∪ C.parts (Fin.last m) := by
        rw [C.prefix_union_last]
        exact (mem_sdiff.mp hx).1
      rcases mem_union.mp hxU with hxP | hxL
      · exact mem_union_left _ hxP
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hxL, (mem_sdiff.mp hx).2⟩)

theorem removeLast_parts (C : DigitComposition p s (m + 1) S) (hT : T ⊆ C.parts (Fin.last m))
    (hne : (C.parts (Fin.last m) \ T).Nonempty) :
    (C.removeLast hT hne).parts = Fin.snoc C.initial.parts (C.parts (Fin.last m) \ T) := rfl

theorem removeLast_values (C : DigitComposition p s (m + 1) S) (hT : T ⊆ C.parts (Fin.last m))
    (hne : (C.parts (Fin.last m) \ T).Nonempty) :
    (C.removeLast hT hne).value =
      Fin.snoc C.initial.value (C.value (Fin.last m) - digitValue p T) := by
  have he := tokenValue_sdiff p Prod.fst hT
  have hv : digitValue p (C.parts (Fin.last m) \ T) = C.value (Fin.last m) - digitValue p T :=
    eq_sub_of_add_eq he
  unfold removeLast
  rw [appendLast_values, hv]

theorem removeLast_weight_add (C : DigitComposition p s (m + 1) S)
    (hT : T ⊆ C.parts (Fin.last m)) (hne : (C.parts (Fin.last m) \ T).Nonempty) :
    (C.removeLast hT hne).weight + ((m + 1 : ℕ) : ℤ) * digitValue p T = C.weight := by
  have he := tokenValue_sdiff p Prod.fst hT
  have hv : digitValue p (C.parts (Fin.last m) \ T) = C.value (Fin.last m) - digitValue p T :=
    eq_sub_of_add_eq he
  unfold removeLast
  rw [appendLast_weight, hv, C.weight_eq_initial_add_last]
  ring

/-- Restoring the removed last-part digits recovers the original composition. -/
theorem removeLast_extendLast (C : DigitComposition p s (m + 1) S)
    (hT : T ⊆ C.parts (Fin.last m)) (hne : (C.parts (Fin.last m) \ T).Nonempty) :
    (C.removeLast hT hne).extendLast sdiff_disjoint
      (sdiff_union_of_subset (hT.trans (C.subset _))) = C := by
  apply ext_parts
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [extendLast_parts, Fin.snoc_last, removeLast_parts, Fin.snoc_last, sdiff_union_of_subset hT]
  · rw [extendLast_parts, Fin.snoc_castSucc]
    change (C.removeLast hT hne).parts j.castSucc = C.parts j.castSucc
    rw [removeLast_parts, Fin.snoc_castSucc]
    rfl

/-- Optimality survives deleting any digits from a still nonempty last part. -/
theorem IsOptimal.removeLast {C : DigitComposition p s (m + 1) S} (hC : C.IsOptimal)
    (hT : T ⊆ C.parts (Fin.last m)) (hne : (C.parts (Fin.last m) \ T).Nonempty) :
    (C.removeLast hT hne).IsOptimal := by
  intro D
  have hc : (S \ T) ∪ T = S := sdiff_union_of_subset (hT.trans (C.subset _))
  have hD := hC (D.extendLast sdiff_disjoint hc)
  have heD := D.extendLast_weight sdiff_disjoint hc
  have heC := C.removeLast_weight_add hT hne
  linarith only [hD, heD, heC]

/-- Greediness survives deleting any digits from a still nonempty last part. -/
theorem IsGreedy.removeLast {C : DigitComposition p s (m + 1) S} (hC : C.IsGreedy)
    (hT : T ⊆ C.parts (Fin.last m)) (hne : (C.parts (Fin.last m) \ T).Nonempty) :
    (C.removeLast hT hne).IsGreedy := by
  intro D
  by_contra hn
  have hc : (S \ T) ∪ T = S := sdiff_union_of_subset (hT.trans (C.subset _))
  have hh := (extendLast_reverseValues_lt_iff (C.removeLast hT hne) D sdiff_disjoint hc).mpr
    (lt_of_not_ge hn)
  rw [C.removeLast_extendLast hT hne] at hh
  exact (not_lt_of_ge (hC (D.extendLast sdiff_disjoint hc))) hh

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsOptimal.removeLast
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsGreedy.removeLast
