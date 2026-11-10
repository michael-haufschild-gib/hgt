import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PrefixBoundary

/-!
# A shared inverse-content coordinate

Every proper part has integral inverse-content coordinates at least one. At a
boundary coordinate of their initial prefix, these entries sum to the number
of parts. Hence each entry equals one at that same coordinate, for every
optimal or greedy composition.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Inverse content is additive over every finite collection of content vectors. -/
theorem inverseContent_sum {s : ℕ} {α : Type*} (p : ℚ) (I : Finset α)
    (u : α → ZMod s → ℚ) (h : ZMod s) :
    inverseContent p (fun j => ∑ i ∈ I, u i j) h = ∑ i ∈ I, inverseContent p (u i) h := by
  simp only [inverseContent, cyclicWeighted, mul_sum, sum_div]
  rw [sum_comm]

namespace DigitComposition
variable {p s m : ℕ} {S : Finset (Digit p)}

/-- The residue contents of all parts add to the content of the complete digit collection. -/
theorem content_sum_parts (C : DigitComposition p s m S) (h : ZMod s) :
    tokenContent (fun t : Digit p => (t.1 : ZMod s)) S h = ∑ i, C.content i h := by
  have hd : Set.PairwiseDisjoint (↑(univ : Finset (Fin m))) C.parts :=
    fun _ _ _ _ hij => C.disjoint hij
  have he : tokenContent (fun t : Digit p => (t.1 : ZMod s)) (univ.biUnion C.parts) h =
      ∑ i, C.content i h := by
    simp only [content, tokenContent, card_filter, Nat.cast_sum]
    rw [sum_biUnion hd]
  rw [C.biUnion_parts] at he
  exact he

theorem inverseContent_sum_parts (C : DigitComposition p s m S) (h : ZMod s) :
    inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S j : ℚ)) h =
      ∑ i, inverseContent (p : ℚ) (fun j => (C.content i j : ℚ)) h := by
  simp only [C.content_sum_parts, Int.cast_sum]
  exact inverseContent_sum (p : ℚ) univ (fun i j => (C.content i j : ℚ)) h

variable [NeZero s]

/-- Every divisible part has inverse-content coordinates at least one. -/
theorem inverseContent_part_ge_one (C : DigitComposition p s m S) (hp : 2 ≤ p)
    (i : Fin m) (hi : i.val + 1 < m) (h : ZMod s) :
    1 ≤ inverseContent (p : ℚ) (fun j => (C.content i j : ℚ)) h := by
  have hJ : DivisibleContent p (C.content i) :=
    (divisibleContent_tokens_iff p hp Prod.fst (C.parts i)).mpr ⟨C.nonempty i, C.divisible i hi⟩
  exact inverseContent_ge_one_of_divisible p hp hJ h

/-- All divisible parts of an optimal or greedy composition share an inverse coordinate equal to one. -/
theorem exists_common_inverse_one {k : ℕ} {C : DigitComposition p s (k + 2) S}
    (hp : 2 ≤ p) (hC : C.IsOptimal ∨ C.IsGreedy) :
    ∃ h : ZMod s, ∀ i : Fin (k + 1),
      inverseContent (p : ℚ) (fun j => (C.content i.castSucc j : ℚ)) h = 1 := by
  obtain ⟨h, hh⟩ := exists_prefix_inverse_eq hp hC
  have hsum := C.initial.inverseContent_sum_parts h
  rw [hh] at hsum
  let a : Fin (k + 1) → ℚ := fun i =>
    inverseContent (p : ℚ) (fun j => (C.content i.castSucc j : ℚ)) h
  have ha (i : Fin (k + 1)) : 1 ≤ a i :=
    C.inverseContent_part_ge_one hp i.castSucc
      (by simpa only [Fin.val_castSucc, Nat.add_lt_add_iff_right] using i.isLt) h
  have hs : ∑ i, a i = ((k + 1 : ℕ) : ℚ) := hsum.symm
  have hz : ∑ i, (a i - 1) = 0 := by
    rw [sum_sub_distrib, hs, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]
  refine ⟨h, fun i => ?_⟩
  have hi := single_le_sum (fun j _ => sub_nonneg.mpr (ha j)) (mem_univ i)
  rw [hz] at hi
  change a i = 1
  linarith only [hi, ha i]

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_common_inverse_one
