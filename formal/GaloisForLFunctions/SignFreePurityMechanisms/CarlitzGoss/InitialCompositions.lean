import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.IncreasingAllocations
import Mathlib.Order.Fin.Tuple

/-!
# Initial segments of greedy and optimal compositions

The initial parts of an admissible composition have divisible total value.
Any other admissible composition of that digit collection therefore has all
its parts divisible, so the unchanged final block can be appended to it.

Weight differences and reverse-lexicographic comparisons survive this
replacement. Thus optimality and greediness both pass to the initial
composition obtained by deleting the last part.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} {S : Finset (Digit p)}

/-- The initial m parts form an admissible composition of their own digit collection. -/
def initial (C : DigitComposition p s (m + 1) S) :
    DigitComposition p s m (C.prefixDigits m) where
  parts := fun i => C.parts i.castSucc
  subset := fun i x hx => (C.mem_prefix m x).mpr ⟨i.castSucc, i.isLt, hx⟩
  disjoint := fun i j hij => C.disjoint (fun he => hij (Fin.ext (congrArg (fun k : Fin (m + 1) => k.val) he)))
  cover := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := (C.mem_prefix m x).mp hx
    let j : Fin m := ⟨i.val, hi⟩
    have he : j.castSucc = i := Fin.ext rfl
    exact ⟨j, he.symm ▸ hxi⟩
  nonempty := fun i => C.nonempty i.castSucc
  divisible := fun i _ => C.divisible i.castSucc (by simpa only [Fin.val_castSucc, Nat.add_lt_add_iff_right] using i.isLt)

/-- Every part of a composition is divisible when its total value is divisible. -/
theorem all_divisible_of_total (C : DigitComposition p s (m + 1) S)
    (hN : ((p : ℤ) ^ s - 1) ∣ digitValue p S) :
    ∀ i, ((p : ℤ) ^ s - 1) ∣ C.value i := by
  have hfirst : ((p : ℤ) ^ s - 1) ∣ ∑ i : Fin m, C.value i.castSucc := by
    apply dvd_sum
    intro i _
    exact C.divisible i.castSucc (by simpa only [Fin.val_castSucc, Nat.add_lt_add_iff_right] using i.isLt)
  have hlast : ((p : ℤ) ^ s - 1) ∣ C.value (Fin.last m) := by
    have he := C.sum_values
    rw [Fin.sum_univ_castSucc] at he
    have hd := dvd_sub hN hfirst
    rw [← he] at hd
    simpa only [add_sub_cancel_left] using hd
  intro i
  by_cases hi : i.val < m
  · exact C.divisible i (by omega)
  · have he : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    simpa only [he] using hlast

/-- The initial prefix of an admissible composition has divisible total value. -/
theorem initial_total_divisible (C : DigitComposition p s (m + 1) S) :
    ((p : ℤ) ^ s - 1) ∣ digitValue p (C.prefixDigits m) := by
  rw [C.value_prefix]
  apply dvd_sum
  intro i hi
  exact C.divisible i (by have hh := (mem_filter.mp hi).2; omega)

/-- Appending a nonempty last block to a composition of divisible parts. -/
def appendLast {T L : Finset (Digit p)} (A : DigitComposition p s m T)
    (hdis : Disjoint T L) (hne : L.Nonempty)
    (hdiv : ∀ i, ((p : ℤ) ^ s - 1) ∣ A.value i) (hc : T ∪ L = S) :
    DigitComposition p s (m + 1) S := by
  have hT : T ⊆ S := by rw [← hc]; exact subset_union_left
  have hL : L ⊆ S := by rw [← hc]; exact subset_union_right
  refine {
    parts := Fin.snoc A.parts L
    subset := ?_
    disjoint := ?_
    cover := ?_
    nonempty := ?_
    divisible := ?_ }
  · apply Fin.lastCases
    · simpa only [Fin.snoc_last] using hL
    · intro i
      simpa only [Fin.snoc_castSucc] using (A.subset i).trans hT
  · apply Fin.lastCases
    · apply Fin.lastCases
      · exact fun h => (h rfl).elim
      · intro j _
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact disjoint_left.mpr fun x hx hxj => disjoint_left.mp hdis (A.subset j hxj) hx
    · intro i
      apply Fin.lastCases
      · intro _
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact disjoint_left.mpr fun x hxi hx => disjoint_left.mp hdis (A.subset i hxi) hx
      · intro j hij
        simp only [Fin.snoc_castSucc]
        exact A.disjoint (fun he => hij (congrArg Fin.castSucc he))
  · intro x hx
    rw [← hc] at hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨i, hi⟩ := A.cover x hx
      exact ⟨i.castSucc, by simpa only [Fin.snoc_castSucc] using hi⟩
    · exact ⟨Fin.last m, by simpa only [Fin.snoc_last] using hx⟩
  · apply Fin.lastCases
    · simpa only [Fin.snoc_last] using hne
    · intro i
      simpa only [Fin.snoc_castSucc] using A.nonempty i
  · apply Fin.lastCases
    · intro h
      simp only [Fin.val_last, lt_self_iff_false] at h
    · intro i _
      simpa only [Fin.snoc_castSucc, value] using hdiv i

theorem appendLast_values {T L : Finset (Digit p)} (A : DigitComposition p s m T)
    (hdis : Disjoint T L) (hne : L.Nonempty)
    (hdiv : ∀ i, ((p : ℤ) ^ s - 1) ∣ A.value i) (hc : T ∪ L = S) :
    (A.appendLast hdis hne hdiv hc).value = Fin.snoc A.value (digitValue p L) := by
  exact Fin.comp_snoc (digitValue p) A.parts L

theorem appendLast_weight {T L : Finset (Digit p)} (A : DigitComposition p s m T)
    (hdis : Disjoint T L) (hne : L.Nonempty)
    (hdiv : ∀ i, ((p : ℤ) ^ s - 1) ∣ A.value i) (hc : T ∪ L = S) :
    (A.appendLast hdis hne hdiv hc).weight =
      A.weight + ((m + 1 : ℕ) : ℤ) * digitValue p L := by
  rw [weight, A.appendLast_values hdis hne hdiv hc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rfl

/-- The last block and the preceding prefix are disjoint. -/
theorem prefix_disjoint_last (C : DigitComposition p s (m + 1) S) :
    Disjoint (C.prefixDigits m) (C.parts (Fin.last m)) := by
  apply disjoint_left.mpr
  intro x hx hxlast
  obtain ⟨i, hi, hxi⟩ := (C.mem_prefix m x).mp hx
  have hne : i ≠ Fin.last m := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last] at hv
    omega
  exact disjoint_left.mp (C.disjoint hne) hxi hxlast

/-- A composition is the union of its initial prefix and its last block. -/
theorem prefix_union_last (C : DigitComposition p s (m + 1) S) :
    C.prefixDigits m ∪ C.parts (Fin.last m) = S := by
  ext x
  constructor
  · intro hx
    rcases mem_union.mp hx with hx | hx
    · exact C.prefix_subset m hx
    · exact C.subset (Fin.last m) hx
  · intro hx
    obtain ⟨i, hi⟩ := C.cover x hx
    by_cases him : i.val < m
    · exact mem_union_left _ ((C.mem_prefix m x).mpr ⟨i, him, hi⟩)
    · have he : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      exact mem_union_right _ (he ▸ hi)

theorem weight_eq_initial_add_last (C : DigitComposition p s (m + 1) S) :
    C.weight = C.initial.weight + ((m + 1 : ℕ) : ℤ) * C.value (Fin.last m) := by
  rw [weight, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rfl

/-- The value vector separates into its initial vector and last value. -/
theorem values_eq_snoc_initial (C : DigitComposition p s (m + 1) S) :
    C.value = Fin.snoc C.initial.value (C.value (Fin.last m)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]
    rfl

/-- An optimal composition has an optimal initial composition. -/
theorem IsOptimal.initial {C : DigitComposition p s (m + 2) S} (hC : C.IsOptimal) :
    C.initial.IsOptimal := by
  intro B
  let D := B.appendLast C.prefix_disjoint_last (C.nonempty (Fin.last (m + 1)))
    (B.all_divisible_of_total C.initial_total_divisible) C.prefix_union_last
  have hD := hC D
  have heD := B.appendLast_weight C.prefix_disjoint_last (C.nonempty (Fin.last (m + 1)))
    (B.all_divisible_of_total C.initial_total_divisible) C.prefix_union_last
  have heC := C.weight_eq_initial_add_last
  change D.weight = B.weight + ((m + 2 : ℕ) : ℤ) * C.value (Fin.last (m + 1)) at heD
  linarith only [hD, heD, heC]

/-- A greedy composition has a greedy initial composition. -/
theorem IsGreedy.initial {C : DigitComposition p s (m + 2) S} (hC : C.IsGreedy) :
    C.initial.IsGreedy := by
  intro B
  by_contra hn
  have hB := lt_of_not_ge hn
  let D := B.appendLast C.prefix_disjoint_last (C.nonempty (Fin.last (m + 1)))
    (B.all_divisible_of_total C.initial_total_divisible) C.prefix_union_last
  have hvalsD : D.value = Fin.snoc B.value (C.value (Fin.last (m + 1))) :=
    B.appendLast_values C.prefix_disjoint_last (C.nonempty (Fin.last (m + 1)))
      (B.all_divisible_of_total C.initial_total_divisible) C.prefix_union_last
  have hCD : C.reverseValues < D.reverseValues := by
    change Pi.Lex (· < ·) (· < ·) (C.value ∘ Fin.rev) (D.value ∘ Fin.rev)
    rw [C.values_eq_snoc_initial, hvalsD, Fin.snoc_comp_rev, Fin.snoc_comp_rev]
    exact (Fin.pi_lex_lt_cons_cons (fun a b : ℤ => a < b)).mpr (Or.inr ⟨rfl, hB⟩)
  exact (not_lt_of_ge (hC D)) hCD

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsOptimal.initial
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsGreedy.initial
