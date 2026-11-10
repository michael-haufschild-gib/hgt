import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitExchanges

/-!
# Exchanges of congruent digit blocks

Nonempty subcollections in two distinct parts can be exchanged whenever their
values agree modulo p^s−1. Admissibility is preserved, and the weight change is
the position gap times the value transferred to the later part. An optimum
therefore cannot have a larger congruent block available in an earlier part.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} {S A B : Finset (Digit p)}

/-- Exchanging two subcollections between distinct parts. -/
def exchangeParts (C : DigitComposition p s m S) (i j : Fin m)
    (A B : Finset (Digit p)) (k : Fin m) : Finset (Digit p) :=
  if k = i then (C.parts i \ A) ∪ B
  else if k = j then (C.parts j \ B) ∪ A else C.parts k

theorem mem_exchangeParts (C : DigitComposition p s m S) {i j : Fin m} (hij : i ≠ j)
    (hA : A ⊆ C.parts i) (hB : B ⊆ C.parts j) (k : Fin m) (x : Digit p) :
    x ∈ C.exchangeParts i j A B k ↔
      (x ∈ C.parts k ∧ x ∉ A ∧ x ∉ B) ∨ (k = i ∧ x ∈ B) ∨ (k = j ∧ x ∈ A) := by
  have ha : x ∈ C.parts k → x ∈ A → k = i := fun hx hxA => (C.mem_part_iff (hA hxA) k).mp hx
  have hb : x ∈ C.parts k → x ∈ B → k = j := fun hx hxB => (C.mem_part_iff (hB hxB) k).mp hx
  by_cases hki : k = i
  · subst k
    simp only [exchangeParts, ite_true, mem_union, mem_sdiff, true_and, hij, false_and, or_false]
    tauto
  · by_cases hkj : k = j
    · subst k
      simp only [exchangeParts, hki, ite_false, ite_true, mem_union, mem_sdiff,
        false_and, true_and, false_or]
      tauto
    · simp only [exchangeParts, hki, hkj, ite_false, false_and, or_false]
      tauto

theorem exchangeParts_value_sub (C : DigitComposition p s m S) {i j : Fin m} (hij : i ≠ j)
    (hA : A ⊆ C.parts i) (hB : B ⊆ C.parts j) (k : Fin m) :
    digitValue p (C.exchangeParts i j A B k) - C.value k =
      (if k = i then digitValue p B - digitValue p A else 0) +
        (if k = j then digitValue p A - digitValue p B else 0) := by
  by_cases hki : k = i
  · subst k
    have hdis : Disjoint (C.parts i \ A) B := disjoint_left.mpr fun x hx hxB =>
      disjoint_left.mp (C.disjoint hij) (mem_sdiff.mp hx).1 (hB hxB)
    have he := tokenValue_sdiff p Prod.fst hA
    simp only [exchangeParts, ite_true, if_neg hij, add_zero]
    change tokenValue p Prod.fst ((C.parts i \ A) ∪ B) - tokenValue p Prod.fst (C.parts i) = _
    rw [tokenValue, sum_union hdis]
    change tokenValue p Prod.fst (C.parts i \ A) + digitValue p B - C.value i = _
    change tokenValue p Prod.fst (C.parts i \ A) + digitValue p A = C.value i at he
    linarith only [he]
  · by_cases hkj : k = j
    · subst k
      have hdis : Disjoint (C.parts j \ B) A := disjoint_left.mpr fun x hx hxA =>
        disjoint_left.mp (C.disjoint hij.symm) (mem_sdiff.mp hx).1 (hA hxA)
      have he := tokenValue_sdiff p Prod.fst hB
      simp only [exchangeParts, if_neg hki, ite_true, zero_add]
      change tokenValue p Prod.fst ((C.parts j \ B) ∪ A) - tokenValue p Prod.fst (C.parts j) = _
      rw [tokenValue, sum_union hdis]
      change tokenValue p Prod.fst (C.parts j \ B) + digitValue p A - C.value j = _
      change tokenValue p Prod.fst (C.parts j \ B) + digitValue p B = C.value j at he
      linarith only [he]
    · simp only [exchangeParts, if_neg hki, if_neg hkj, value, sub_self, add_zero]

/-- Nonempty blocks of equal residue modulo p^s−1 can be exchanged between two parts. -/
def exchangeBlocks (C : DigitComposition p s m S) {i j : Fin m} (hij : i ≠ j)
    (hA : A ⊆ C.parts i) (hB : B ⊆ C.parts j) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hres : ((p : ℤ) ^ s - 1) ∣ digitValue p A - digitValue p B) :
    DigitComposition p s m S where
  parts := C.exchangeParts i j A B
  subset := by
    intro k x hx
    rcases (C.mem_exchangeParts hij hA hB k x).mp hx with h | h | h
    · exact C.subset k h.1
    · exact C.subset j (hB h.2)
    · exact C.subset i (hA h.2)
  disjoint := by
    intro k l hkl
    apply disjoint_left.mpr
    intro x hx hy
    rcases (C.mem_exchangeParts hij hA hB k x).mp hx with hx | hx | hx <;>
      rcases (C.mem_exchangeParts hij hA hB l x).mp hy with hy | hy | hy
    · exact disjoint_left.mp (C.disjoint hkl) hx.1 hy.1
    · exact hx.2.2 hy.2
    · exact hx.2.1 hy.2
    · exact hy.2.2 hx.2
    · exact hkl (hx.1.trans hy.1.symm)
    · exact disjoint_left.mp (C.disjoint hij) (hA hy.2) (hB hx.2)
    · exact hy.2.1 hx.2
    · exact disjoint_left.mp (C.disjoint hij) (hA hx.2) (hB hy.2)
    · exact hkl (hx.1.trans hy.1.symm)
  cover := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact ⟨j, (C.mem_exchangeParts hij hA hB j x).mpr (Or.inr (Or.inr ⟨rfl, hxA⟩))⟩
    · by_cases hxB : x ∈ B
      · exact ⟨i, (C.mem_exchangeParts hij hA hB i x).mpr (Or.inr (Or.inl ⟨rfl, hxB⟩))⟩
      · obtain ⟨k, hk⟩ := C.cover x hx
        exact ⟨k, (C.mem_exchangeParts hij hA hB k x).mpr (Or.inl ⟨hk, hxA, hxB⟩)⟩
  nonempty := by
    intro k
    by_cases hki : k = i
    · obtain ⟨x, hx⟩ := hneB
      exact ⟨x, (C.mem_exchangeParts hij hA hB k x).mpr (Or.inr (Or.inl ⟨hki, hx⟩))⟩
    · by_cases hkj : k = j
      · obtain ⟨x, hx⟩ := hneA
        exact ⟨x, (C.mem_exchangeParts hij hA hB k x).mpr (Or.inr (Or.inr ⟨hkj, hx⟩))⟩
      · obtain ⟨x, hx⟩ := C.nonempty k
        refine ⟨x, (C.mem_exchangeParts hij hA hB k x).mpr (Or.inl ⟨hx, ?_, ?_⟩)⟩
        · intro hxA
          exact hki ((C.mem_part_iff (hA hxA) k).mp hx)
        · intro hxB
          exact hkj ((C.mem_part_iff (hB hxB) k).mp hx)
  divisible := by
    intro k hk
    have he := C.exchangeParts_value_sub hij hA hB k
    have hrev : ((p : ℤ) ^ s - 1) ∣ digitValue p B - digitValue p A := by
      simpa only [neg_sub] using dvd_neg.mpr hres
    have hdiff : ((p : ℤ) ^ s - 1) ∣
        digitValue p (C.exchangeParts i j A B k) - C.value k := by
      rw [he]
      apply dvd_add
      · split_ifs <;> first | exact hrev | exact dvd_zero _
      · split_ifs <;> first | exact hres | exact dvd_zero _
    have hh := dvd_add hdiff (C.divisible k hk)
    simpa only [value, sub_add_cancel] using hh

/-- The weight change equals the position gap times the value transferred to the later part. -/
theorem exchangeBlocks_weight_sub (C : DigitComposition p s m S) {i j : Fin m} (hij : i ≠ j)
    (hA : A ⊆ C.parts i) (hB : B ⊆ C.parts j) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hres : ((p : ℤ) ^ s - 1) ∣ digitValue p A - digitValue p B) :
    (C.exchangeBlocks hij hA hB hneA hneB hres).weight - C.weight =
      ((j.val : ℤ) - (i.val : ℤ)) * (digitValue p A - digitValue p B) := by
  have hv (k : Fin m) : (C.exchangeBlocks hij hA hB hneA hneB hres).value k - C.value k =
      (if k = i then digitValue p B - digitValue p A else 0) +
        (if k = j then digitValue p A - digitValue p B else 0) :=
    C.exchangeParts_value_sub hij hA hB k
  simp only [weight, ← sum_sub_distrib, ← mul_sub, hv, mul_add, mul_ite, mul_zero,
    sum_add_distrib, sum_ite_eq', mem_univ, ite_true, Nat.cast_add, Nat.cast_one]
  ring

/-- In an optimum, congruent nonempty blocks cannot transfer a larger value to a later part. -/
theorem IsOptimal.block_value_le {C : DigitComposition p s m S} (hC : C.IsOptimal)
    {i j : Fin m} (hij : i < j) (hA : A ⊆ C.parts i) (hB : B ⊆ C.parts j)
    (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hres : ((p : ℤ) ^ s - 1) ∣ digitValue p A - digitValue p B) :
    digitValue p A ≤ digitValue p B := by
  by_contra hn
  have hval := lt_of_not_ge hn
  have hidx : (i.val : ℤ) < j.val := by exact_mod_cast (show i.val < j.val from hij)
  have hpos := mul_pos (sub_pos.mpr hidx) (sub_pos.mpr hval)
  have he := C.exchangeBlocks_weight_sub (ne_of_lt hij) hA hB hneA hneB hres
  have hmax := hC (C.exchangeBlocks (ne_of_lt hij) hA hB hneA hneB hres)
  linarith only [hpos, he, hmax]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsOptimal.block_value_le
