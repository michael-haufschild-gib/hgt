import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitValues
import Mathlib.Order.PiLex
import Mathlib.Data.Finset.Max

/-!
# Admissible carry-free digit compositions

A finite subset of `ℕ × Fin (p−1)` records at most p−1 copies of each power
of p. An admissible composition partitions these occurrences into nonempty
parts whose values, except possibly the last, are divisible by `p^s−1`.

The recursive digit-prefix criterion is equivalent to existence of an indexed
composition. The finite space of compositions has both a maximal weighted sum
and a reverse-lexicographic maximum. Greedy part values are unique; with two
parts, greediness and optimality coincide.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Base-p digit occurrences; the second coordinate distinguishes at most p−1 equal powers. -/
abbrev Digit (p : ℕ) := ℕ × Fin (p - 1)

def digitValue (p : ℕ) (S : Finset (Digit p)) : ℤ := tokenValue p Prod.fst S

/-- A carry-free partition whose first m−1 positive parts are divisible by `p^s−1`. -/
structure DigitComposition (p s m : ℕ) (S : Finset (Digit p)) where
  parts : Fin m → Finset (Digit p)
  subset : ∀ i, parts i ⊆ S
  disjoint : Pairwise fun i j => Disjoint (parts i) (parts j)
  cover : ∀ x ∈ S, ∃ i, x ∈ parts i
  nonempty : ∀ i, (parts i).Nonempty
  divisible : ∀ i, i.val + 1 < m → ((p : ℤ) ^ s - 1) ∣ digitValue p (parts i)

namespace DigitComposition
variable {p s m : ℕ} {S : Finset (Digit p)}

theorem ext_parts {C D : DigitComposition p s m S} (h : C.parts = D.parts) : C = D := by
  cases C
  cases D
  cases h
  rfl

instance : Finite (DigitComposition p s m S) := by
  apply Finite.of_injective
    (fun C : DigitComposition p s m S => fun i =>
      (⟨C.parts i, mem_powerset.mpr (C.subset i)⟩ : ↥S.powerset))
  intro C D h
  apply ext_parts
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- Integer value of one part of a digit partition. -/
def value (C : DigitComposition p s m S) (i : Fin m) : ℤ := digitValue p (C.parts i)

/-- Weighted sum of the parts, with positions numbered from one. -/
def weight (C : DigitComposition p s m S) : ℤ := ∑ i, ((i.val + 1 : ℕ) : ℤ) * C.value i

def IsOptimal (C : DigitComposition p s m S) : Prop :=
  ∀ D : DigitComposition p s m S, D.weight ≤ C.weight

theorem biUnion_parts (C : DigitComposition p s m S) : univ.biUnion C.parts = S := by
  ext x
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact C.subset i hi
  · exact C.cover x

/-- The part values sum to the value of the original digit collection. -/
theorem sum_values (C : DigitComposition p s m S) : ∑ i, C.value i = digitValue p S := by
  have hd : Set.PairwiseDisjoint (↑(univ : Finset (Fin m))) C.parts :=
    fun _ _ _ _ hij => C.disjoint hij
  calc
    ∑ i, C.value i = ∑ x ∈ univ.biUnion C.parts, (p : ℤ) ^ x.1 := by
      rw [sum_biUnion hd]
      rfl
    _ = digitValue p S := by rw [C.biUnion_parts]; rfl

theorem value_pos (C : DigitComposition p s m S) (hp : 0 < p) (i : Fin m) :
    0 < C.value i := (tokenValue_pos_iff p hp Prod.fst _).mpr (C.nonempty i)

/-- Every composition weight is at most its number of parts times its total value. -/
theorem weight_le (C : DigitComposition p s m S) (hp : 0 < p) :
    C.weight ≤ (m : ℤ) * digitValue p S := by
  rw [← C.sum_values, mul_sum]
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (C.value_pos hp i).le
  exact_mod_cast Nat.succ_le_of_lt i.isLt

/-- With two parts, maximizing weight is exactly maximizing the last part. -/
theorem weight_two (C : DigitComposition p s 2 S) :
    C.weight = digitValue p S + C.value 1 := by
  have hs := C.sum_values
  simp only [Fin.sum_univ_two] at hs
  dsimp only [weight]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  norm_num only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, one_mul]
  linarith only [hs]

/-- The reversed vector of part values, ordered lexicographically. -/
def reverseValues (C : DigitComposition p s m S) : Lex (Fin m → ℤ) :=
  toLex fun i => C.value i.rev

/-- Greedy means largest last part, then largest penultimate part, and so on. -/
def IsGreedy (C : DigitComposition p s m S) : Prop :=
  ∀ D : DigitComposition p s m S, D.reverseValues ≤ C.reverseValues

theorem exists_optimal (h : Nonempty (DigitComposition p s m S)) :
    ∃ C : DigitComposition p s m S, C.IsOptimal := by
  classical
  letI := Fintype.ofFinite (DigitComposition p s m S)
  letI := h
  obtain ⟨C, _, hC⟩ := univ.exists_max_image
    (fun C : DigitComposition p s m S => C.weight) univ_nonempty
  exact ⟨C, fun D => hC D (mem_univ D)⟩

theorem exists_greedy (h : Nonempty (DigitComposition p s m S)) :
    ∃ C : DigitComposition p s m S, C.IsGreedy := by
  classical
  letI := Fintype.ofFinite (DigitComposition p s m S)
  letI := h
  obtain ⟨C, _, hC⟩ := univ.exists_max_image
    (fun C : DigitComposition p s m S => C.reverseValues) univ_nonempty
  exact ⟨C, fun D => hC D (mem_univ D)⟩

/-- Greedy part values are unique, even when equal digit occurrences have different labels. -/
theorem IsGreedy.values_eq {C D : DigitComposition p s m S}
    (hC : C.IsGreedy) (hD : D.IsGreedy) : C.value = D.value := by
  have he : C.reverseValues = D.reverseValues := le_antisymm (hD C) (hC D)
  funext i
  have hh := congrFun (congrArg ofLex he) i.rev
  simpa only [reverseValues, ofLex_toLex, Fin.rev_rev] using hh

/-- Increasing the final part strictly increases the reverse-lexicographic vector. -/
theorem reverseValues_lt_of_last_lt {C D : DigitComposition p s (m + 1) S}
    (h : C.value (Fin.last m) < D.value (Fin.last m)) : C.reverseValues < D.reverseValues := by
  change Pi.Lex (· < ·) (· < ·)
    (fun i : Fin (m + 1) => C.value i.rev) (fun i : Fin (m + 1) => D.value i.rev)
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    have hj0 : j.val < 0 := hj
    omega
  · simpa only [Fin.rev_zero] using h

/-- A greedy composition has maximal last part. -/
theorem IsGreedy.last_max {C : DigitComposition p s (m + 1) S} (hC : C.IsGreedy)
    (D : DigitComposition p s (m + 1) S) : D.value (Fin.last m) ≤ C.value (Fin.last m) := by
  by_contra h
  have hh := reverseValues_lt_of_last_lt (lt_of_not_ge h)
  exact (not_lt_of_ge (hC D)) hh

/-- For two parts, maximal last value already determines the greedy value vector. -/
theorem isGreedy_two_iff (C : DigitComposition p s 2 S) :
    C.IsGreedy ↔ ∀ D : DigitComposition p s 2 S, D.value 1 ≤ C.value 1 := by
  constructor
  · intro h D
    exact h.last_max D
  · intro h D
    rcases lt_or_eq_of_le (h D) with hlt | heq
    · exact (reverseValues_lt_of_last_lt hlt).le
    · have hC := C.sum_values
      have hD := D.sum_values
      simp only [Fin.sum_univ_two] at hC hD
      have hzero : D.value 0 = C.value 0 := by linarith only [hC, hD, heq]
      have hv : D.value = C.value := by
        funext i
        fin_cases i
        · exact hzero
        · exact heq
      apply le_of_eq
      change toLex (fun i : Fin 2 => D.value i.rev) = toLex (fun i : Fin 2 => C.value i.rev)
      rw [hv]

/-- The greedy and optimal conditions coincide for two-part compositions. -/
theorem isOptimal_two_iff_isGreedy (C : DigitComposition p s 2 S) :
    C.IsOptimal ↔ C.IsGreedy := by
  rw [isGreedy_two_iff]
  change (∀ D : DigitComposition p s 2 S, D.weight ≤ C.weight) ↔ _
  simp only [weight_two, add_le_add_iff_left]

/-- The only part of a one-part composition is the entire digit collection. -/
def single (hS : S.Nonempty) : DigitComposition p s 1 S where
  parts := fun _ => S
  subset := fun _ => Subset.refl S
  disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
  cover := fun x hx => ⟨0, hx⟩
  nonempty := fun _ => hS
  divisible := by intro i hi; have := i.isLt; omega

/-- Prepending a divisible nonempty block to a composition of its complement. -/
def prepend {T : Finset (Digit p)} (hT : T ⊆ S) (hne : T.Nonempty)
    (hdiv : ((p : ℤ) ^ s - 1) ∣ digitValue p T)
    (C : DigitComposition p s (m + 1) (S \ T)) : DigitComposition p s (m + 2) S where
  parts := Fin.cons T C.parts
  subset := by
    intro i
    cases i using Fin.cases with
    | zero => exact hT
    | succ i => exact fun x hx => (mem_sdiff.mp (C.subset i hx)).1
  disjoint := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        exact disjoint_left.mpr fun x hx hxj => (mem_sdiff.mp (C.subset j hxj)).2 hx
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        exact disjoint_left.mpr fun x hxi hx => (mem_sdiff.mp (C.subset i hxi)).2 hx
      | succ j => exact C.disjoint (fun he => hij (congrArg Fin.succ he))
  cover := by
    intro x hx
    by_cases ht : x ∈ T
    · exact ⟨0, ht⟩
    · obtain ⟨i, hi⟩ := C.cover x (mem_sdiff.mpr ⟨hx, ht⟩)
      exact ⟨i.succ, hi⟩
  nonempty := by
    intro i
    cases i using Fin.cases with
    | zero => exact hne
    | succ i => exact C.nonempty i
  divisible := by
    intro i hi
    cases i using Fin.cases with
    | zero => exact hdiv
    | succ i => exact C.divisible i (by simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using hi)

/-- Removing the first block leaves a composition of the remaining digits. -/
def tail (C : DigitComposition p s (m + 2) S) :
    DigitComposition p s (m + 1) (S \ C.parts 0) where
  parts := fun i => C.parts i.succ
  subset := by
    intro i x hx
    refine mem_sdiff.mpr ⟨C.subset i.succ hx, ?_⟩
    intro hx0
    exact disjoint_left.mp (C.disjoint (Fin.succ_ne_zero i)) hx hx0
  disjoint := fun i j hij => C.disjoint (fun he => hij (Fin.succ_injective _ he))
  cover := by
    intro x hx
    obtain ⟨i, hi⟩ := C.cover x (mem_sdiff.mp hx).1
    cases i using Fin.cases with
    | zero => exact ((mem_sdiff.mp hx).2 hi).elim
    | succ i => exact ⟨i, hi⟩
  nonempty := fun i => C.nonempty i.succ
  divisible := fun i hi => C.divisible i.succ (by simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using hi)

/-- Indexed compositions and recursive divisible-prefix partitions describe the same objects. -/
theorem nonempty_iff_tokenPrefix [NeZero s] (hp : 2 ≤ p) (k : ℕ) (S : Finset (Digit p)) :
    Nonempty (DigitComposition p s (k + 1) S) ↔
      TokenPrefix p (fun t : Digit p => (t.1 : ZMod s)) k S := by
  induction k generalizing S with
  | zero =>
    constructor
    · rintro ⟨C⟩
      exact TokenPrefix.zero ((C.nonempty 0).mono (C.subset 0))
    · intro h
      cases h with
      | zero hS => exact ⟨single hS⟩
  | succ k ih =>
    constructor
    · rintro ⟨C⟩
      apply TokenPrefix.cons (C.subset 0)
      · apply (divisibleContent_tokens_iff p hp Prod.fst (C.parts 0)).mpr
        exact ⟨C.nonempty 0, C.divisible 0 (by simp)⟩
      · exact (ih _).mp ⟨C.tail⟩
    · intro h
      cases h with
      | @cons _ _ T hT hJ hrest =>
        obtain ⟨hne, hdiv⟩ := (divisibleContent_tokens_iff p hp Prod.fst T).mp hJ
        obtain ⟨C⟩ := (ih _).mpr hrest
        exact ⟨prepend hT hne hdiv C⟩

/-- Exact inverse-content feasibility for carry-free positive compositions. -/
theorem nonempty_iff_inverseContent [NeZero s] (hp : 2 ≤ p) (k : ℕ) (S : Finset (Digit p)) :
    Nonempty (DigitComposition p s (k + 1) S) ↔
      ∀ h : ZMod s, (k : ℚ) < inverseContent (p : ℚ)
        (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S j : ℚ)) h := by
  rw [nonempty_iff_tokenPrefix hp, tokenPrefix_iff_inverseContent p k hp]

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.nonempty_iff_inverseContent
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_greedy

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.isOptimal_two_iff_isGreedy
