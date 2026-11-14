import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.SubgroupFinset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Popular translations and geometric growth

The overlap of a finite set with all its left translates has total mass equal to the square of
its cardinality. Translations retaining more than half the set form a set of size strictly less
than twice its size, unless the original set is empty. Every remaining translation increases
the union by a factor of at least three halves. No commutativity is needed.
-/

open Finset
open scoped Pointwise

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Translations retaining strictly more than half of a set. -/
def popularTranslations (A : Finset G) : Finset G :=
  univ.filter fun g => A.card < 2 * (A ∩ g • A).card

omit [Fintype G] in
/-- Overlap is the number of points whose inverse translate remains in the set. -/
theorem inter_translate_eq_filter (A : Finset G) (g : G) :
    A ∩ g • A = A.filter (fun x => g⁻¹ * x ∈ A) := by
  ext x
  simp only [mem_inter, mem_filter, mem_smul_finset, smul_eq_mul]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨hx, by simpa only [inv_mul_cancel_left] using hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, g⁻¹ * x, hy, mul_inv_cancel_left g x⟩

/-- Double counting ordered pairs of points gives the exact total overlap. -/
theorem sum_inter_translate_card (A : Finset G) :
    ∑ g : G, (A ∩ g • A).card = A.card ^ 2 := by
  simp_rw [inter_translate_eq_filter, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have hsum (x : G) : (∑ g : G, if g⁻¹ * x ∈ A then 1 else 0) = A.card := by
    calc
      _ = ∑ g : G, if g ∈ A then 1 else 0 :=
        (Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight x))
          (fun g => if g ∈ A then (1 : ℕ) else 0))
      _ = A.card := by simp
  simp_rw [hsum]
  simp only [sum_const, smul_eq_mul, pow_two, mul_one]

/-- The strict popularity threshold gives a sharp integer bound, including the empty set. -/
theorem popular_card_mul_succ_le (A : Finset G) :
    (popularTranslations A).card * (A.card + 1) ≤ 2 * A.card ^ 2 := by
  calc
    _ = ∑ _g ∈ popularTranslations A, (A.card + 1) := by simp
    _ ≤ ∑ g ∈ popularTranslations A, 2 * (A ∩ g • A).card := by
      apply sum_le_sum
      intro g hg
      exact Nat.succ_le_of_lt (mem_filter.mp hg).2
    _ ≤ ∑ g : G, 2 * (A ∩ g • A).card :=
      sum_le_sum_of_subset (filter_subset _ _)
    _ = 2 * A.card ^ 2 := by rw [← mul_sum, sum_inter_translate_card]

/-- A nonempty set has strictly fewer than twice its size popular translations. -/
theorem popular_card_lt_iff (A : Finset G) :
    (popularTranslations A).card < 2 * A.card ↔ A.Nonempty := by
  constructor
  · intro h
    rw [← card_pos]
    omega
  · intro h
    have hp := popular_card_mul_succ_le A
    have hA : 0 < A.card := card_pos.mpr h
    by_contra hn
    have hm := Nat.mul_le_mul_right (A.card + 1) (Nat.le_of_not_gt hn)
    nlinarith only [hp, hA, hm]

omit [Fintype G] in
/-- Exact inclusion-exclusion for a set and any translate. -/
theorem union_translate_card (A : Finset G) (g : G) :
    (A ∪ g • A).card + (A ∩ g • A).card = 2 * A.card := by
  simpa only [card_smul_finset, two_mul] using card_union_add_card_inter A (g • A)

/-- Every translation is either popular or increases the set by at least three halves. -/
theorem popular_or_growth (A : Finset G) (g : G) :
    g ∈ popularTranslations A ∨ 3 * A.card ≤ 2 * (A ∪ g • A).card := by
  by_cases hg : g ∈ popularTranslations A
  · exact Or.inl hg
  · have hbound : 2 * (A ∩ g • A).card ≤ A.card := by
      simpa only [popularTranslations, mem_filter, mem_univ, true_and, not_lt] using hg
    have hcard := union_translate_card A g
    exact Or.inr (by omega)

/-- A small nonempty set leaves strictly more than half the group outside its popular set. -/
theorem popular_complement_majority (A : Finset G) :
    A = ∅ ∨ Fintype.card G < 4 * A.card ∨
      Fintype.card G < 2 * (univ \ popularTranslations A).card := by
  by_cases hA : A = ∅
  · exact Or.inl hA
  by_cases hsize : Fintype.card G < 4 * A.card
  · exact Or.inr (Or.inl hsize)
  have hpop := (popular_card_lt_iff A).mpr (nonempty_iff_ne_empty.mpr hA)
  have hpartition := card_sdiff_add_card_eq_card (subset_univ (popularTranslations A))
  rw [card_univ] at hpartition
  exact Or.inr (Or.inr (by omega))

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.sum_inter_translate_card
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.popular_card_lt_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.popular_or_growth
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.popular_complement_majority
