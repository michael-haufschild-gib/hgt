import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PopularSymmetry

/-!
# Greedy containers for subproducts

Repeatedly adjoining a translate outside the half-popular set grows a finite set by at least
three halves. A maximal selection therefore has logarithmic length, and every unused factor
belongs to the popular set of the final subproduct sheet. Repeated factors remain distinct
indices; the conclusion controls multiplicity as well as distinct group elements.
-/

open Finset
open scoped Pointwise

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

variable {G ι : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [DecidableEq ι]

/-- All products formed by independently retaining or omitting the indexed factors. -/
def subproducts (q : ι → G) (I : Finset ι) : Finset G :=
  ∏ i ∈ I, ({1, q i} : Finset G)

omit [Fintype G] in
/-- Adding one factor adjoins its translate of the previous sheet. -/
theorem subproducts_insert (q : ι → G) (I : Finset ι) (i : ι) (hi : i ∉ I) :
    subproducts q (insert i I) = subproducts q I ∪ q i • subproducts q I := by
  rw [subproducts, prod_insert hi]
  have hp : ({1, q i} : Finset G) = {1} ∪ {q i} := by simp
  rw [hp, union_mul, singleton_mul, singleton_mul, one_smul]
  rfl

/-- Every finite factor family admits a multiplicity-preserving greedy container. -/
theorem exists_greedy_container (q : ι → G) (I : Finset ι) (A : Finset G) :
    ∃ J ⊆ I, 3 ^ J.card * A.card ≤ 2 ^ J.card * (A * subproducts q J).card ∧
      ∀ i ∈ I \ J, q i ∈ popularTranslations (A * subproducts q J) := by
  induction I using Finset.strongInductionOn generalizing A with
  | _ I ih =>
    by_cases hstop : ∀ i ∈ I, q i ∈ popularTranslations A
    · refine ⟨∅, empty_subset _, ?_, ?_⟩
      · simp [subproducts]
      · intro i hi
        simpa only [subproducts, prod_empty, mul_one] using hstop i (mem_sdiff.mp hi).1
    · push_neg at hstop
      obtain ⟨i, hi, hnot⟩ := hstop
      have hgrow := (popular_or_growth A (q i)).resolve_left hnot
      obtain ⟨J, hJ, hbound, hpopular⟩ := ih (I.erase i) (erase_ssubset hi) (A ∪ q i • A)
      have hiJ : i ∉ J := fun h => (mem_erase.mp (hJ h)).1 rfl
      have hfactor : A * subproducts q (insert i J) =
          (A ∪ q i • A) * subproducts q J := by
        rw [subproducts_insert q J i hiJ, mul_union, union_mul, mul_smul_comm, smul_mul_assoc]
      refine ⟨insert i J, insert_subset hi (Subset.trans hJ (erase_subset _ _)), ?_, ?_⟩
      · rw [card_insert_of_notMem hiJ, pow_succ, pow_succ, hfactor]
        have hfirst := Nat.mul_le_mul_left (3 ^ J.card) hgrow
        have hsecond := Nat.mul_le_mul_left 2 hbound
        nlinarith only [hfirst, hsecond]
      · intro j hj
        rw [hfactor]
        apply hpopular j
        rcases mem_sdiff.mp hj with ⟨hjI, hjJ⟩
        exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun h => hjJ (by subst j; exact mem_insert_self i J), hjI⟩,
          fun h => hjJ (mem_insert_of_mem h)⟩

/-- Starting from the identity gives a small skeleton whose sheet contains every unused factor
in its half-popular container. -/
theorem exists_subproduct_container (q : ι → G) (I : Finset ι) :
    ∃ J ⊆ I, 3 ^ J.card ≤ 2 ^ J.card * (subproducts q J).card ∧
      ∀ i ∈ I \ J, q i ∈ popularTranslations (subproducts q J) := by
  simpa only [Finset.card_one, mul_one, one_mul] using exists_greedy_container q I (1 : Finset G)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup
