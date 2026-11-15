import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBoxSeparation
import GaloisForLFunctions.BiarithmeticGeometry.Affine.IntegerWindowCounts

/-!
# Counting intersecting vertical translates of moment boxes

At spacing `ε / (q + 1)`, degree-one separation confines every intersecting
integer index to a finite interval. Its cardinality is bounded explicitly
by a linear function of the Euclidean direction difference. The constants
depend on physical dimension and grid density, but not on polynomial degree.
Zero scale is exactly the exceptional case: all integer translates intersect.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms
open GaloisForLFunctions.BiarithmeticGeometry.IntegerWindowCounts

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Intersection of two vertically indexed boxes at a prescribed grid density. -/
def integerTranslateOverlap (r k q : ℕ) (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (i j : ℤ) : Prop :=
  (momentCoveringBox r (k + 1) ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) ∩
    momentCoveringBox r (k + 1) ε η (ε * (j : ℝ) / (q + 1 : ℝ))).Nonempty

/-- Boxes with the same integer center intersect for every pair of directions and every scale. -/
theorem integerTranslateOverlap_self (r k q : ℕ) (ε : ℝ)
    (δ η : Fin (r + 1) → ℝ) (i : ℤ) : integerTranslateOverlap r k q ε δ η i i := by
  exact ⟨horizontalMoment r (k + 1) 0 (ε * (i : ℝ) / (q + 1 : ℝ)),
    momentCenter_mem_momentCoveringBox r (k + 1) ε δ _,
    momentCenter_mem_momentCoveringBox r (k + 1) ε η _⟩

/-- The common vertical scale cancels from the integer-index separation bound. -/
theorem integerTranslateOverlap_separation (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ η : Fin (r + 1) → ℝ) (i j : ℤ) (h : integerTranslateOverlap r k q ε δ η i j) :
    |(i : ℝ) - (j : ℝ)| ≤ (q + 1 : ℝ) * (4 + 2 * ∑ l, |(δ - η) l|) := by
  have hd : (0 : ℝ) < q + 1 := by positivity
  have hεabs : 0 < |ε| := abs_pos.mpr hε
  have hs := momentCoveringBox_intersection_separation r k ε δ η
    (ε * (i : ℝ) / (q + 1 : ℝ)) (ε * (j : ℝ) / (q + 1 : ℝ)) h
  rw [show ε * (i : ℝ) / (q + 1 : ℝ) - ε * (j : ℝ) / (q + 1 : ℝ) =
      ε * (((i : ℝ) - (j : ℝ)) / (q + 1 : ℝ)) by ring,
    abs_mul, abs_div, abs_of_pos hd] at hs
  have hc := (mul_le_mul_iff_right₀ hεabs).mp hs
  calc
    _ ≤ (4 + 2 * ∑ l, |(δ - η) l|) * (q + 1 : ℝ) := (div_le_iff₀ hd).mp hc
    _ = _ := mul_comm _ _

/-- Parallel boxes can interact only within four grid-density units of their integer centers. -/
theorem integerTranslateOverlap_parallel_separation (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i j : ℤ) (h : integerTranslateOverlap r k q ε δ δ i j) :
    |(i : ℝ) - (j : ℝ)| ≤ 4 * (q + 1 : ℝ) := by
  calc
    _ ≤ (q + 1 : ℝ) * 4 := by
      simpa only [sub_self, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero]
        using integerTranslateOverlap_separation r k q ε hε δ δ i j h
    _ = _ := mul_comm _ _

/-- The coordinate sum gives a complete finite enumeration with no dimension-dependent loss. -/
theorem exists_intersectingTranslateFinset_l1 (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ η : Fin (r + 1) → ℝ) (i : ℤ) :
    ∃ S : Finset ℤ, (∀ j, j ∈ S ↔ integerTranslateOverlap r k q ε δ η i j) ∧
      (S.card : ℝ) ≤ 1 + 8 * (q + 1 : ℝ) +
        4 * (q + 1 : ℝ) * ∑ l, |(δ - η) l| := by
  have hR : 0 ≤ (q + 1 : ℝ) * (4 + 2 * ∑ l, |(δ - η) l|) := by positivity
  obtain ⟨S, hS, hcard⟩ := exists_finset_of_abs_sub_le i
    ((q + 1 : ℝ) * (4 + 2 * ∑ l, |(δ - η) l|)) hR
    (integerTranslateOverlap r k q ε δ η i)
    (fun j hj => integerTranslateOverlap_separation r k q ε hε δ η i j hj)
  refine ⟨S, hS, hcard.trans_eq ?_⟩
  ring

/-- Every intersecting translate is enumerated, with an explicit degree-independent Euclidean bound. -/
theorem exists_intersectingTranslateFinset (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ η : Fin (r + 1) → ℝ) (i : ℤ) :
    ∃ S : Finset ℤ, (∀ j, j ∈ S ↔ integerTranslateOverlap r k q ε δ η i j) ∧
      (S.card : ℝ) ≤ 1 + 8 * (q + 1 : ℝ) +
        4 * (q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) * euclideanNorm (δ - η) := by
  obtain ⟨S, hS, hcard⟩ := exists_intersectingTranslateFinset_l1 r k q ε hε δ η i
  refine ⟨S, hS, hcard.trans ?_⟩
  have hd : 0 ≤ 4 * (q + 1 : ℝ) := by positivity
  calc
    _ ≤ 1 + 8 * (q + 1 : ℝ) + (4 * (q + 1 : ℝ)) *
        (((r + 1 : ℕ) : ℝ) * euclideanNorm (δ - η)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_abs_le_card_mul_euclideanNorm (δ - η)) hd)
    _ = _ := by ring

/-- Parallel families have a bounded number of intersecting translates independent of dimension and degree. -/
theorem exists_same_direction_intersectingTranslateFinset (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) :
    ∃ S : Finset ℤ, (∀ j, j ∈ S ↔ integerTranslateOverlap r k q ε δ δ i j) ∧
      (S.card : ℝ) ≤ 8 * (q + 1 : ℝ) + 1 := by
  obtain ⟨S, hS, hcard⟩ := exists_intersectingTranslateFinset r k q ε hε δ δ i
  refine ⟨S, hS, ?_⟩
  have hz : euclideanNorm (0 : Fin (r + 1) → ℝ) = 0 := by simp [euclideanNorm]
  have hc : (S.card : ℝ) ≤ 1 + 8 * (q + 1 : ℝ) := by
    simpa only [sub_self, hz, mul_zero, add_zero] using hcard
  exact hc.trans_eq (add_comm _ _)

/-- At spacing equal to the vertical scale, at most nine parallel translates meet a given box. -/
theorem exists_nine_parallel_intersecting_translates (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) :
    ∃ S : Finset ℤ, (∀ j, j ∈ S ↔
      (momentCoveringBox r (k + 1) ε δ (ε * (i : ℝ)) ∩
        momentCoveringBox r (k + 1) ε δ (ε * (j : ℝ))).Nonempty) ∧ S.card ≤ 9 := by
  obtain ⟨S, hS, hcard⟩ := exists_same_direction_intersectingTranslateFinset r k 0 ε hε δ i
  refine ⟨S, fun j => ?_, ?_⟩
  · simpa only [integerTranslateOverlap, Nat.cast_zero, zero_add, div_one] using hS j
  · norm_num at hcard
    exact_mod_cast hcard

/-- All integer translates meet at zero scale, for every pair of directions. -/
theorem integerTranslateOverlap_zero (r k q : ℕ) (δ η : Fin (r + 1) → ℝ) (i j : ℤ) :
    integerTranslateOverlap r k q 0 δ η i j := by
  simpa only [integerTranslateOverlap, zero_mul, zero_div] using
    (momentCoveringBox_zero_intersection_iff r k δ η 0 0).mpr rfl

/-- Finite enumeration of the full intersection family is possible exactly at nonzero scale. -/
theorem finite_intersectingTranslate_enumeration_iff (r k q : ℕ) (ε : ℝ)
    (δ η : Fin (r + 1) → ℝ) (i : ℤ) :
    (∃ S : Finset ℤ, ∀ j, j ∈ S ↔ integerTranslateOverlap r k q ε δ η i j) ↔ ε ≠ 0 := by
  constructor
  · rintro ⟨S, hS⟩ rfl
    have hall : (Set.univ : Set ℤ) ⊆ (S : Set ℤ) := by
      intro j _
      exact (hS j).mpr (integerTranslateOverlap_zero r k q δ η i j)
    exact Set.infinite_univ (S.finite_toSet.subset hall)
  · intro hε
    obtain ⟨S, hS, _⟩ := exists_intersectingTranslateFinset r k q ε hε δ η i
    exact ⟨S, hS⟩

/-- Every real scale either collapses or admits the explicit finite overlap count. -/
theorem intersectingTranslate_count_dichotomy (r k q : ℕ) (ε : ℝ)
    (δ η : Fin (r + 1) → ℝ) (i : ℤ) :
    ε = 0 ∨ ∃ S : Finset ℤ, (∀ j, j ∈ S ↔ integerTranslateOverlap r k q ε δ η i j) ∧
      (S.card : ℝ) ≤ 1 + 8 * (q + 1 : ℝ) +
        4 * (q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) * euclideanNorm (δ - η) := by
  by_cases hε : ε = 0
  · exact Or.inl hε
  · exact Or.inr (exists_intersectingTranslateFinset r k q ε hε δ η i)

#print axioms integerTranslateOverlap_self
#print axioms integerTranslateOverlap_separation
#print axioms integerTranslateOverlap_parallel_separation
#print axioms exists_intersectingTranslateFinset_l1
#print axioms exists_intersectingTranslateFinset
#print axioms exists_same_direction_intersectingTranslateFinset
#print axioms exists_nine_parallel_intersecting_translates
#print axioms integerTranslateOverlap_zero
#print axioms finite_intersectingTranslate_enumeration_iff
#print axioms intersectingTranslate_count_dichotomy

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
