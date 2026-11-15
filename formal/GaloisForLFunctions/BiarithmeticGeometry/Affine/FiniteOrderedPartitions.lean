import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ordered finite cutoff partitions

For values in the unit interval, multiplying each value by the complements
of all earlier values gives nonnegative weights bounded by the original
values. Their sum is one minus the product of all complements. Vanishing
earlier values can be deleted without changing an individual weight.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.FiniteOrderedPartitions
noncomputable section

variable {ι : Type*} [LinearOrder ι]

/-- The union value of a finite family of scalar cutoffs. -/
def cutoffUnion (S : Finset ι) (a : ι → ℝ) : ℝ := 1 - ∏ i ∈ S, (1 - a i)

/-- A cutoff value multiplied by the complements of all earlier values. -/
def orderedWeight (S : Finset ι) (a : ι → ℝ) (i : ι) : ℝ :=
  a i * ∏ j ∈ S.filter (fun j => j < i), (1 - a j)

/-- The ordered weights telescope to the union value. -/
theorem sum_orderedWeight (S : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ S, orderedWeight S a i) = cutoffUnion S a := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp only [cutoffUnion, Finset.sum_empty, Finset.prod_empty, sub_self]
  | insert i S hmax ih =>
    have hi : i ∉ S := fun hi => (lt_irrefl i) (hmax i hi)
    have hbefore : (insert i S).filter (fun j => j < i) = S := by
      rw [Finset.filter_insert, if_neg (lt_irrefl i)]
      exact Finset.filter_eq_self.mpr hmax
    have hold : ∀ j ∈ S, orderedWeight (insert i S) a j = orderedWeight S a j := by
      intro j hj
      have hnot : ¬ i < j := not_lt.mpr (hmax j hj).le
      simp only [orderedWeight, Finset.filter_insert, if_neg hnot]
    rw [Finset.sum_insert hi, Finset.sum_congr rfl hold, ih]
    simp only [orderedWeight, hbefore, cutoffUnion, Finset.prod_insert hi]
    ring

/-- Every ordered weight lies between zero and its original cutoff value. -/
theorem orderedWeight_mem_Icc (S : Finset ι) (a : ι → ℝ)
    (h : ∀ j ∈ S, a j ∈ Set.Icc (0 : ℝ) 1) (i : ι) (hi : i ∈ S) :
    orderedWeight S a i ∈ Set.Icc 0 (a i) := by
  have hf (j : ι) (hj : j ∈ S.filter (fun j => j < i)) :
      (1 - a j) ∈ Set.Icc (0 : ℝ) 1 := by
    have ha := h j (Finset.mem_filter.mp hj).1
    exact ⟨sub_nonneg.mpr ha.2, by linarith only [ha.1]⟩
  have hp : (∏ j ∈ S.filter (fun j => j < i), (1 - a j)) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Finset.prod_nonneg (fun j hj => (hf j hj).1),
      Finset.prod_le_one (fun j hj => (hf j hj).1) (fun j hj => (hf j hj).2)⟩
  refine ⟨mul_nonneg (h i hi).1 hp.1, ?_⟩
  simpa only [orderedWeight, mul_one] using mul_le_mul_of_nonneg_left hp.2 (h i hi).1

omit [LinearOrder ι] in
/-- Combining unit-interval cutoffs again gives a unit-interval cutoff. -/
theorem cutoffUnion_mem_Icc (S : Finset ι) (a : ι → ℝ)
    (h : ∀ i ∈ S, a i ∈ Set.Icc (0 : ℝ) 1) :
    cutoffUnion S a ∈ Set.Icc (0 : ℝ) 1 := by
  have hp0 : 0 ≤ ∏ i ∈ S, (1 - a i) :=
    Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (h i hi).2)
  have hp1 : (∏ i ∈ S, (1 - a i)) ≤ 1 :=
    Finset.prod_le_one (fun i hi => sub_nonneg.mpr (h i hi).2)
      (fun i hi => by linarith only [(h i hi).1])
  exact ⟨by unfold cutoffUnion; linarith only [hp1],
    by unfold cutoffUnion; linarith only [hp0]⟩

omit [LinearOrder ι] in
/-- One cutoff equal to one forces the combined cutoff to equal one. -/
theorem cutoffUnion_eq_one (S : Finset ι) (a : ι → ℝ)
    (h : ∃ i ∈ S, a i = 1) : cutoffUnion S a = 1 := by
  obtain ⟨i, hi, hai⟩ := h
  have hp : (∏ j ∈ S, (1 - a j)) = 0 :=
    Finset.prod_eq_zero hi (by rw [hai, sub_self])
  rw [cutoffUnion, hp, sub_zero]

omit [LinearOrder ι] in
/-- A family that vanishes at a point has zero combined cutoff there. -/
theorem cutoffUnion_eq_zero (S : Finset ι) (a : ι → ℝ)
    (h : ∀ i ∈ S, a i = 0) : cutoffUnion S a = 0 := by
  have hp : (∏ i ∈ S, (1 - a i)) = 1 :=
    Finset.prod_eq_one (fun i hi => by rw [h i hi, sub_zero])
  rw [cutoffUnion, hp, sub_self]

/-- Deleting earlier zero-valued cutoffs preserves the ordered weight exactly. -/
theorem orderedWeight_eq_of_zero_outside (S T : Finset ι) (a : ι → ℝ) (i : ι)
    (hT : T ⊆ S) (hz : ∀ j ∈ S, j ∉ T → j < i → a j = 0) :
    orderedWeight S a i = orderedWeight T a i := by
  have hs : T.filter (fun j => j < i) ⊆ S.filter (fun j => j < i) := by
    intro j hj
    obtain ⟨hj, hji⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hT hj, hji⟩
  have hp : (∏ j ∈ T.filter (fun j => j < i), (1 - a j)) =
      ∏ j ∈ S.filter (fun j => j < i), (1 - a j) := by
    apply Finset.prod_subset hs
    intro j hj hn
    obtain ⟨hjS, hji⟩ := Finset.mem_filter.mp hj
    have hjT : j ∉ T := fun h => hn (Finset.mem_filter.mpr ⟨h, hji⟩)
    rw [hz j hjS hjT hji, sub_zero]
  unfold orderedWeight
  rw [hp]

#print axioms sum_orderedWeight
#print axioms orderedWeight_mem_Icc
#print axioms cutoffUnion_mem_Icc
#print axioms cutoffUnion_eq_one
#print axioms cutoffUnion_eq_zero
#print axioms orderedWeight_eq_of_zero_outside

end
end GaloisForLFunctions.BiarithmeticGeometry.FiniteOrderedPartitions
