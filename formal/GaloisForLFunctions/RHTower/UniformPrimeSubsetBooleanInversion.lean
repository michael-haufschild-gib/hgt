import GaloisForLFunctions.RHTower.UniformPrimeSubsetEnergy

/-!
# Boolean inversion for finite label energy

The complete alternating response of a finite label energy at the empty core
isolates exactly the pairs of original source labels whose symmetric difference
is the selected Boolean packet.  When every source coefficient has the parity
of its label, this alternating response is nonnegative at every finite order.

This is finite algebra: it assumes neither a selection schedule nor an
analytic estimate.
-/

noncomputable section
open Finset
open scoped symmDiff
namespace RHTower

private theorem booleanIndicatorCoefficient
    {α : Type*} [DecidableEq α] (A D : Finset α) :
    (-1 : ℝ) ^ A.card *
        (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card * (if D ⊆ B then 1 else 0)) =
      if D = A then 1 else 0 := by
  classical
  induction A using Finset.induction_on generalizing D with
  | empty => simp
  | @insert p A hp ih =>
      by_cases hDp : p ∈ D
      · let E := D.erase p
        have hpE : p ∉ E := by simp [E]
        have hD : D = insert p E := by
          simp only [E, insert_erase hDp]
        rw [hD]
        rw [Finset.sum_powerset_insert hp, Finset.card_insert_of_notMem hp, pow_succ]
        have hleft :
            (∑ B ∈ A.powerset,
              (-1 : ℝ) ^ B.card * (if insert p E ⊆ B then 1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro B hB
          have hpB : p ∉ B := fun h => hp (Finset.mem_powerset.mp hB h)
          simp [Finset.insert_subset_iff, hpB]
        have hright :
            (∑ B ∈ A.powerset,
              (-1 : ℝ) ^ (insert p B).card *
                (if insert p E ⊆ insert p B then 1 else 0)) =
              -(∑ B ∈ A.powerset,
                (-1 : ℝ) ^ B.card * (if E ⊆ B then 1 else 0)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro B hB
          have hpB : p ∉ B := fun h => hp (Finset.mem_powerset.mp hB h)
          have hsub : insert p E ⊆ insert p B ↔ E ⊆ B := by
            simp [Finset.subset_insert_iff, hpE]
          rw [Finset.card_insert_of_notMem hpB, pow_succ]
          by_cases hEB : E ⊆ B
          · have hEB' : insert p E ⊆ insert p B := hsub.mpr hEB
            simp [hEB, hEB']
          · have hEB' : ¬ insert p E ⊆ insert p B := fun h => hEB (hsub.mp h)
            simp [hEB, hEB']
        rw [hleft, hright]
        have hrec := ih E
        calc
          (-1 : ℝ) ^ A.card * (-1) *
              (0 + -(∑ B ∈ A.powerset,
                (-1 : ℝ) ^ B.card * (if E ⊆ B then 1 else 0))) =
              (-1 : ℝ) ^ A.card *
                (∑ B ∈ A.powerset,
                  (-1 : ℝ) ^ B.card * (if E ⊆ B then 1 else 0)) := by ring
          _ = if insert p E = insert p A then 1 else 0 := by
            rw [hrec]
            have hinj : insert p E = insert p A ↔ E = A := by
              constructor
              · intro h
                have h' := congrArg (fun V : Finset α => V.erase p) h
                simpa [hpE, hp] using h'
              · intro h
                simp [h]
            by_cases hEA : E = A
            · have hIns : insert p E = insert p A := hinj.mpr hEA
              simp [hEA]
            · have hIns : insert p E ≠ insert p A := fun h => hEA (hinj.mp h)
              simp [hEA, hIns]
      · rw [Finset.sum_powerset_insert hp, Finset.card_insert_of_notMem hp, pow_succ]
        have hcancel :
            (∑ B ∈ A.powerset,
              (-1 : ℝ) ^ B.card * (if D ⊆ B then 1 else 0)) +
            (∑ B ∈ A.powerset,
              (-1 : ℝ) ^ (insert p B).card *
                (if D ⊆ insert p B then 1 else 0)) = 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_eq_zero
          intro B hB
          have hpB : p ∉ B := fun h => hp (Finset.mem_powerset.mp hB h)
          have hsub : D ⊆ insert p B ↔ D ⊆ B := by
            rw [Finset.subset_insert_iff]
            simp [hDp]
          rw [Finset.card_insert_of_notMem hpB, pow_succ]
          by_cases hDB : D ⊆ B
          · have hDB' : D ⊆ insert p B := hsub.mpr hDB
            simp [hDB, hDB']
          · have hDB' : ¬ D ⊆ insert p B := fun h => hDB (hsub.mp h)
            simp [hDB, hDB']
        rw [hcancel]
        have hne : D ≠ insert p A := by
          intro h
          have hm : p ∈ D := h.symm ▸ mem_insert_self p A
          exact hDp hm
        simp [hne]

private theorem booleanIndicatorCoefficient_mul
    {α : Type*} [DecidableEq α] (A D : Finset α) (x : ℝ) :
    (-1 : ℝ) ^ A.card *
        (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card * (if D ⊆ B then x else 0)) =
      if D = A then x else 0 := by
  calc
    (-1 : ℝ) ^ A.card *
        (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card * (if D ⊆ B then x else 0)) =
        ∑ B ∈ A.powerset,
          ((-1 : ℝ) ^ A.card * (-1 : ℝ) ^ B.card * (if D ⊆ B then x else 0)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro B _
            ring
    _ = ∑ B ∈ A.powerset,
          (((-1 : ℝ) ^ A.card * (-1 : ℝ) ^ B.card *
            (if D ⊆ B then 1 else 0)) * x) := by
          apply Finset.sum_congr rfl
          intro B _
          by_cases h : D ⊆ B <;> simp [h]
    _ = ((-1 : ℝ) ^ A.card *
        (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card * (if D ⊆ B then 1 else 0))) * x := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro B _
          ring
    _ = _ := by
      rw [booleanIndicatorCoefficient]
      split <;> simp_all

/-- A normalized Boolean difference isolates precisely the pairs whose
symmetric difference is the selected packet. -/
theorem subsetLabelEnergy_boolean_difference_eq_pairs
    {α ι : Type*} [DecidableEq α] (U : Finset α) (I : Finset ι)
    (a : ι → Finset α) (c : ι → ℝ)
    (ha : ∀ i ∈ I, a i ⊆ U) (A : Finset α) :
    (-1 : ℝ) ^ A.card *
        (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card * subsetLabelEnergy U I a c B) =
      ∑ i ∈ I, ∑ j ∈ I,
        if a i ∆ a j = A then c i * c j else 0 := by
  simp_rw [subsetLabelEnergy_eq_pairs U I a c ha]
  calc
    (-1 : ℝ) ^ A.card *
        (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card *
          (∑ i ∈ I, ∑ j ∈ I,
            if a i ∆ a j ⊆ B then c i * c j else 0)) =
        ∑ B ∈ A.powerset, ∑ i ∈ I, ∑ j ∈ I,
          (-1 : ℝ) ^ A.card * ((-1 : ℝ) ^ B.card *
            (if a i ∆ a j ⊆ B then c i * c j else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B hB
          rw [← mul_assoc, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ i ∈ I, ∑ B ∈ A.powerset, ∑ j ∈ I,
          (-1 : ℝ) ^ A.card * ((-1 : ℝ) ^ B.card *
            (if a i ∆ a j ⊆ B then c i * c j else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ B ∈ A.powerset,
          (-1 : ℝ) ^ A.card * ((-1 : ℝ) ^ B.card *
            (if a i ∆ a j ⊆ B then c i * c j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ∑ j ∈ I,
          (-1 : ℝ) ^ A.card *
            (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card *
              (if a i ∆ a j ⊆ B then c i * c j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact booleanIndicatorCoefficient_mul A (a i ∆ a j) (c i * c j)

private theorem card_add_eq_card_symmDiff_add_twice_inter
    {α : Type*} [DecidableEq α] (S T : Finset α) :
    S.card + T.card = (S ∆ T).card + 2 * (S ∩ T).card := by
  have hdisj : Disjoint (S \ T) (T \ S) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    exact (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, card_union_of_disjoint hdisj]
  have hS := card_sdiff_add_card_inter S T
  have hT := card_sdiff_add_card_inter T S
  rw [inter_comm T S] at hT
  omega

/-- A parity-oriented source has nonnegative alternating energy response on
every finite Boolean packet at the original core. -/
theorem subsetLabelEnergy_booleanAlternating_nonneg_of_parity
    {α ι : Type*} [DecidableEq α] (U : Finset α) (I : Finset ι)
    (a : ι → Finset α) (c : ι → ℝ)
    (ha : ∀ i ∈ I, a i ⊆ U)
    (hparity : ∀ i ∈ I, 0 ≤ (-1 : ℝ) ^ (a i).card * c i)
    (A : Finset α) :
    0 ≤ ∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card * subsetLabelEnergy U I a c B := by
  have hdiff := subsetLabelEnergy_boolean_difference_eq_pairs U I a c ha A
  have hsign : (-1 : ℝ) ^ A.card * (-1 : ℝ) ^ A.card = 1 := by
    rw [← pow_add, show A.card + A.card = 2 * A.card by omega, pow_mul]
    norm_num
  calc
    0 ≤ ∑ i ∈ I, ∑ j ∈ I,
        if a i ∆ a j = A then (-1 : ℝ) ^ A.card * (c i * c j) else 0 := by
          apply Finset.sum_nonneg
          intro i hi
          apply Finset.sum_nonneg
          intro j hj
          by_cases h : a i ∆ a j = A
          · rw [if_pos h]
            have hcard := card_add_eq_card_symmDiff_add_twice_inter (a i) (a j)
            rw [h] at hcard
            have hmul := mul_nonneg (hparity i hi) (hparity j hj)
            have heq : (-1 : ℝ) ^ A.card * (c i * c j) =
                ((-1 : ℝ) ^ (a i).card * c i) * ((-1 : ℝ) ^ (a j).card * c j) := by
              calc
                (-1 : ℝ) ^ A.card * (c i * c j) =
                    (-1 : ℝ) ^ (A.card + 2 * (a i ∩ a j).card) *
                      (c i * c j) := by
                        rw [pow_add, pow_mul]
                        norm_num
                _ = (-1 : ℝ) ^ ((a i).card + (a j).card) *
                      (c i * c j) := by rw [hcard]
                _ = ((-1 : ℝ) ^ (a i).card * c i) *
                      ((-1 : ℝ) ^ (a j).card * c j) := by
                        rw [pow_add]
                        ring
            rw [heq]
            exact hmul
          · simp [h]
    _ = (-1 : ℝ) ^ A.card *
        (∑ i ∈ I, ∑ j ∈ I,
          if a i ∆ a j = A then c i * c j else 0) := by
          rw [Finset.mul_sum]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : a i ∆ a j = A <;> simp [h]
    _ = (-1 : ℝ) ^ A.card *
        ((-1 : ℝ) ^ A.card *
          (∑ B ∈ A.powerset,
            (-1 : ℝ) ^ B.card * subsetLabelEnergy U I a c B)) := by rw [hdiff]
    _ = _ := by rw [← mul_assoc, hsign, one_mul]

end RHTower
