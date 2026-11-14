import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.GreedyProductContainers

/-!
# Subproduct growth outside the final stabilizer

Saturating every partial subproduct sheet by the final stabilizer makes all partial
stabilizers equal. Each factor outside that subgroup adds at least one entire coset.
Thus the number of such factors, counted with multiplicity, is less than the number
of occupied stabilizer cosets. This is an elementary form of the stabilizer-container
mechanism; subgroup generation alone does not provide this bound.
-/

open Finset
open scoped Pointwise

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

open HTGeometry.AddComb

variable {G ι : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [DecidableEq ι]

private theorem saturated_subproducts_bound (q : ι → G) (H : Finset G)
    (hH : IsSubgroupFinset H) (I : Finset ι) :
    mulStab (subproducts q I * H) ⊆ H →
      ((I.filter fun i => q i ∉ H).card + 1) * H.card ≤ (subproducts q I * H).card := by
  induction I using Finset.induction_on with
  | empty => simp [subproducts]
  | @insert i I hi ih =>
    intro hperiod
    have hstep : subproducts q (insert i I) * H =
        subproducts q I * H ∪ q i • (subproducts q I * H) := by
      rw [subproducts_insert q I i hi, union_mul, smul_mul_assoc]
    have hperiodI : mulStab (subproducts q I * H) ⊆ H := by
      intro g hg
      apply hperiod
      rw [mem_mulStab, hstep]
      have hfix := mem_mulStab.mp hg
      rw [smul_finset_union, smul_comm g (q i), hfix]
    have hbase := ih hperiodI
    have hsub : subproducts q I * H ⊆ subproducts q (insert i I) * H := by
      rw [hstep]
      exact subset_union_left
    by_cases hqi : q i ∈ H
    · have hfilter : (insert i I).filter (fun j => q j ∉ H) = I.filter (fun j => q j ∉ H) := by
        simp only [filter_insert, hqi, not_true_eq_false, if_false]
      rw [hfilter]
      exact hbase.trans (card_le_card hsub)
    · have hlt : (subproducts q I * H).card < (subproducts q (insert i I) * H).card := by
        apply lt_of_le_of_ne (card_le_card hsub)
        intro heq
        have heqset := eq_of_subset_of_card_le hsub heq.ge
        have hshift : q i • (subproducts q I * H) ⊆ subproducts q I * H := by
          rw [heqset, hstep]
          exact subset_union_right
        have hfix := eq_of_subset_of_card_le hshift (by rw [card_smul_finset])
        exact hqi (hperiodI (mem_mulStab.mpr hfix))
      obtain ⟨m, hm⟩ := hH.card_dvd_card_mul (subproducts q I)
      obtain ⟨n, hn⟩ := hH.card_dvd_card_mul (subproducts q (insert i I))
      have hmn : m < n := by
        rw [hm, hn] at hlt
        exact (Nat.mul_lt_mul_left hH.card_pos').mp hlt
      have hgain : (subproducts q I * H).card + H.card ≤
          (subproducts q (insert i I) * H).card := by
        rw [hm, hn]
        have hmul := Nat.mul_le_mul_left H.card (Nat.succ_le_of_lt hmn)
        nlinarith only [hmul]
      have hiF : i ∉ I.filter (fun j => q j ∉ H) := fun h => hi (mem_filter.mp h).1
      rw [filter_insert, if_pos hqi, card_insert_of_notMem hiF]
      nlinarith only [hbase, hgain]

/-- Every occurrence outside the final stabilizer contributes a new stabilizer coset. -/
theorem subproduct_stabilizer_growth (q : ι → G) (I : Finset ι) :
    ((I.filter fun i => q i ∉ mulStab (subproducts q I)).card + 1) *
      (mulStab (subproducts q I)).card ≤ (subproducts q I).card := by
  have h := saturated_subproducts_bound q (mulStab (subproducts q I))
    (isSubgroupFinset_mulStab _) I
  simpa only [mul_mulStab] using h (by simp only [mul_mulStab]; exact Subset.rfl)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup
