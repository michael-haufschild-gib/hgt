import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalEdgeOrientation

/-! The explicit adjacent edge plan has exactly the two canonical probability marginals. -/

open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalEdgePlan (r k : ℕ) (u v : Fin (r + 2)) : ℝ :=
  ∑ i, if finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v
    then finiteWeilCanonicalEdgeMass r k i else 0

theorem finiteWeilCanonicalEdgePlan_nonneg (r k : ℕ) (u v : Fin (r + 2)) :
    0 ≤ finiteWeilCanonicalEdgePlan r k u v := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact (finiteWeilCanonicalEdgeMass_pos r k i).le
  · exact le_rfl

theorem finiteWeilCanonicalEdgePlan_row_sum (r k : ℕ) (u : Fin (r + 2)) :
    (∑ v, finiteWeilCanonicalEdgePlan r k u v) =
      ∑ i, if finiteWeilCanonicalEdgeSource r i = u then finiteWeilCanonicalEdgeMass r k i else 0 := by
  unfold finiteWeilCanonicalEdgePlan
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : finiteWeilCanonicalEdgeSource r i = u <;> simp [h]

theorem finiteWeilCanonicalEdgePlan_col_sum (r k : ℕ) (v : Fin (r + 2)) :
    (∑ u, finiteWeilCanonicalEdgePlan r k u v) =
      ∑ i, if finiteWeilCanonicalEdgeTarget r i = v then finiteWeilCanonicalEdgeMass r k i else 0 := by
  unfold finiteWeilCanonicalEdgePlan
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : finiteWeilCanonicalEdgeTarget r i = v <;> simp [h]

theorem finiteWeilCanonicalEdgePlan_divergence (r k : ℕ) (u : Fin (r + 2)) :
    (∑ v, finiteWeilCanonicalEdgePlan r k u v) -
      (∑ v, finiteWeilCanonicalEdgePlan r k v u) =
        finiteWeilCanonicalPositiveProfile r k u - finiteWeilCanonicalNegativeProfile r k u := by
  rw [finiteWeilCanonicalEdgePlan_row_sum, finiteWeilCanonicalEdgePlan_col_sum,
    ← Finset.sum_sub_distrib]
  have hp := finiteWeilCanonicalEdge_pairing r k (fun j => if j = u then 1 else 0)
  simpa [mul_sub, mul_ite] using hp

theorem finiteWeilCanonicalEdgePlan_row_zero (r k : ℕ) (u : Fin (r + 2))
    (hu : finiteWeilBinomialParity r u = -1) :
    (∑ v, finiteWeilCanonicalEdgePlan r k u v) = 0 := by
  rw [finiteWeilCanonicalEdgePlan_row_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : finiteWeilCanonicalEdgeSource r i ≠ u := by
    intro e
    have hs := finiteWeilCanonicalEdgeSource_parity r i
    rw [e, hu] at hs
    norm_num at hs
  simp [hne]

theorem finiteWeilCanonicalEdgePlan_col_zero (r k : ℕ) (u : Fin (r + 2))
    (hu : finiteWeilBinomialParity r u = 1) :
    (∑ v, finiteWeilCanonicalEdgePlan r k v u) = 0 := by
  rw [finiteWeilCanonicalEdgePlan_col_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : finiteWeilCanonicalEdgeTarget r i ≠ u := by
    intro e
    have ht := finiteWeilCanonicalEdgeTarget_parity r i
    rw [e, hu] at ht
    norm_num at ht
  simp [hne]

theorem finiteWeilCanonicalPositiveProfile_zero_of_parity (r k : ℕ) (u : Fin (r + 2))
    (hu : finiteWeilBinomialParity r u = -1) : finiteWeilCanonicalPositiveProfile r k u = 0 := by
  have hc := finiteWeilCanonicalCluster_parity r k u
  rw [hu, neg_one_mul] at hc
  have hz : |finiteWeilCanonicalCluster r k u| + finiteWeilCanonicalCluster r k u = 0 := by
    linarith only [hc]
  change (|finiteWeilCanonicalCluster r k u| + finiteWeilCanonicalCluster r k u) /
    finiteWeilAbsMass (finiteWeilCanonicalCluster r k) = 0
  rw [hz, zero_div]

theorem finiteWeilCanonicalNegativeProfile_zero_of_parity (r k : ℕ) (u : Fin (r + 2))
    (hu : finiteWeilBinomialParity r u = 1) : finiteWeilCanonicalNegativeProfile r k u = 0 := by
  have hc := finiteWeilCanonicalCluster_parity r k u
  rw [hu, one_mul] at hc
  change (|finiteWeilCanonicalCluster r k u| - finiteWeilCanonicalCluster r k u) /
    finiteWeilAbsMass (finiteWeilCanonicalCluster r k) = 0
  rw [← hc, sub_self, zero_div]

theorem finiteWeilCanonicalEdgePlan_marginals (r k : ℕ) (u : Fin (r + 2)) :
    (∑ v, finiteWeilCanonicalEdgePlan r k u v) = finiteWeilCanonicalPositiveProfile r k u ∧
      (∑ v, finiteWeilCanonicalEdgePlan r k v u) = finiteWeilCanonicalNegativeProfile r k u := by
  have hd := finiteWeilCanonicalEdgePlan_divergence r k u
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r u with hu | hu
  · have hcol := finiteWeilCanonicalEdgePlan_col_zero r k u hu
    have hQ := finiteWeilCanonicalNegativeProfile_zero_of_parity r k u hu
    constructor
    · simpa only [hcol, hQ, sub_zero] using hd
    · rw [hcol, hQ]
  · have hrow := finiteWeilCanonicalEdgePlan_row_zero r k u hu
    have hP := finiteWeilCanonicalPositiveProfile_zero_of_parity r k u hu
    constructor
    · rw [hrow, hP]
    · rw [hrow, hP] at hd
      linarith only [hd]

theorem finiteWeilCanonicalEdgePlan_zero_of_nonadjacent (r k : ℕ) (u v : Fin (r + 2))
    (huv : (u : ℕ) + 1 ≠ (v : ℕ)) (hvu : (v : ℕ) + 1 ≠ (u : ℕ)) :
    finiteWeilCanonicalEdgePlan r k u v = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hne : ¬(finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v) := by
    intro he
    have ha := finiteWeilCanonicalEdge_adjacent r i
    rw [he.1, he.2] at ha
    exact ha.elim huv hvu
  simp [hne]

theorem finiteWeilCanonicalEdgePlan_diagonal (r k : ℕ) (u : Fin (r + 2)) :
    finiteWeilCanonicalEdgePlan r k u u = 0 :=
  finiteWeilCanonicalEdgePlan_zero_of_nonadjacent r k u u (by omega) (by omega)

theorem finiteWeilCanonicalEdgePlan_total (r k : ℕ) :
    (∑ u, ∑ v, finiteWeilCanonicalEdgePlan r k u v) = 1 := by
  simp_rw [(finiteWeilCanonicalEdgePlan_marginals r k _).1]
  exact (finiteWeilCanonicalProfiles_spec r k).2.1

end RHTower
