import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalCoupling
import GaloisForLFunctions.RHTower.WeilLogShiftFiniteCouplingCost
/-! The canonical adjacent coupling attains the sharp index-transport minimum. -/

open scoped BigOperators NNReal
namespace RHTower

theorem finiteWeilCanonicalCoupling_cost_eq (r k : ℕ) (c : Fin (r + 2) → Fin (r + 2) → ℝ) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) c =
      ∑ i, finiteWeilCanonicalEdgeMass r k i *
        c (finiteWeilCanonicalEdgeSource r i) (finiteWeilCanonicalEdgeTarget r i) := by
  change (∑ u, ∑ v, finiteWeilCanonicalEdgePlan r k u v * c u v) = _
  unfold finiteWeilCanonicalEdgePlan
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ u, ∑ i, ∑ v,
        (if finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v
          then finiteWeilCanonicalEdgeMass r k i else 0) * c u v := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ u, ∑ v,
        (if finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v
          then finiteWeilCanonicalEdgeMass r k i else 0) * c u v := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hrow (u : Fin (r + 2)) :
          (∑ v, (if finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v
            then finiteWeilCanonicalEdgeMass r k i else 0) * c u v) =
          if finiteWeilCanonicalEdgeSource r i = u then
            finiteWeilCanonicalEdgeMass r k i * c u (finiteWeilCanonicalEdgeTarget r i) else 0 := by
        by_cases hu : finiteWeilCanonicalEdgeSource r i = u
        · simp [hu, ite_mul]
        · simp [hu]
      simp_rw [hrow]
      simp

noncomputable def finiteWeilIndexCost {n : ℕ} (u v : Fin n) : ℝ :=
  |((u : ℕ) : ℝ) - ((v : ℕ) : ℝ)|

theorem finiteWeilCanonicalEdge_index_cost (r : ℕ) (i : Fin (r + 1)) :
    finiteWeilIndexCost (finiteWeilCanonicalEdgeSource r i) (finiteWeilCanonicalEdgeTarget r i) = 1 := by
  unfold finiteWeilIndexCost
  rcases finiteWeilCanonicalEdge_adjacent r i with h | h
  · have hr : ((finiteWeilCanonicalEdgeSource r i : ℕ) : ℝ) + 1 =
        ((finiteWeilCanonicalEdgeTarget r i : ℕ) : ℝ) := by exact_mod_cast h
    rw [show ((finiteWeilCanonicalEdgeSource r i : ℕ) : ℝ) -
      ((finiteWeilCanonicalEdgeTarget r i : ℕ) : ℝ) = -1 by linarith only [hr]]
    norm_num
  · have hr : ((finiteWeilCanonicalEdgeTarget r i : ℕ) : ℝ) + 1 =
        ((finiteWeilCanonicalEdgeSource r i : ℕ) : ℝ) := by exact_mod_cast h
    rw [show ((finiteWeilCanonicalEdgeSource r i : ℕ) : ℝ) -
      ((finiteWeilCanonicalEdgeTarget r i : ℕ) : ℝ) = 1 by linarith only [hr]]
    norm_num

theorem finiteWeilCanonicalCoupling_index_cost (r k : ℕ) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) finiteWeilIndexCost = 1 := by
  rw [finiteWeilCanonicalCoupling_cost_eq]
  simp only [finiteWeilCanonicalEdge_index_cost, mul_one]
  exact finiteWeilCanonicalEdgeMass_sum r k

theorem finiteWeilBinomialParity_index_dual (r : ℕ) (u v : Fin (r + 2)) :
    finiteWeilBinomialParity r u / 2 - finiteWeilBinomialParity r v / 2 ≤ finiteWeilIndexCost u v := by
  by_cases he : u = v
  · subst v
    simp [finiteWeilIndexCost]
  · have hval : (u : ℕ) ≠ (v : ℕ) := fun e => he (Fin.ext e)
    have hdist : (1 : ℝ) ≤ finiteWeilIndexCost u v := by
      unfold finiteWeilIndexCost
      by_cases hlt : (u : ℕ) < (v : ℕ)
      · have hr : ((u : ℕ) : ℝ) + 1 ≤ ((v : ℕ) : ℝ) := by
          exact_mod_cast (show (u : ℕ) + 1 ≤ (v : ℕ) by omega)
        rw [abs_of_nonpos (by linarith only [hr])]
        linarith only [hr]
      · have hr : ((v : ℕ) : ℝ) + 1 ≤ ((u : ℕ) : ℝ) := by
          exact_mod_cast (show (v : ℕ) + 1 ≤ (u : ℕ) by omega)
        rw [abs_of_nonneg (by linarith only [hr])]
        linarith only [hr]
    have hu := abs_le.mp (le_of_eq (finiteWeilBinomialParity_abs r u))
    have hv := abs_le.mp (le_of_eq (finiteWeilBinomialParity_abs r v))
    linarith only [hu.2, hv.1, hdist]

theorem finiteWeilCanonicalProfiles_index_dual_pairing (r k : ℕ) :
    (∑ u, (finiteWeilCanonicalPositiveNNProfile r k u : ℝ) * (finiteWeilBinomialParity r u / 2)) -
      (∑ u, (finiteWeilCanonicalNegativeNNProfile r k u : ℝ) * (finiteWeilBinomialParity r u / 2)) = 1 := by
  change (∑ u, finiteWeilCanonicalPositiveProfile r k u * (finiteWeilBinomialParity r u / 2)) -
    (∑ u, finiteWeilCanonicalNegativeProfile r k u * (finiteWeilBinomialParity r u / 2)) = 1
  calc
    _ = (∑ u, (finiteWeilCanonicalPositiveProfile r k u - finiteWeilCanonicalNegativeProfile r k u) *
        finiteWeilBinomialParity r u) / 2 := by
      simp only [Finset.sum_div, sub_mul, Finset.sum_sub_distrib, mul_div_assoc, sub_div]
    _ = 1 := by rw [finiteWeilCanonicalProfiles_parity_pairing]; norm_num

theorem finiteWeilCanonicalCoupling_index_lower_bound (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) :
    1 ≤ finiteWeilCouplingCost gamma finiteWeilIndexCost := by
  rw [← finiteWeilCanonicalProfiles_index_dual_pairing r k]
  exact finiteWeilCoupling_dual_bound gamma finiteWeilIndexCost
    (fun u => finiteWeilBinomialParity r u / 2) (finiteWeilBinomialParity_index_dual r)

theorem finiteWeilCanonicalCoupling_index_optimal (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) finiteWeilIndexCost ≤
      finiteWeilCouplingCost gamma finiteWeilIndexCost := by
  rw [finiteWeilCanonicalCoupling_index_cost]
  exact finiteWeilCanonicalCoupling_index_lower_bound r k gamma

end RHTower
