import GaloisForLFunctions.RHTower.WeilLogShiftCutMetric

/-! Every prefix cut has a sharp canonical transport bound. -/

open scoped BigOperators NNReal

noncomputable section
namespace RHTower

def finiteWeilCutCost {n : ℕ} (i : Fin n) (u v : Fin (n + 1)) : ℝ :=
  |finiteWeilCutIndicator i u - finiteWeilCutIndicator i v|

theorem finiteWeilCutIndicator_step {n : ℕ} (i e : Fin n) :
    finiteWeilCutIndicator i e.castSucc - finiteWeilCutIndicator i e.succ =
      if e = i then 1 else 0 := by
  by_cases he : e = i
  · subst e
    simp [finiteWeilCutIndicator_left, finiteWeilCutIndicator_right]
  · have hne : (e : ℕ) ≠ (i : ℕ) := fun h => he (Fin.ext h)
    by_cases hlt : (e : ℕ) < (i : ℕ)
    · have hl : (e : ℕ) ≤ (i : ℕ) := by omega
      have hr : (e : ℕ) + 1 ≤ (i : ℕ) := by omega
      simp [finiteWeilCutIndicator, he, hl, hr]
    · have hl : ¬(e : ℕ) ≤ (i : ℕ) := by omega
      have hr : ¬(e : ℕ) + 1 ≤ (i : ℕ) := by omega
      simp [finiteWeilCutIndicator, he, hl, hr]

theorem finiteWeilCanonicalEdge_cut_cost (r : ℕ) (i e : Fin (r + 1)) :
    finiteWeilCutCost i (finiteWeilCanonicalEdgeSource r e) (finiteWeilCanonicalEdgeTarget r e) =
      if e = i then 1 else 0 := by
  rw [finiteWeilCutCost, finiteWeilCanonicalEdge_difference, abs_mul,
    finiteWeilBinomialParity_abs, one_mul, finiteWeilCutIndicator_step]
  split_ifs <;> norm_num

theorem finiteWeilCanonicalProfiles_cut_dual (r : ℕ) (i : Fin (r + 1))
    (u v : Fin (r + 2)) :
    finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u -
      finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i v ≤ finiteWeilCutCost i u v := by
  rw [← mul_sub]
  calc
    _ ≤ |finiteWeilBinomialParity r i.castSucc *
        (finiteWeilCutIndicator i u - finiteWeilCutIndicator i v)| := le_abs_self _
    _ = _ := by rw [abs_mul, finiteWeilBinomialParity_abs, one_mul]; rfl

theorem finiteWeilCanonicalProfiles_cut_dual_pairing (r k : ℕ) (i : Fin (r + 1)) :
    (∑ u, (finiteWeilCanonicalPositiveNNProfile r k u : ℝ) *
      (finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u)) -
      (∑ u, (finiteWeilCanonicalNegativeNNProfile r k u : ℝ) *
        (finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u)) =
        finiteWeilCanonicalEdgeMass r k i := by
  calc
    _ = finiteWeilBinomialParity r i.castSucc *
        ((∑ u, (finiteWeilCanonicalPositiveNNProfile r k u : ℝ) * finiteWeilCutIndicator i u) -
          (∑ u, (finiteWeilCanonicalNegativeNNProfile r k u : ℝ) * finiteWeilCutIndicator i u)) := by
      simp only [mul_sub, Finset.mul_sum, mul_left_comm]
    _ = finiteWeilBinomialParity r i.castSucc * finiteWeilCanonicalPrefixDifference r k i := by
      rw [finiteWeilCanonicalProfiles_cut_pairing]
    _ = _ := by
      rw [finiteWeilCanonicalPrefixDifference_signed_mass, ← mul_assoc, ← pow_two,
        finiteWeilBinomialParity_sq, one_mul]

theorem finiteWeilCanonicalCoupling_cut_cost (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) (finiteWeilCutCost i) =
      finiteWeilCanonicalEdgeMass r k i := by
  rw [finiteWeilCanonicalCoupling_cost_eq]
  simp only [finiteWeilCanonicalEdge_cut_cost, mul_ite, mul_one, mul_zero]
  simp

theorem finiteWeilCanonicalTransport_cut_lower_bound (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) (i : Fin (r + 1)) :
    finiteWeilCanonicalEdgeMass r k i ≤ finiteWeilCouplingCost gamma (finiteWeilCutCost i) := by
  rw [← finiteWeilCanonicalProfiles_cut_dual_pairing r k i]
  exact finiteWeilCoupling_dual_bound gamma (finiteWeilCutCost i)
    (fun u => finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u)
    (finiteWeilCanonicalProfiles_cut_dual r i)

theorem finiteWeilCoupling_ordered_cost_eq {n : ℕ} {P Q : Fin (n + 1) → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (x : Fin (n + 1) → ℝ) (hmono : Monotone x) :
    finiteWeilCouplingCost gamma (fun u v => |x u - x v|) =
      ∑ i : Fin n, (x i.succ - x i.castSucc) * finiteWeilCouplingCost gamma (finiteWeilCutCost i) := by
  unfold finiteWeilCouplingCost
  simp_rw [finiteWeil_ordered_distance_eq_cuts x hmono, Finset.mul_sum]
  calc
    _ = ∑ u, ∑ i : Fin n, ∑ v, (gamma.plan u v : ℝ) *
        ((x i.succ - x i.castSucc) * |finiteWeilCutIndicator i u - finiteWeilCutIndicator i v|) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ u, ∑ v, (gamma.plan u v : ℝ) *
        ((x i.succ - x i.castSucc) * |finiteWeilCutIndicator i u - finiteWeilCutIndicator i v|) := by
      rw [Finset.sum_comm]
    _ = _ := by simp only [finiteWeilCutCost, mul_left_comm]

end RHTower
