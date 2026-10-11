import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalIndexTransport

/-! The midpoint profile is the uniform endpoint pushforward of the canonical edge probability. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilCoupling_add_pairing {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (f g : ι → ℝ) :
    (∑ u, (P u : ℝ) * f u) + (∑ v, (Q v : ℝ) * g v) =
      finiteWeilCouplingCost gamma (fun u v => f u + g v) := by
  have hr : (∑ u, ∑ v, (gamma.plan u v : ℝ) * f u) = ∑ u, (P u : ℝ) * f u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [← Finset.sum_mul]
    have h := congrArg NNReal.toReal (gamma.row u)
    simp only [NNReal.coe_sum] at h
    rw [h]
  have hc : (∑ u, ∑ v, (gamma.plan u v : ℝ) * g v) = ∑ v, (Q v : ℝ) * g v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.sum_mul]
    have h := congrArg NNReal.toReal (gamma.col v)
    simp only [NNReal.coe_sum] at h
    rw [h]
  simp only [finiteWeilCouplingCost, mul_add, Finset.sum_add_distrib, hr, hc]

theorem finiteWeilCanonicalEdge_sum (r : ℕ) (i : Fin (r + 1)) (f : Fin (r + 2) → ℝ) :
    f (finiteWeilCanonicalEdgeSource r i) + f (finiteWeilCanonicalEdgeTarget r i) =
      f i.castSucc + f i.succ := by
  by_cases hs : finiteWeilBinomialParity r i.castSucc = 1
  · rw [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, if_pos hs, if_pos hs]
  · rw [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, if_neg hs, if_neg hs]
    ring

theorem finiteWeilCanonicalMixture_midpoint_edge_pairing (r k : ℕ) (f : Fin (r + 2) → ℝ) :
    (∑ u, finiteWeilCanonicalMixture r k (1 / 2) u * f u) =
      (∑ i, finiteWeilCanonicalEdgeMass r k i * (f i.castSucc + f i.succ)) / 2 := by
  have hc := finiteWeilCoupling_add_pairing (finiteWeilCanonicalCoupling r k) f f
  change (∑ u, finiteWeilCanonicalPositiveProfile r k u * f u) +
    (∑ u, finiteWeilCanonicalNegativeProfile r k u * f u) = _ at hc
  rw [finiteWeilCanonicalCoupling_cost_eq] at hc
  simp_rw [finiteWeilCanonicalEdge_sum] at hc
  calc
    _ = ((∑ u, finiteWeilCanonicalPositiveProfile r k u * f u) +
        (∑ u, finiteWeilCanonicalNegativeProfile r k u * f u)) / 2 := by
      simp only [finiteWeilCanonicalMixture, add_mul, mul_assoc, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      ring
    _ = _ := congrArg (fun z : ℝ => z / 2) hc

theorem finiteWeilCanonicalMixture_midpoint_edge_profile (r k : ℕ) (u : Fin (r + 2)) :
    finiteWeilCanonicalMixture r k (1 / 2) u =
      ((∑ i : Fin (r + 1), if i.castSucc = u then finiteWeilCanonicalEdgeMass r k i else 0) +
        (∑ i : Fin (r + 1), if i.succ = u then finiteWeilCanonicalEdgeMass r k i else 0)) / 2 := by
  have h := finiteWeilCanonicalMixture_midpoint_edge_pairing r k (fun v => if v = u then (1 : ℝ) else 0)
  simpa [mul_add, mul_ite, Finset.sum_add_distrib] using h

end RHTower
