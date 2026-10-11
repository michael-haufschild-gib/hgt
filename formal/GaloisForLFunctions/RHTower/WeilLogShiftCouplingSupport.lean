import GaloisForLFunctions.RHTower.WeilLogShiftCouplingSlack
import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalIndexTransport

/-! Canonical marginal parity fixes orientation; index optimality forbids long edges. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilCanonicalTransport_source_zero (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) (u v : Fin (r + 2))
    (hu : finiteWeilBinomialParity r u = -1) : gamma.plan u v = 0 := by
  have hr := congrArg NNReal.toReal (gamma.row u)
  simp only [NNReal.coe_sum, finiteWeilCanonicalPositiveNNProfile, NNReal.coe_mk] at hr
  rw [finiteWeilCanonicalPositiveProfile_zero_of_parity r k u hu] at hr
  apply NNReal.coe_injective
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => (gamma.plan u j).coe_nonneg)).mp hr v (Finset.mem_univ v)

theorem finiteWeilCanonicalTransport_target_zero (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) (u v : Fin (r + 2))
    (hv : finiteWeilBinomialParity r v = 1) : gamma.plan u v = 0 := by
  have hc := congrArg NNReal.toReal (gamma.col v)
  simp only [NNReal.coe_sum, finiteWeilCanonicalNegativeNNProfile, NNReal.coe_mk] at hc
  rw [finiteWeilCanonicalNegativeProfile_zero_of_parity r k v hv] at hc
  apply NNReal.coe_injective
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => (gamma.plan j v).coe_nonneg)).mp hc u (Finset.mem_univ u)

theorem finiteWeilCanonicalTransport_diagonal (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) (u : Fin (r + 2)) : gamma.plan u u = 0 := by
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r u with hu | hu
  · exact finiteWeilCanonicalTransport_target_zero r k gamma u u hu
  · exact finiteWeilCanonicalTransport_source_zero r k gamma u u hu

theorem finiteWeilCanonicalTransport_reverse_edge_zero (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) (i : Fin (r + 1)) :
    gamma.plan (finiteWeilCanonicalEdgeTarget r i) (finiteWeilCanonicalEdgeSource r i) = 0 :=
  finiteWeilCanonicalTransport_source_zero r k gamma _ _ (finiteWeilCanonicalEdgeTarget_parity r i)

theorem finiteWeilBinomialParity_index_dual_strict (r : ℕ) (u v : Fin (r + 2))
    (hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ)) :
    finiteWeilBinomialParity r u / 2 - finiteWeilBinomialParity r v / 2 < finiteWeilIndexCost u v := by
  have hdist : (1 : ℝ) < finiteWeilIndexCost u v := by
    unfold finiteWeilIndexCost
    rcases hfar with h | h
    · have hr : ((u : ℕ) : ℝ) + 1 < ((v : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith only [hr])]
      linarith only [hr]
    · have hr : ((v : ℕ) : ℝ) + 1 < ((u : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith only [hr])]
      linarith only [hr]
  have hu := abs_le.mp (le_of_eq (finiteWeilBinomialParity_abs r u))
  have hv := abs_le.mp (le_of_eq (finiteWeilBinomialParity_abs r v))
  linarith only [hu.2, hv.1, hdist]

theorem finiteWeilCanonicalTransport_index_banded (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k))
    (hopt : finiteWeilCouplingCost gamma finiteWeilIndexCost = 1) (u v : Fin (r + 2))
    (hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ)) : gamma.plan u v = 0 := by
  have ha : finiteWeilCouplingCost gamma finiteWeilIndexCost =
      (∑ a, (finiteWeilCanonicalPositiveNNProfile r k a : ℝ) * (finiteWeilBinomialParity r a / 2)) -
        (∑ b, (finiteWeilCanonicalNegativeNNProfile r k b : ℝ) * (finiteWeilBinomialParity r b / 2)) := by
    rw [hopt, finiteWeilCanonicalProfiles_index_dual_pairing]
  exact finiteWeilCoupling_zero_of_strict_dual gamma finiteWeilIndexCost
    (fun a => finiteWeilBinomialParity r a / 2) (finiteWeilBinomialParity_index_dual r) ha u v
    (finiteWeilBinomialParity_index_dual_strict r u v hfar)

end RHTower
