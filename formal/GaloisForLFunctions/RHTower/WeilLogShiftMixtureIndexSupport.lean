import GaloisForLFunctions.RHTower.WeilLogShiftMixtureCoupling
import GaloisForLFunctions.RHTower.WeilLogShiftAdjacentUniqueness

/-! Exact cut flux and support of every optimal oriented mixture coupling. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilIndexCost_self {n : ℕ} (u : Fin n) : finiteWeilIndexCost u u = 0 := by
  simp [finiteWeilIndexCost]

theorem finiteWeilIndexCost_symm {n : ℕ} (u v : Fin n) :
    finiteWeilIndexCost u v = finiteWeilIndexCost v u := abs_sub_comm _ _

theorem finiteWeilOrientedMixtureCoupling_index_cost (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (hba : (b : ℝ) ≤ (a : ℝ)) :
    finiteWeilCouplingCost (finiteWeilOrientedMixtureCoupling r k a b hba) finiteWeilIndexCost =
      (a : ℝ) - (b : ℝ) := by
  rw [finiteWeilOrientedMixtureCoupling_cost_eq r k a b hba _ finiteWeilIndexCost_self,
    finiteWeilCanonicalCoupling_index_cost, mul_one]

theorem finiteWeilCanonicalMixtureNNProfile_index_pairing (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    (∑ u, (finiteWeilCanonicalMixtureNNProfile r k a u : ℝ) * (finiteWeilBinomialParity r u / 2)) -
      (∑ u, (finiteWeilCanonicalMixtureNNProfile r k b u : ℝ) * (finiteWeilBinomialParity r u / 2)) =
      (a : ℝ) - (b : ℝ) := by
  rw [finiteWeilCanonicalMixtureNNProfile_pairing,
    finiteWeilCanonicalProfiles_index_dual_pairing, mul_one]

theorem finiteWeilOrientedMixtureTransport_index_lower_bound (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) :
    (a : ℝ) - (b : ℝ) ≤ finiteWeilCouplingCost gamma finiteWeilIndexCost := by
  rw [← finiteWeilCanonicalMixtureNNProfile_index_pairing r k a b]
  exact finiteWeilCoupling_dual_bound gamma finiteWeilIndexCost
    (fun u => finiteWeilBinomialParity r u / 2) (finiteWeilBinomialParity_index_dual r)

theorem finiteWeilOrientedMixtureTransport_index_banded (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b))
    (hopt : finiteWeilCouplingCost gamma finiteWeilIndexCost = (a : ℝ) - (b : ℝ))
    (u v : Fin (r + 2)) (hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ)) :
    gamma.plan u v = 0 := by
  apply finiteWeilCoupling_zero_of_strict_dual gamma finiteWeilIndexCost
    (fun j => finiteWeilBinomialParity r j / 2) (finiteWeilBinomialParity_index_dual r)
  · rw [finiteWeilCanonicalMixtureNNProfile_index_pairing]
    exact hopt
  · exact finiteWeilBinomialParity_index_dual_strict r u v hfar

theorem finiteWeilOrientedMixtureTransport_reverse_edge_zero (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b))
    (hopt : finiteWeilCouplingCost gamma finiteWeilIndexCost = (a : ℝ) - (b : ℝ))
    (i : Fin (r + 1)) :
    gamma.plan (finiteWeilCanonicalEdgeTarget r i) (finiteWeilCanonicalEdgeSource r i) = 0 := by
  apply finiteWeilCoupling_zero_of_strict_dual gamma finiteWeilIndexCost
    (fun j => finiteWeilBinomialParity r j / 2) (finiteWeilBinomialParity_index_dual r)
  · rw [finiteWeilCanonicalMixtureNNProfile_index_pairing]
    exact hopt
  · rw [finiteWeilIndexCost_symm, finiteWeilCanonicalEdge_index_cost,
      finiteWeilCanonicalEdgeTarget_parity, finiteWeilCanonicalEdgeSource_parity]
    norm_num

theorem finiteWeilMixtureCoupling_cut_flux (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b))
    (hband : ∀ u v : Fin (r + 2), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) → gamma.plan u v = 0)
    (i : Fin (r + 1)) :
    (gamma.plan i.castSucc i.succ : ℝ) - (gamma.plan i.succ i.castSucc : ℝ) =
      ((a : ℝ) - (b : ℝ)) * finiteWeilCanonicalPrefixDifference r k i := by
  have hp := finiteWeilCoupling_pairing gamma (finiteWeilCutIndicator i)
  rw [finiteWeilCanonicalMixtureNNProfile_pairing, finiteWeilCanonicalProfiles_cut_pairing] at hp
  unfold finiteWeilCouplingCost at hp
  rw [finiteWeil_banded_cut_pairing (fun u v => (gamma.plan u v : ℝ))
    (fun u v h => by rw [hband u v h]; rfl)] at hp
  exact hp.symm

theorem finiteWeilOrientedMixtureTransport_edge_mass (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b))
    (hopt : finiteWeilCouplingCost gamma finiteWeilIndexCost = (a : ℝ) - (b : ℝ))
    (i : Fin (r + 1)) :
    (gamma.plan (finiteWeilCanonicalEdgeSource r i) (finiteWeilCanonicalEdgeTarget r i) : ℝ) =
      ((a : ℝ) - (b : ℝ)) * finiteWeilCanonicalEdgeMass r k i := by
  have hp := finiteWeilMixtureCoupling_cut_flux r k a b gamma
    (finiteWeilOrientedMixtureTransport_index_banded r k a b gamma hopt) i
  have hz := finiteWeilOrientedMixtureTransport_reverse_edge_zero r k a b gamma hopt i
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r i.castSucc with hs | hs
  · simp only [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, hs, ↓reduceIte] at hz ⊢
    have hz' : (gamma.plan i.succ i.castSucc : ℝ) = 0 := congrArg NNReal.toReal hz
    rw [hz', sub_zero, finiteWeilCanonicalPrefixDifference_signed_mass, hs, one_mul] at hp
    exact hp
  · norm_num [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, hs] at hz ⊢
    have hz' : (gamma.plan i.castSucc i.succ : ℝ) = 0 := congrArg NNReal.toReal hz
    rw [hz', finiteWeilCanonicalPrefixDifference_signed_mass, hs, neg_one_mul] at hp
    linarith only [hp]

end RHTower
