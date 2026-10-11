import GaloisForLFunctions.RHTower.WeilLogShiftBandedCut
import GaloisForLFunctions.RHTower.WeilLogShiftCouplingSupport

/-! Every adjacent canonical coupling is forced by its cut fluxes; the index optimum is unique. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilCanonicalEdge_covers_adjacent (r : ℕ) (u v : Fin (r + 2))
    (hadj : (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)) :
    ∃ i : Fin (r + 1),
      (finiteWeilCanonicalEdgeSource r i = u ∧ finiteWeilCanonicalEdgeTarget r i = v) ∨
        (finiteWeilCanonicalEdgeSource r i = v ∧ finiteWeilCanonicalEdgeTarget r i = u) := by
  have hforward (a b : Fin (r + 2)) (hab : (a : ℕ) + 1 = (b : ℕ)) :
      ∃ i : Fin (r + 1),
        (finiteWeilCanonicalEdgeSource r i = a ∧ finiteWeilCanonicalEdgeTarget r i = b) ∨
          (finiteWeilCanonicalEdgeSource r i = b ∧ finiteWeilCanonicalEdgeTarget r i = a) := by
    let i : Fin (r + 1) := ⟨a, by have hb := b.isLt; omega⟩
    have hl : i.castSucc = a := Fin.ext rfl
    have hr : i.succ = b := Fin.ext hab
    refine ⟨i, ?_⟩
    by_cases hs : finiteWeilBinomialParity r i.castSucc = 1
    · exact Or.inl ⟨by rw [finiteWeilCanonicalEdgeSource, if_pos hs, hl],
        by rw [finiteWeilCanonicalEdgeTarget, if_pos hs, hr]⟩
    · exact Or.inr ⟨by rw [finiteWeilCanonicalEdgeSource, if_neg hs, hr],
        by rw [finiteWeilCanonicalEdgeTarget, if_neg hs, hl]⟩
  rcases hadj with h | h
  · exact hforward u v h
  · obtain ⟨i, hi⟩ := hforward v u h
    exact ⟨i, hi.elim Or.inr Or.inl⟩

theorem finiteWeilCanonicalTransport_edge_mass (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k))
    (hband : ∀ u v : Fin (r + 2), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) → gamma.plan u v = 0)
    (i : Fin (r + 1)) :
    (gamma.plan (finiteWeilCanonicalEdgeSource r i) (finiteWeilCanonicalEdgeTarget r i) : ℝ) =
      finiteWeilCanonicalEdgeMass r k i := by
  have hp := finiteWeilCanonicalCoupling_cut_flux r k gamma hband i
  have hz := finiteWeilCanonicalTransport_reverse_edge_zero r k gamma i
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r i.castSucc with hs | hs
  · simp only [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, hs, ↓reduceIte] at hz ⊢
    have hz' : (gamma.plan i.succ i.castSucc : ℝ) = 0 := congrArg NNReal.toReal hz
    rw [hz', sub_zero, finiteWeilCanonicalPrefixDifference_signed_mass, hs, one_mul] at hp
    exact hp
  · norm_num [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, hs] at hz ⊢
    have hz' : (gamma.plan i.castSucc i.succ : ℝ) = 0 := congrArg NNReal.toReal hz
    rw [hz', finiteWeilCanonicalPrefixDifference_signed_mass, hs, neg_one_mul] at hp
    linarith only [hp]

theorem finiteWeilCanonicalTransport_eq_of_banded (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k))
    (hband : ∀ u v : Fin (r + 2), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) → gamma.plan u v = 0) :
    gamma = finiteWeilCanonicalCoupling r k := by
  have hc (u v : Fin (r + 2))
      (hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ)) :
      (finiteWeilCanonicalCoupling r k).plan u v = 0 :=
    finiteWeilCanonicalCoupling_zero_of_nonadjacent r k u v (by omega) (by omega)
  apply finiteWeilCoupling_ext
  intro u v
  by_cases he : u = v
  · subst v
    rw [finiteWeilCanonicalTransport_diagonal r k gamma,
      finiteWeilCanonicalTransport_diagonal r k (finiteWeilCanonicalCoupling r k)]
  · by_cases ha : (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)
    · obtain ⟨i, hi⟩ := finiteWeilCanonicalEdge_covers_adjacent r u v ha
      rcases hi with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rw [← hu, ← hv]
        apply NNReal.coe_injective
        rw [finiteWeilCanonicalTransport_edge_mass r k gamma hband,
          finiteWeilCanonicalTransport_edge_mass r k (finiteWeilCanonicalCoupling r k) hc]
      · rw [← hu, ← hv]
        rw [finiteWeilCanonicalTransport_reverse_edge_zero r k gamma,
          finiteWeilCanonicalTransport_reverse_edge_zero r k (finiteWeilCanonicalCoupling r k)]
    · have hval : (u : ℕ) ≠ (v : ℕ) := fun h => he (Fin.ext h)
      have hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) := by omega
      rw [hband u v hfar, hc u v hfar]

theorem finiteWeilCanonicalTransport_index_minimum_iff (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) :
    finiteWeilCouplingCost gamma finiteWeilIndexCost = 1 ↔ gamma = finiteWeilCanonicalCoupling r k := by
  constructor
  · intro h
    exact finiteWeilCanonicalTransport_eq_of_banded r k gamma
      (finiteWeilCanonicalTransport_index_banded r k gamma h)
  · intro h
    rw [h, finiteWeilCanonicalCoupling_index_cost]

theorem finiteWeilCanonicalTransport_index_unique_minimizer (r k : ℕ) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
        (finiteWeilCanonicalNegativeNNProfile r k),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
          (finiteWeilCanonicalNegativeNNProfile r k),
        finiteWeilCouplingCost gamma finiteWeilIndexCost ≤ finiteWeilCouplingCost eta finiteWeilIndexCost := by
  refine ⟨finiteWeilCanonicalCoupling r k, finiteWeilCanonicalCoupling_index_optimal r k, ?_⟩
  intro gamma hg
  have hle := hg (finiteWeilCanonicalCoupling r k)
  rw [finiteWeilCanonicalCoupling_index_cost] at hle
  have he : finiteWeilCouplingCost gamma finiteWeilIndexCost = 1 :=
    le_antisymm hle (finiteWeilCanonicalCoupling_index_lower_bound r k gamma)
  exact (finiteWeilCanonicalTransport_index_minimum_iff r k gamma).mp he

end RHTower
