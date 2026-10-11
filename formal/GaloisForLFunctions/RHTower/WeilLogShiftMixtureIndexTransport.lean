import GaloisForLFunctions.RHTower.WeilLogShiftMixtureIndexSupport

/-! Every pair in the probability fiber has one optimal index coupling, at cost |a-b|. -/

open scoped BigOperators NNReal

noncomputable section
namespace RHTower

theorem finiteWeilOrientedMixtureTransport_index_minimum_iff (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (hba : (b : ℝ) ≤ (a : ℝ))
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) :
    finiteWeilCouplingCost gamma finiteWeilIndexCost = (a : ℝ) - (b : ℝ) ↔
      gamma = finiteWeilOrientedMixtureCoupling r k a b hba := by
  constructor
  · intro hopt
    have hc := finiteWeilOrientedMixtureCoupling_index_cost r k a b hba
    apply finiteWeilCoupling_ext_of_off_diagonal
    intro u v he
    by_cases ha : (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)
    · obtain ⟨i, hi⟩ := finiteWeilCanonicalEdge_covers_adjacent r u v ha
      rcases hi with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rw [← hu, ← hv]
        apply NNReal.coe_injective
        rw [finiteWeilOrientedMixtureTransport_edge_mass r k a b gamma hopt,
          finiteWeilOrientedMixtureTransport_edge_mass r k a b _ hc]
      · rw [← hu, ← hv]
        rw [finiteWeilOrientedMixtureTransport_reverse_edge_zero r k a b gamma hopt,
          finiteWeilOrientedMixtureTransport_reverse_edge_zero r k a b _ hc]
    · have hval : (u : ℕ) ≠ (v : ℕ) := fun h => he (Fin.ext h)
      have hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) := by omega
      rw [finiteWeilOrientedMixtureTransport_index_banded r k a b gamma hopt u v hfar,
        finiteWeilOrientedMixtureTransport_index_banded r k a b _ hc u v hfar]
  · intro he
    rw [he, finiteWeilOrientedMixtureCoupling_index_cost]

def finiteWeilMixtureCoupling (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b) :=
  if h : (b : ℝ) ≤ (a : ℝ) then finiteWeilOrientedMixtureCoupling r k a b h
  else finiteWeilCouplingTranspose
    (finiteWeilOrientedMixtureCoupling r k b a ((le_total (a : ℝ) (b : ℝ)).resolve_right h))

theorem finiteWeilMixtureCoupling_cost_eq (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (c : Fin (r + 2) → Fin (r + 2) → ℝ) (hc : ∀ u, c u u = 0) (hsym : ∀ u v, c u v = c v u) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) c =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) c := by
  by_cases h : (b : ℝ) ≤ (a : ℝ)
  · rw [finiteWeilMixtureCoupling, dif_pos h,
      finiteWeilOrientedMixtureCoupling_cost_eq r k a b h c hc, abs_of_nonneg (sub_nonneg.mpr h)]
  · have hab : (a : ℝ) ≤ (b : ℝ) := (le_total (a : ℝ) (b : ℝ)).resolve_right h
    rw [finiteWeilMixtureCoupling, dif_neg h, finiteWeilCouplingCost_transpose _ c hsym,
      finiteWeilOrientedMixtureCoupling_cost_eq r k b a _ c hc, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring

theorem finiteWeilMixtureCoupling_index_cost (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) finiteWeilIndexCost = |(a : ℝ) - (b : ℝ)| := by
  rw [finiteWeilMixtureCoupling_cost_eq r k a b _ finiteWeilIndexCost_self finiteWeilIndexCost_symm,
    finiteWeilCanonicalCoupling_index_cost, mul_one]

theorem finiteWeilMixtureTransport_index_lower_bound (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) :
    |(a : ℝ) - (b : ℝ)| ≤ finiteWeilCouplingCost gamma finiteWeilIndexCost := by
  rcases le_total (b : ℝ) (a : ℝ) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact finiteWeilOrientedMixtureTransport_index_lower_bound r k a b gamma
  · have ht := finiteWeilOrientedMixtureTransport_index_lower_bound r k b a (finiteWeilCouplingTranspose gamma)
    rw [finiteWeilCouplingCost_transpose _ _ finiteWeilIndexCost_symm] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith only [ht]

theorem finiteWeilMixtureTransport_index_minimum_iff (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) :
    finiteWeilCouplingCost gamma finiteWeilIndexCost = |(a : ℝ) - (b : ℝ)| ↔
      gamma = finiteWeilMixtureCoupling r k a b := by
  constructor
  · intro hopt
    by_cases h : (b : ℝ) ≤ (a : ℝ)
    · rw [finiteWeilMixtureCoupling, dif_pos h]
      apply (finiteWeilOrientedMixtureTransport_index_minimum_iff r k a b h gamma).mp
      simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using hopt
    · have hab : (a : ℝ) ≤ (b : ℝ) := (le_total (a : ℝ) (b : ℝ)).resolve_right h
      rw [finiteWeilMixtureCoupling, dif_neg h]
      have ht : finiteWeilCouplingCost (finiteWeilCouplingTranspose gamma) finiteWeilIndexCost =
          (b : ℝ) - (a : ℝ) := by
        rw [finiteWeilCouplingCost_transpose _ _ finiteWeilIndexCost_symm, hopt,
          abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
      have he := (finiteWeilOrientedMixtureTransport_index_minimum_iff r k b a hab
        (finiteWeilCouplingTranspose gamma)).mp ht
      have he' := congrArg (fun g => finiteWeilCouplingTranspose g) he
      simpa only [finiteWeilCouplingTranspose_involutive] using he'
  · intro he
    rw [he, finiteWeilMixtureCoupling_index_cost]

theorem finiteWeilMixtureTransport_index_unique_minimizer (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
        (finiteWeilCanonicalMixtureNNProfile r k b),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
          (finiteWeilCanonicalMixtureNNProfile r k b),
        finiteWeilCouplingCost gamma finiteWeilIndexCost ≤ finiteWeilCouplingCost eta finiteWeilIndexCost := by
  refine ⟨finiteWeilMixtureCoupling r k a b, ?_, ?_⟩
  · intro eta
    rw [finiteWeilMixtureCoupling_index_cost]
    exact finiteWeilMixtureTransport_index_lower_bound r k a b eta
  · intro gamma hg
    have hle := hg (finiteWeilMixtureCoupling r k a b)
    rw [finiteWeilMixtureCoupling_index_cost] at hle
    exact (finiteWeilMixtureTransport_index_minimum_iff r k a b gamma).mp
      (le_antisymm hle (finiteWeilMixtureTransport_index_lower_bound r k a b gamma))

end RHTower
