import GaloisForLFunctions.RHTower.WeilLogShiftMixtureOrderedTransport
import GaloisForLFunctions.RHTower.WeilLogShiftLogTransport

/-! The entire probability fiber has exact logarithmic transport distance |a-b| K. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilMixtureCoupling_log_cost (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b)
      (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalLogTransportCost r k := by
  rw [finiteWeilMixtureCoupling_node_cost, finiteWeilCanonicalCoupling_log_cost]

theorem finiteWeilMixtureTransport_log_lower_bound (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) :
    |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalLogTransportCost r k ≤
      finiteWeilCouplingCost gamma
        (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) := by
  rw [← finiteWeilMixtureCoupling_log_cost]
  exact finiteWeilMixtureTransport_ordered_optimal r k a b _
    (finiteWeilClusterLogNodes_strictMono r k).monotone gamma

theorem finiteWeilMixtureTransport_log_minimum_iff (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) :
    finiteWeilCouplingCost gamma
      (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalLogTransportCost r k ↔
        gamma = finiteWeilMixtureCoupling r k a b := by
  rw [← finiteWeilMixtureCoupling_log_cost]
  exact finiteWeilMixtureTransport_ordered_minimum_iff r k a b _
    (finiteWeilClusterLogNodes_strictMono r k) gamma

theorem finiteWeilMixtureCoupling_log_cost_bounds (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    |(a : ℝ) - (b : ℝ)| / ((k + r + 3 : ℕ) : ℝ) ≤
        finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b)
          (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) ∧
      finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b)
          (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) ≤
        |(a : ℝ) - (b : ℝ)| / ((k + 2 : ℕ) : ℝ) := by
  simp only [finiteWeilMixtureCoupling_log_cost]
  have hb := finiteWeilCanonicalLogTransportCost_bounds r k
  have hs (z : ℝ) : |(a : ℝ) - (b : ℝ)| * (1 / z) = |(a : ℝ) - (b : ℝ)| / z := by ring
  constructor
  · have h := mul_le_mul_of_nonneg_left hb.1 (abs_nonneg ((a : ℝ) - (b : ℝ)))
    rw [hs] at h
    exact h
  · have h := mul_le_mul_of_nonneg_left hb.2 (abs_nonneg ((a : ℝ) - (b : ℝ)))
    rw [hs] at h
    exact h

theorem finiteWeilMixtureTransport_log_unique_minimizer (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
        (finiteWeilCanonicalMixtureNNProfile r k b),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
          (finiteWeilCanonicalMixtureNNProfile r k b),
        finiteWeilCouplingCost gamma
            (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) ≤
          finiteWeilCouplingCost eta
            (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) :=
  finiteWeilMixtureTransport_ordered_unique_minimizer r k a b _ (finiteWeilClusterLogNodes_strictMono r k)

theorem finiteWeilMixtureCoupling_log_cost_zero_iff (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b)
      (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) = 0 ↔ a = b := by
  rw [finiteWeilMixtureCoupling_log_cost, mul_eq_zero]
  constructor
  · rintro (h | h)
    · apply Subtype.ext
      have hd := abs_eq_zero.mp h
      linarith only [hd]
    · exact False.elim ((ne_of_gt (finiteWeilCanonicalLogTransportCost_pos r k)) h)
  · intro h
    subst b
    exact Or.inl (by simp)

end RHTower
