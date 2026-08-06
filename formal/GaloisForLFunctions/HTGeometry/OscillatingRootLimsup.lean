import GaloisForLFunctions.HTGeometry.RootGrowthEngine

/-!
# An oscillating bounded factor has root limsup one

A factor that is bounded above by a constant and, infinitely often, bounded
below by a positive constant contributes nothing to the root growth: its `k`-th
roots have `limsup` exactly one.  It may vanish along a whole residue class —
only the frequent lower bound is used.

This is the last ingredient of the independent cusp-constant computation, where
the factor is `cos(π(1-s+k)/2)`.  That factor runs over the four values
`±cos θ`, `±sin θ` as `k` runs over the residues modulo four, so it is bounded,
and at least one of `cos θ`, `sin θ` is non-zero, which gives the frequent lower
bound.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

section RealLimsup

variable {u : ℕ → ℝ}

theorem rpow_inv_le_const_rpow_inv {C : ℝ} (hnn : ∀ k, 0 ≤ u k)
    (hub : ∀ k, u k ≤ C) (k : ℕ) :
    (u k) ^ (1 / (k : ℝ)) ≤ C ^ (1 / (k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact Real.rpow_le_rpow (hnn k) (hub k) (by positivity)

theorem isBoundedUnder_rpow_inv {C : ℝ} (hC : 0 < C) (hnn : ∀ k, 0 ≤ u k)
    (hub : ∀ k, u k ≤ C) :
    IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ => (u k) ^ (1 / (k : ℝ))) := by
  have hconv := tendsto_const_rpow_inv_nat hC
  obtain ⟨M, hM⟩ := (hconv.eventually_lt_const (by norm_num : (1 : ℝ) < 2)).exists_forall_of_atTop
  refine ⟨max 2 (Finset.sup' (Finset.range (M + 1)) (by simp)
      fun k => (u k) ^ (1 / (k : ℝ))), ?_⟩
  rw [Filter.eventually_map]
  filter_upwards with k
  rcases Nat.lt_or_ge k M with hk | hk
  · refine le_max_of_le_right ?_
    exact Finset.le_sup' (fun k => (u k) ^ (1 / (k : ℝ)))
      (Finset.mem_range.mpr (by omega))
  · exact le_max_of_le_left (le_of_lt (lt_of_le_of_lt
      (rpow_inv_le_const_rpow_inv hnn hub k) (hM k hk)))

/-- **The root limsup of a bounded, frequently non-degenerate factor is one.** -/
theorem limsup_rpow_inv_eq_one {C c₀ : ℝ} (hC : 0 < C) (hc₀ : 0 < c₀)
    (hnn : ∀ k, 0 ≤ u k) (hub : ∀ k, u k ≤ C)
    (hlb : ∃ᶠ k in atTop, c₀ ≤ u k) :
    limsup (fun k : ℕ => (u k) ^ (1 / (k : ℝ))) atTop = 1 := by
  have hbdd := isBoundedUnder_rpow_inv hC hnn hub
  have hlow : IsBoundedUnder (· ≥ ·) atTop
      (fun k : ℕ => (u k) ^ (1 / (k : ℝ))) := by
    refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with k
    exact Real.rpow_nonneg (hnn k) _
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun k : ℕ => (u k) ^ (1 / (k : ℝ))) := hlow.isCoboundedUnder_le
  refine le_antisymm ?_ ?_
  · have hle : limsup (fun k : ℕ => (u k) ^ (1 / (k : ℝ))) atTop
        ≤ limsup (fun k : ℕ => C ^ (1 / (k : ℝ))) atTop :=
      limsup_le_limsup (Filter.Eventually.of_forall
        (rpow_inv_le_const_rpow_inv hnn hub)) hcob
        (tendsto_const_rpow_inv_nat hC).isBoundedUnder_le
    rwa [(tendsto_const_rpow_inv_nat hC).limsup_eq] at hle
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨a, ha1, ha2⟩ := exists_between hcon
    have hev : ∀ᶠ k : ℕ in atTop, a < c₀ ^ (1 / (k : ℝ)) :=
      (tendsto_const_rpow_inv_nat hc₀).eventually_const_lt ha2
    have hfreq : ∃ᶠ k : ℕ in atTop, a ≤ (u k) ^ (1 / (k : ℝ)) := by
      refine (hlb.and_eventually hev).mono fun k hk => ?_
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa using hk.2.le
      · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        exact le_trans hk.2.le (Real.rpow_le_rpow hc₀.le hk.1 (by positivity))
    exact absurd (le_limsup_of_frequently_le hfreq hbdd) (not_le.mpr ha1)

end RealLimsup

end GaloisForLFunctions.HTGeometry
