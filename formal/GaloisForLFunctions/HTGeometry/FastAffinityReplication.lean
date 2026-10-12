import GaloisForLFunctions.HTGeometry.FastDiagonalSelection
import Mathlib.Analysis.SpecificLimits.Basic

/-! A fast separating power schedule exists exactly under eventual strict affinity loss. -/

open Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

theorem exists_monotone_ennreal_fast_powers_zero_iff (f : ℕ → ℝ≥0∞) :
    (∃ m : ℕ → ℕ, Monotone m ∧ (∀ r, r ≤ m r) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun r => f r ^ m r) atTop (𝓝 0)) ↔ ∀ᶠ r in atTop, f r < 1 := by
  constructor
  · rintro ⟨m, _, _, _, hpow⟩
    filter_upwards [hpow.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))] with r hr
    by_contra h
    have hp : 1 ≤ f r ^ m r := one_le_pow₀ (le_of_not_gt h)
    exact not_lt_of_ge hp hr
  · intro hf
    apply exists_monotone_fast_diagonal_tendsto (fun r n => f r ^ n)
    exact hf.mono fun r hr => ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr

end GaloisForLFunctions.HTGeometry
