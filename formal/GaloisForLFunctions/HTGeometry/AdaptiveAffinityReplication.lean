import GaloisForLFunctions.HTGeometry.MonotoneDiagonalSelection
import Mathlib.Analysis.SpecificLimits.Basic

/-! Stable slow replication at affinity one and universal decay below one. -/

open Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

theorem exists_monotone_ennreal_powers_tendsto_one {f : ℕ → ℝ≥0∞}
    (hf : Tendsto f atTop (𝓝 1)) :
    ∃ m : ℕ → ℕ, Monotone m ∧ (∀ r, m r ≤ r) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun r => f r ^ m r) atTop (𝓝 1) := by
  apply exists_monotone_diagonal_tendsto (fun n r => f r ^ n)
  intro n
  have h := ((ENNReal.continuous_pow n).tendsto 1).comp hf
  rw [one_pow] at h
  exact h.congr fun r => rfl

theorem tendsto_ennreal_powers_zero_of_tendsto_lt_one
    {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞} {m : ℕ → ℕ}
    (hf : Tendsto f atTop (𝓝 c)) (hc : c < 1) (hm : Tendsto m atTop atTop) :
    Tendsto (fun r => f r ^ m r) atTop (𝓝 0) := by
  obtain ⟨b, hcb, hb⟩ := exists_between hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hb).comp hm)
    (Filter.Eventually.of_forall (fun r => (zero_le : 0 ≤ f r ^ m r)))
  filter_upwards [hf.eventually (gt_mem_nhds hcb)] with r hr
  exact pow_le_pow_left' hr.le (m r)

end GaloisForLFunctions.HTGeometry
