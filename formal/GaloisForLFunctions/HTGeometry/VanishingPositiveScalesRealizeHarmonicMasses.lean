import Mathlib.Analysis.PSeries
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
Every vanishing positive scale realizes each positive harmonic mass along a
divergent horizon schedule. Choosing the first horizon reaching the target
bounds the overshoot by one scaled harmonic cell.
-/

open Finset Filter
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.HTGeometry
set_option autoImplicit false

/-- The harmonic sum with its first unit term removed. -/
def shiftedHarmonicSum (T : ℕ) : ℝ := ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1)

/-- Each shifted harmonic cell is at most one. -/
theorem shiftedHarmonicSum_le (T : ℕ) : shiftedHarmonicSum T ≤ T := by
  calc
    _ ≤ ∑ _n ∈ Icc 1 T, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg _))
    _ = _ := by simp

private theorem shiftedHarmonicSum_step_le (T : ℕ) :
    shiftedHarmonicSum (T + 1) ≤ shiftedHarmonicSum T + 1 := by
  rw [shiftedHarmonicSum, sum_Icc_succ_top (by omega)]
  exact add_le_add le_rfl
    ((div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg _)))

/-- Removing finitely many harmonic terms preserves divergence. -/
theorem tendsto_shiftedHarmonicSum_atTop : Tendsto shiftedHarmonicSum atTop atTop := by
  have hsucc : Tendsto (fun T : ℕ => T + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with T hT
    omega
  have heq (T : ℕ) : (∑ n ∈ range (T + 1), (1 / ((n : ℝ) + 1))) =
      1 + shiftedHarmonicSum T := by
    have hset : range (T + 1) = insert 0 (Icc 1 T) := by
      ext n
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hset, sum_insert (by simp)]
    simp only [Nat.cast_zero, zero_add, div_one, shiftedHarmonicSum]
  apply tendsto_atTop.2
  intro b
  filter_upwards [(Real.tendsto_sum_range_one_div_nat_succ_atTop.comp hsucc).eventually_ge_atTop (b + 1)]
    with T hT
  change b + 1 ≤ ∑ n ∈ range (T + 1), 1 / ((n : ℝ) + 1) at hT
  rw [heq] at hT
  linarith only [hT]

/-- The first harmonic horizon reaching a positive target overshoots by at most one scaled cell. -/
theorem exists_scaled_shiftedHarmonicSum_between {k ℓ : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    ∃ T : ℕ, ℓ ≤ k * shiftedHarmonicSum T ∧ k * shiftedHarmonicSum T ≤ ℓ + k := by
  have hexists : ∃ T : ℕ, ℓ ≤ k * shiftedHarmonicSum T := by
    obtain ⟨T, hT⟩ := (tendsto_shiftedHarmonicSum_atTop.eventually_ge_atTop (ℓ / k)).exists
    refine ⟨T, ?_⟩
    simpa only [mul_comm] using (div_le_iff₀ hk).mp hT
  let T := Nat.find hexists
  have hlo : ℓ ≤ k * shiftedHarmonicSum T := Nat.find_spec hexists
  have hT : 1 ≤ T := by
    by_contra h
    have hz : T = 0 := by omega
    have : ℓ ≤ 0 := by simpa only [hz, shiftedHarmonicSum, Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1),
      sum_empty, mul_zero] using hlo
    exact (not_le_of_gt hℓ) this
  have hprev : k * shiftedHarmonicSum (T - 1) < ℓ :=
    lt_of_not_ge (Nat.find_min hexists (by change T - 1 < T; omega))
  have hstep : shiftedHarmonicSum T ≤ shiftedHarmonicSum (T - 1) + 1 := by
    have h := shiftedHarmonicSum_step_le (T - 1)
    rw [Nat.sub_add_cancel hT] at h
    exact h
  refine ⟨T, hlo, ?_⟩
  have h := mul_le_mul_of_nonneg_left hstep hk.le
  linarith only [h, hprev]

/-- Every vanishing positive scale realizes each positive finite harmonic mass at divergent horizons. -/
theorem exists_tendsto_scaled_shiftedHarmonicSum {k : ℕ → ℝ}
    (hk : ∀ t, 0 < k t) (hk0 : Tendsto k atTop (𝓝 0)) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ H : ℕ → ℕ, Tendsto H atTop atTop ∧
      Tendsto (fun t => k t * shiftedHarmonicSum (H t)) atTop (𝓝 ℓ) := by
  choose H hlo hhi using fun t => exists_scaled_shiftedHarmonicSum_between (hk t) hℓ
  have hlim : Tendsto (fun t => k t * shiftedHarmonicSum (H t) - ℓ) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun t => sub_nonneg.mpr (hlo t))
      (Eventually.of_forall fun t => ?_) hk0
    linarith only [hhi t]
  have hH : Tendsto H atTop atTop := by
    apply tendsto_atTop.2
    intro N
    have hsmall : ∀ᶠ t : ℕ in atTop, k t * (N : ℝ) < ℓ := by
      have h := hk0.mul_const (N : ℝ)
      simp only [zero_mul] at h
      exact h.eventually (gt_mem_nhds hℓ)
    filter_upwards [hsmall] with t ht
    by_contra hn
    have hHN : (H t : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hn))
    have hupper : k t * shiftedHarmonicSum (H t) ≤ k t * (N : ℝ) :=
      mul_le_mul_of_nonneg_left ((shiftedHarmonicSum_le _).trans hHN) (hk t).le
    exact (not_le_of_gt ht) ((hlo t).trans hupper)
  refine ⟨H, hH, ?_⟩
  simpa only [sub_add_cancel, zero_add] using hlim.add_const ℓ

#print axioms shiftedHarmonicSum_le
#print axioms tendsto_shiftedHarmonicSum_atTop
#print axioms exists_scaled_shiftedHarmonicSum_between
#print axioms exists_tendsto_scaled_shiftedHarmonicSum
end GaloisForLFunctions.HTGeometry
