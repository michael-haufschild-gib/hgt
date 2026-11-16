import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Exact thresholds for a local divisor gain

The local gain in Zimov's Lemma 3 (arXiv:2611.13606) is strictly decreasing
in the logarithmic prime coordinate. Its difference from the logarithmic
normalization has exactly one positive zero. This gives a threshold for
every valuation, independently of colossally abundant numbers or zero sums.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.BiScaleUncertainty.Robin

/-- Denominator of the gain from increasing a prime valuation by one. -/
def stepDenominator (v : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (v + 1), Real.exp (((k : ℝ) + 1) * x)

/-- Local divisor gain in logarithmic prime coordinates. -/
def stepGain (v : ℕ) (x : ℝ) : ℝ := 1 + 1 / stepDenominator v x

theorem stepDenominator_pos (v : ℕ) (x : ℝ) : 0 < stepDenominator v x := by
  exact sum_pos (fun _ _ => Real.exp_pos _) (nonempty_range_iff.mpr (Nat.succ_ne_zero v))

theorem strictMono_stepDenominator (v : ℕ) : StrictMono (stepDenominator v) := by
  intro x y hxy
  apply sum_lt_sum_of_nonempty (nonempty_range_iff.mpr (Nat.succ_ne_zero v))
  intro k _
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hxy (by positivity))

theorem strictAnti_stepGain (v : ℕ) : StrictAnti (stepGain v) := by
  intro x y hxy
  have h := one_div_lt_one_div_of_lt (stepDenominator_pos v x)
    (strictMono_stepDenominator v hxy)
  dsimp [stepGain]
  linarith only [h]

theorem continuous_stepGain (v : ℕ) : Continuous (stepGain v) := by
  apply continuous_const.add
  exact continuous_const.div (by unfold stepDenominator; fun_prop)
    (fun x => (stepDenominator_pos v x).ne')

theorem one_lt_stepGain (v : ℕ) (x : ℝ) : 1 < stepGain v x := by
  exact lt_add_of_pos_right _ (one_div_pos.mpr (stepDenominator_pos v x))

/-- More prior copies of the prime strictly reduce its next divisor gain. -/
theorem stepGain_succ_lt (v : ℕ) (x : ℝ) : stepGain (v + 1) x < stepGain v x := by
  have hd : stepDenominator v x < stepDenominator (v + 1) x := by
    unfold stepDenominator
    rw [sum_range_succ (n := v + 1)]
    exact lt_add_of_pos_right _ (Real.exp_pos _)
  have h := one_div_lt_one_div_of_lt (stepDenominator_pos v x) hd
  dsimp [stepGain]
  linarith only [h]

theorem stepGain_zero_coordinate (v : ℕ) :
    stepGain v 0 = 1 + 1 / ((v : ℝ) + 1) := by
  simp [stepGain, stepDenominator]

/-- Difference between the local divisor gain and the global normalization. -/
def stepBalance (v : ℕ) (L x : ℝ) : ℝ :=
  stepGain v x - Real.log (L + x) / Real.log L

theorem strictAntiOn_stepBalance (v : ℕ) {L : ℝ} (hL : 1 < L) :
    StrictAntiOn (stepBalance v L) (Set.Ioi (-L)) := by
  intro x hx y _ hxy
  apply sub_lt_sub (strictAnti_stepGain v hxy)
  exact (div_lt_div_iff_of_pos_right (Real.log_pos hL)).mpr
    (Real.log_lt_log (by change -L < x at hx; linarith only [hx])
      (by linarith only [hxy]))

/-- A positive zero exists and is unique on the entire logarithm domain. -/
theorem existsUnique_stepThreshold (v : ℕ) {L : ℝ} (hL : 1 < L) :
    ∃! x : ℝ, x ∈ Set.Ioi (-L) ∧ stepBalance v L x = 0 := by
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hleft : 0 < stepBalance v L 0 := by
    simpa only [stepBalance, add_zero, div_self hlog.ne', sub_pos] using one_lt_stepGain v 0
  have hright : stepBalance v L (L ^ 2) < 0 := by
    have hgain : stepGain v (L ^ 2) < 2 := by
      have hterm : 1 < Real.exp (L ^ 2) := Real.one_lt_exp_iff.mpr (sq_pos_of_pos hL0)
      have hsum : Real.exp (L ^ 2) ≤ stepDenominator v (L ^ 2) := by
        have h := single_le_sum (f := fun k : ℕ => Real.exp (((k : ℝ) + 1) * L ^ 2))
          (fun k _ => (Real.exp_pos _).le) (mem_range.mpr (Nat.succ_pos v))
        norm_num only [Nat.cast_zero, zero_add, one_mul] at h
        exact h
      have hinv := one_div_lt_one_div_of_lt zero_lt_one (hterm.trans_le hsum)
      dsimp [stepGain]
      linarith only [hinv]
    have hnorm : 2 < Real.log (L + L ^ 2) / Real.log L := by
      rw [lt_div_iff₀ hlog]
      have h := Real.log_lt_log (sq_pos_of_pos hL0)
        (show L ^ 2 < L + L ^ 2 by linarith only [hL0])
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    exact sub_neg.mpr (hgain.trans hnorm)
  have hc : ContinuousOn (stepBalance v L) (Set.Icc 0 (L ^ 2)) := by
    apply (continuous_stepGain v).continuousOn.sub
    apply ContinuousOn.div_const
    apply Real.continuousOn_log.comp (continuous_const.add continuous_id).continuousOn
    intro x hx
    exact ne_of_gt (add_pos_of_pos_of_nonneg hL0 hx.1)
  obtain ⟨x, hx, hz⟩ := intermediate_value_Icc' (sq_nonneg L) hc
    ⟨hright.le, hleft.le⟩
  have hxd : x ∈ Set.Ioi (-L) := by
    change -L < x
    linarith only [hx.1, hL0]
  refine ⟨x, ⟨hxd, hz⟩, ?_⟩
  intro y hy
  exact (strictAntiOn_stepBalance v hL).injOn hy.1 hxd (hy.2.trans hz.symm)

/-- The unique crossing, extended by zero outside the normalization domain. -/
def stepThreshold (v : ℕ) (L : ℝ) : ℝ :=
  if hL : 1 < L then (existsUnique_stepThreshold v hL).exists.choose else 0

theorem stepThreshold_spec (v : ℕ) {L : ℝ} (hL : 1 < L) :
    stepThreshold v L ∈ Set.Ioi (-L) ∧ stepBalance v L (stepThreshold v L) = 0 := by
  unfold stepThreshold
  rw [dif_pos hL]
  exact (existsUnique_stepThreshold v hL).exists.choose_spec

theorem stepThreshold_pos (v : ℕ) {L : ℝ} (hL : 1 < L) :
    0 < stepThreshold v L := by
  have hs := stepThreshold_spec v hL
  have hzero : (0 : ℝ) ∈ Set.Ioi (-L) := by change -L < 0; linarith only [hL]
  have hleft : 0 < stepBalance v L 0 := by
    simpa only [stepBalance, add_zero, div_self (Real.log_pos hL).ne', sub_pos]
      using one_lt_stepGain v 0
  by_contra h
  have hle := (strictAntiOn_stepBalance v hL).antitoneOn hs.1 hzero (le_of_not_gt h)
  rw [hs.2] at hle
  exact (not_le_of_gt hleft) hle

/-- A gain exceeds the normalization exactly below the crossing. -/
theorem stepBalance_pos_iff (v : ℕ) {L x : ℝ} (hL : 1 < L) (hx : -L < x) :
    0 < stepBalance v L x ↔ x < stepThreshold v L := by
  have hs := stepThreshold_spec v hL
  constructor
  · intro h
    by_contra hnot
    have hle := (strictAntiOn_stepBalance v hL).antitoneOn hs.1 hx (le_of_not_gt hnot)
    rw [hs.2] at hle
    exact (not_le_of_gt h) hle
  · intro h
    have hlt := strictAntiOn_stepBalance v hL hx hs.1 h
    rwa [hs.2] at hlt

theorem stepBalance_neg_iff (v : ℕ) {L x : ℝ} (hL : 1 < L) (hx : -L < x) :
    stepBalance v L x < 0 ↔ stepThreshold v L < x := by
  have hs := stepThreshold_spec v hL
  constructor
  · intro h
    by_contra hnot
    have hle := (strictAntiOn_stepBalance v hL).antitoneOn hx hs.1 (le_of_not_gt hnot)
    rw [hs.2] at hle
    exact (not_le_of_gt h) hle
  · intro h
    have hlt := strictAntiOn_stepBalance v hL hs.1 hx h
    rwa [hs.2] at hlt

/-- Raising the valuation moves the exact crossing strictly toward zero. -/
theorem stepThreshold_succ_lt (v : ℕ) {L : ℝ} (hL : 1 < L) :
    stepThreshold (v + 1) L < stepThreshold v L := by
  have hs := stepThreshold_spec v hL
  apply (stepBalance_neg_iff (v + 1) hL hs.1).mp
  have hg := stepGain_succ_lt v (stepThreshold v L)
  dsimp [stepBalance] at hs ⊢
  linarith only [hs.2, hg]

end GaloisForLFunctions.BiScaleUncertainty.Robin
