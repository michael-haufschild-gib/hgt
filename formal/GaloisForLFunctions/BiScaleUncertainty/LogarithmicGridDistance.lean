import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridPolarRecovery

/-!
# Exact nearest-node distance on the infinite logarithmic grid

The floor of `exp T` supplies the two bracketing nodes. Their smaller displacement is
the actual nearest-grid distance, is attained, and vanishes exactly on the grid.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def logarithmicFloorNode (T : ℝ) : ℕ := ⌊Real.exp T⌋₊

def logarithmicGridDistance (T : ℝ) : ℝ :=
  min (T - Real.log (logarithmicFloorNode T : ℝ))
    (Real.log ((logarithmicFloorNode T : ℝ) + 1) - T)

theorem logarithmicFloorNode_ge_two {T : ℝ} (hT : 2 ≤ T) :
    2 ≤ logarithmicFloorNode T := by
  apply (Nat.le_floor_iff' (by norm_num : (2 : ℕ) ≠ 0)).mpr
  norm_num
  linarith [Real.add_one_le_exp T]

theorem logarithmicFloorNode_brackets {T : ℝ} (hT : 2 ≤ T) :
    Real.log (logarithmicFloorNode T : ℝ) ≤ T ∧
      T < Real.log ((logarithmicFloorNode T : ℝ) + 1) := by
  have hN := logarithmicFloorNode_ge_two hT
  have hp : 0 < (logarithmicFloorNode T : ℝ) := by
    exact_mod_cast (show 0 < logarithmicFloorNode T by omega)
  have hlo := Real.log_le_log hp (Nat.floor_le (Real.exp_pos T).le)
  have hhi := Real.log_lt_log (Real.exp_pos T) (Nat.lt_floor_add_one (Real.exp T))
  rw [Real.log_exp] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem logarithmicGridDistance_nonneg {T : ℝ} (hT : 2 ≤ T) :
    0 ≤ logarithmicGridDistance T := by
  obtain ⟨hl, hr⟩ := logarithmicFloorNode_brackets hT
  exact le_min (sub_nonneg.mpr hl) (sub_nonneg.mpr hr.le)

theorem logarithmicGridDistance_le_node {T : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    logarithmicGridDistance T ≤ |Real.log (n : ℝ) - T| := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  by_cases hnN : n ≤ logarithmicFloorNode T
  · have hl := Real.log_le_log hnp (show (n : ℝ) ≤ logarithmicFloorNode T by exact_mod_cast hnN)
    calc
      _ ≤ T - Real.log (logarithmicFloorNode T : ℝ) := min_le_left _ _
      _ ≤ _ := by linarith [neg_le_abs (Real.log (n : ℝ) - T)]
  · have hnN' : logarithmicFloorNode T + 1 ≤ n := by omega
    have hl := Real.log_le_log (show 0 < (logarithmicFloorNode T : ℝ) + 1 by positivity)
      (show (logarithmicFloorNode T : ℝ) + 1 ≤ n by exact_mod_cast hnN')
    calc
      _ ≤ Real.log ((logarithmicFloorNode T : ℝ) + 1) - T := min_le_right _ _
      _ ≤ _ := by linarith [le_abs_self (Real.log (n : ℝ) - T)]

theorem exists_logarithmicGridDistance_node {T : ℝ} (hT : 2 ≤ T) :
    ∃ n : ℕ, 2 ≤ n ∧ |Real.log (n : ℝ) - T| = logarithmicGridDistance T := by
  obtain ⟨hl, hr⟩ := logarithmicFloorNode_brackets hT
  have hN := logarithmicFloorNode_ge_two hT
  by_cases hc : T - Real.log (logarithmicFloorNode T : ℝ) ≤
      Real.log ((logarithmicFloorNode T : ℝ) + 1) - T
  · refine ⟨logarithmicFloorNode T, hN, ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hl), logarithmicGridDistance, min_eq_left hc]
    ring
  · refine ⟨logarithmicFloorNode T + 1, by omega, ?_⟩
    simp only [Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (sub_nonneg.mpr hr.le), logarithmicGridDistance,
      min_eq_right (le_of_not_ge hc)]

theorem logarithmicGridDistance_le_exp_neg {T : ℝ} (hT : 2 ≤ T) :
    logarithmicGridDistance T ≤ Real.exp (-T) := by
  have hb := logarithmicCeilLag_bounds T
  have hn := logarithmicGridDistance_le_node (T := T)
    (logarithmicCeilNode_ge_two (T := T) (by linarith))
  change logarithmicGridDistance T ≤ |logarithmicCeilLag T| at hn
  rw [abs_of_nonneg hb.1] at hn
  exact hn.trans hb.2

theorem logarithmicGridDistance_le_one {T : ℝ} (hT : 2 ≤ T) :
    logarithmicGridDistance T ≤ 1 :=
  (logarithmicGridDistance_le_exp_neg hT).trans (Real.exp_le_one_iff.mpr (by linarith))

theorem logarithmicGridDistance_pos_iff {T : ℝ} (hT : 2 ≤ T) :
    0 < logarithmicGridDistance T ↔ ∀ n : ℕ, 2 ≤ n → T ≠ Real.log (n : ℝ) := by
  constructor
  · intro hd n hn heq
    have h := logarithmicGridDistance_le_node (T := T) hn
    rw [← heq, sub_self, abs_zero] at h
    linarith
  · intro hoff
    by_contra hd
    have heq : logarithmicGridDistance T = 0 :=
      le_antisymm (le_of_not_gt hd) (logarithmicGridDistance_nonneg hT)
    obtain ⟨n, hn, hab⟩ := exists_logarithmicGridDistance_node hT
    rw [heq, abs_eq_zero, sub_eq_zero] at hab
    exact hoff n hn hab.symm

end

end GaloisForLFunctions.BiScaleUncertainty
