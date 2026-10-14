import GaloisForLFunctions.RHTower.PaperLagCayleySchattenThreshold
import GaloisForLFunctions.HTGeometry.LpDiagonalPartialEnergy

/-! # Critical energy of the actual lag-source discrepancy

The square-root singular-value energy differs from the literal coordinate
energy by a bounded amount. The discrepancy belongs to the weak class at the
sharp endpoint one half.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Filter
open scoped Topology

private theorem difference_eq_diagonalOperator :
    sourceOperator - arithmeticOperator =
      diagonalOperator (fun n => (phase n : ℂ) - arithmeticPhase n)
        norm_phase_discrepancy_le_two := by
  ext x n
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, sourceOperator_apply,
    arithmeticOperator_apply, diagonalOperator_apply]
  ring

theorem sqrt_phase_discrepancy_tail_le (n : ℕ) :
    Real.sqrt ‖(phase (n + 9) : ℂ) - arithmeticPhase (n + 9)‖ ≤ 1 / (n + 12 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, (phase_discrepancy_tail_le n).trans ?_⟩
  rw [div_pow, one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem sqrt_phase_discrepancy_le (n : ℕ) :
    Real.sqrt ‖(phase n : ℂ) - arithmeticPhase n‖ ≤ 22 / (n + 3 : ℝ) := by
  by_cases hn : 9 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h := sqrt_phase_discrepancy_tail_le k
    simpa only [Nat.add_comm 9 k, Nat.cast_add, Nat.cast_ofNat, add_assoc,
      show (9 + 3 : ℝ) = 12 by norm_num] using
      h.trans (by gcongr; norm_num : 1 / (k + 12 : ℝ) ≤ 22 / (k + 12 : ℝ))
  · have hn' : (n : ℝ) ≤ 8 := by exact_mod_cast (by omega : n ≤ 8)
    have h : Real.sqrt ‖(phase n : ℂ) - arithmeticPhase n‖ ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, (norm_phase_discrepancy_le_two n).trans (by norm_num)⟩
    exact h.trans ((le_div_iff₀ (by positivity)).mpr (by linarith))

theorem difference_memWeakSchattenClass_half :
    MemWeakSchattenClass (1 / 2) (sourceOperator - arithmeticOperator) := by
  refine ⟨18, by norm_num, fun n => ?_⟩
  rw [← Real.sqrt_eq_rpow]
  by_cases hn : 9 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 9 k]
    have h := (approxNumber_le (sourceOperator - arithmeticOperator) (k + 9)
      (differencePrefix (k + 9)) (hasRankLE_differencePrefix (k + 9))).trans
      (norm_difference_sub_prefix_quadratic_le k)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, h.trans ?_⟩
    push_cast
    have hb : 1 / (3 * (k + 12 : ℝ) * (k + 11)) ≤ 1 / (k + 10 : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    convert hb.trans (show 1 / (k + 10 : ℝ) ^ 2 ≤ (18 / (k + 10 : ℝ)) ^ 2 by
      rw [div_pow]; gcongr; norm_num) using 1
    ring
  · have hn' : (n : ℝ) ≤ 8 := by exact_mod_cast (by omega : n ≤ 8)
    have ht : ‖sourceOperator - arithmeticOperator‖ ≤ 2 := by
      rw [difference_eq_diagonalOperator]
      exact norm_diagonalOperator_le _ _
    have h : Real.sqrt (approxNumber (sourceOperator - arithmeticOperator) n) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, ((approxNumber_le_norm _ n).trans ht).trans (by norm_num)⟩
    exact h.trans ((le_div_iff₀ (by positivity)).mpr (by linarith))

theorem critical_energy_coordinate_bounds (N : ℕ) :
    0 ≤ schattenPowerPartialSum (1 / 2) (sourceOperator - arithmeticOperator) (N + 9) -
      (∑ n ∈ Finset.range (N + 9), ‖(phase n : ℂ) - arithmeticPhase n‖ ^ (1 / 2 : ℝ)) ∧
    schattenPowerPartialSum (1 / 2) (sourceOperator - arithmeticOperator) (N + 9) -
      (∑ n ∈ Finset.range (N + 9), ‖(phase n : ℂ) - arithmeticPhase n‖ ^ (1 / 2 : ℝ)) ≤ 1 := by
  have hlo := diagonal_coordinate_energy_le (fun n => (phase n : ℂ) - arithmeticPhase n)
    norm_phase_discrepancy_le_two (by norm_num : (0 : ℝ) < 1 / 2) (N + 9)
  have hup := diagonal_partial_energy_le_coordinate_add_tail
    (fun n => (phase n : ℂ) - arithmeticPhase n) norm_phase_discrepancy_le_two
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (N + 9)
  rw [← difference_eq_diagonalOperator] at hlo hup
  change _ ≤ _ + (N + 9 : ℕ) *
    ‖(sourceOperator - arithmeticOperator) - differencePrefix (N + 9)‖ ^ (1 / 2 : ℝ) at hup
  have htail : ‖(sourceOperator - arithmeticOperator) - differencePrefix (N + 9)‖ ^ (1 / 2 : ℝ)
      ≤ 1 / (N + 9 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, (norm_difference_sub_prefix_quadratic_le N).trans ?_⟩
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hbudget := mul_le_mul_of_nonneg_left htail (show (0 : ℝ) ≤ N + 9 by positivity)
  rw [mul_one_div_cancel (by positivity : (N + 9 : ℝ) ≠ 0)] at hbudget
  push_cast at hup
  exact ⟨sub_nonneg.mpr hlo, by linarith⟩

theorem critical_energy_coordinate_log_difference_tendsto_zero :
    Tendsto (fun N : ℕ =>
      (schattenPowerPartialSum (1 / 2) (sourceOperator - arithmeticOperator) N -
        ∑ n ∈ Finset.range N, ‖(phase n : ℂ) - arithmeticPhase n‖ ^ (1 / 2 : ℝ)) /
          Real.log (N + 1)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hb : Tendsto (fun N : ℕ => 1 / Real.log (N + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_ge_atTop 9] with N hN
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Nat.add_comm 9 k]
    exact div_nonneg (critical_energy_coordinate_bounds k).1 (Real.log_nonneg (by norm_cast; omega))
  · filter_upwards [eventually_ge_atTop 9] with N hN
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Nat.add_comm 9 k]
    exact div_le_div_of_nonneg_right (critical_energy_coordinate_bounds k).2
      (Real.log_nonneg (by norm_cast; omega))

end
end RHTower.PaperLagCayley
