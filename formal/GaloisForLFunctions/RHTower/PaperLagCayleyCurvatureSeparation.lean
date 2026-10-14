import GaloisForLFunctions.RHTower.PaperLagCayleyOperator
import GaloisForLFunctions.RHTower.WeilLagArchCurvatureAsymptotic

/-! # Actual lag-source separation and quadratic Cayley approximation

The full curvature source lies strictly below its arithmetic model on an
explicit tail. Its signed discrepancy has exact quadratic scale. The same
analysis sharpens the finite-prefix Cayley operator approximation.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerLagCurvature Filter
open scoped Topology

theorem source_tail_lt_arithmetic (n : ℕ) : source (n + 9) < arithmetic (n + 9) := by
  apply sub_neg.mp
  rw [source_sub_arithmetic]
  exact mul_neg_of_pos_of_neg (by positivity) (archCurvatureCorrection_tail_neg n)

theorem source_discrepancy_quadratic_tendsto :
    Tendsto (fun n : ℕ => (n + 3 : ℝ) ^ 2 * (source n - arithmetic n))
      atTop (𝓝 (-(1 / 6))) := by
  convert archCurvatureCorrection_cubic_tendsto using 1
  funext n
  rw [source_sub_arithmetic]
  ring

theorem arithmetic_sub_source_le (n : ℕ) :
    arithmetic n - source n ≤ 1 / (6 * (n + 3 : ℝ) * (n + 2)) := by
  calc
    _ = (n + 3 : ℝ) *
        ((logCurvature n - 1 / (n + 3 : ℝ)) - trivialCurvature n) := by
      rw [← neg_sub (source n), source_sub_arithmetic, archCurvatureCorrection_eq]
      ring
    _ ≤ (n + 3 : ℝ) * (logCurvature n - 1 / (n + 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (trivialCurvature_bounds n).1) (by positivity)
    _ ≤ (n + 3 : ℝ) * (1 / (6 * (n + 3 : ℝ) ^ 2 * (n + 2))) :=
      mul_le_mul_of_nonneg_left (logCurvature_centered_cubic_bounds n).2 (by positivity)
    _ = _ := by
      have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp

theorem phase_tail_ne_arithmetic (n : ℕ) :
    (phase (n + 9) : ℂ) ≠ (arithmeticPhase (n + 9) : ℂ) := by
  intro h
  have he := congrArg paperRealCayleyInverse h
  rw [source_from_phase] at he
  change source (n + 9) = paperRealCayleyInverse (realCayley (arithmetic (n + 9))) at he
  rw [paperRealCayleyInverse_apply] at he
  exact (source_tail_lt_arithmetic n).ne he

theorem phase_discrepancy_tail_le (n : ℕ) :
    ‖(phase (n + 9) : ℂ) - arithmeticPhase (n + 9)‖ ≤
      1 / (3 * (n + 12 : ℝ) * (n + 11)) := by
  calc
    _ ≤ 2 * |source (n + 9) - arithmetic (n + 9)| := phase_discrepancy_le _
    _ = 2 * (arithmetic (n + 9) - source (n + 9)) := by
      rw [abs_of_neg (sub_neg.mpr (source_tail_lt_arithmetic n)), neg_sub]
    _ ≤ 2 * (1 / (6 * ((n + 9 : ℕ) + 3 : ℝ) * ((n + 9 : ℕ) + 2))) :=
      mul_le_mul_of_nonneg_left (arithmetic_sub_source_le _) (by norm_num)
    _ = _ := by
      push_cast
      field_simp
      ring

theorem norm_difference_sub_prefix_quadratic_le (N : ℕ) :
    ‖(sourceOperator - arithmeticOperator) - differencePrefix (N + 9)‖ ≤
      1 / (3 * (N + 12 : ℝ) * (N + 11)) := by
  let tail : ℕ → ℂ := fun n =>
    if n < N + 9 then 0 else (phase n : ℂ) - arithmeticPhase n
  have hb : ∀ n, ‖tail n‖ ≤ 1 / (3 * (N + 12 : ℝ) * (N + 11)) := by
    intro n
    dsimp only [tail]
    split_ifs with hn
    · rw [norm_zero]
      positivity
    · have hn9 : 9 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn9
      have hk : N ≤ k := by omega
      have h := phase_discrepancy_tail_le k
      rw [Nat.add_comm 9 k]
      apply h.trans
      apply one_div_le_one_div_of_le (by positivity)
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
      gcongr
  have heq : (sourceOperator - arithmeticOperator) - differencePrefix (N + 9) =
      diagonalOperator tail hb := by
    ext x n
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, sourceOperator_apply,
      arithmeticOperator_apply, differencePrefix, diagonalOperator_apply, truncMultiplier, tail]
    split_ifs <;> ring
  rw [heq]
  exact norm_diagonalOperator_le _ _

end
end RHTower.PaperLagCayley
