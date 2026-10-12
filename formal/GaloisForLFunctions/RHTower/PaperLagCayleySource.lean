import GaloisForLFunctions.HTGeometry.PaperCayleySourceBounds
import GaloisForLFunctions.RHTower.WeilLagCurvatureGreenRegularization

/-! # The complete integer-lag curvature in Cayley coordinates

The native normalized curvature is encoded invertibly. Its arithmetic model is
used for comparison only; all logarithmic and trivial-zero corrections remain
in the actual source, with a summable phase discrepancy of total mass at most four.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHTower.PaperLagCayley

open GaloisForLFunctions.HTGeometry IntegerLagCurvature

def source (n : ℕ) : ℝ := (n + 3 : ℝ) * scaledCurvature n

def arithmetic (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt (n + 3) - 1

def phase (n : ℕ) : Circle := circleCayley (source n)

def arithmeticPhase (n : ℕ) : Circle := circleCayley (arithmetic n)

theorem source_sub_arithmetic (n : ℕ) :
    source n - arithmetic n = (n + 3 : ℝ) * archCurvatureCorrection n := by
  unfold source arithmetic archCurvatureCorrection
  field_simp

theorem abs_source_sub_arithmetic (n : ℕ) :
    |source n - arithmetic n| = (n + 3 : ℝ) * |archCurvatureCorrection n| := by
  rw [source_sub_arithmetic, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 3)]

theorem summable_source_discrepancy : Summable (fun n => |source n - arithmetic n|) := by
  simpa only [abs_source_sub_arithmetic] using summable_archCurvatureCorrection_firstMoment

theorem source_discrepancy_budget : (∑' n, |source n - arithmetic n|) ≤ 2 := by
  simpa only [abs_source_sub_arithmetic, archCurvatureCorrection] using
    tsum_scaledCurvature_centered_firstMoment_le_two

theorem source_discrepancy_le (n : ℕ) :
    |source n - arithmetic n| ≤ 9 / (n + 2 : ℝ) := by
  have h : source n - arithmetic n =
      (n + 3 : ℝ) * scaledCurvature n - ArithmeticFunction.vonMangoldt (n + 3) + 1 := by
    unfold source arithmetic
    ring
  rw [h]
  exact scaledCurvature_error n

theorem phase_discrepancy_le (n : ℕ) :
    ‖(phase n : ℂ) - arithmeticPhase n‖ ≤ 2 * |source n - arithmetic n| :=
  paperRealCayley_norm_sub_le _ _

theorem summable_phase_discrepancy :
    Summable (fun n => ‖(phase n : ℂ) - arithmeticPhase n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) phase_discrepancy_le
    (summable_source_discrepancy.mul_left 2)

theorem phase_discrepancy_budget :
    (∑' n, ‖(phase n : ℂ) - arithmeticPhase n‖) ≤ 4 := by
  calc
    _ ≤ ∑' n, 2 * |source n - arithmetic n| :=
      summable_phase_discrepancy.tsum_le_tsum phase_discrepancy_le
        (summable_source_discrepancy.mul_left 2)
    _ = 2 * ∑' n, |source n - arithmetic n| := tsum_mul_left
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left source_discrepancy_budget (by norm_num)
    _ = 4 := by ring

theorem phase_discrepancy_pointwise (n : ℕ) :
    ‖(phase n : ℂ) - arithmeticPhase n‖ ≤ 18 / (n + 2 : ℝ) := by
  calc
    _ ≤ 2 * |source n - arithmetic n| := phase_discrepancy_le n
    _ ≤ 2 * (9 / (n + 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (source_discrepancy_le n) (by norm_num)
    _ = _ := by ring

theorem phase_discrepancy_tendsto :
    Tendsto (fun n => ‖(phase n : ℂ) - arithmeticPhase n‖) atTop (𝓝 0) :=
  summable_phase_discrepancy.tendsto_atTop_zero

theorem source_from_phase (n : ℕ) :
    paperRealCayleyInverse (phase n : ℂ) = source n := paperRealCayleyInverse_apply _

theorem curvature_from_phase (n : ℕ) :
    paperRealCayleyInverse (phase n : ℂ) / (n + 3 : ℝ) = scaledCurvature n := by
  rw [source_from_phase, source]
  field_simp

end RHTower.PaperLagCayley
