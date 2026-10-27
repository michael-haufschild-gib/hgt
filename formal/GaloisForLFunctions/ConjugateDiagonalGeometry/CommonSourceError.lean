import GaloisForLFunctions.ConjugateDiagonalGeometry.CommonSourceRegulator
import GaloisForLFunctions.ConjugateDiagonalGeometry.XiCompactCurrentError

/-!
# Quantitative error along the common arithmetic regulator

The same source-only index works for changing compact tests. Their Laplacian
bound multiplies the prescribed local logarithmic error; the cutoff support
condition is discharged by the fixed source exhaustion.
-/

open Complex MeasureTheory Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower

/-- The common regulator controls any smooth test by its cutoff Laplacian on the source disc. -/
theorem abs_commonSourceReading_sub_current_le (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
    (n : ℕ) {B : ℝ}
    (hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * φ w) z| ≤ B) :
    |commonSourceReading φ n -
      xiCurrentPairing (fun z => sourceCutoff n z * φ z)| ≤
        (2 * Real.pi)⁻¹ * B * sourceLocalAccuracy n := by
  have hB : 0 ≤ B := (abs_nonneg _).trans
    (hb 0 (by rw [Metric.mem_closedBall, dist_self]; positivity))
  have h := abs_xiCurvatureReading_sub_current_le
    (fun z => sourceCutoff n z * φ z) ((sourceCutoff n).contDiff.mul hp)
    (sourceCutoff n).hasCompactSupport.mul_right 0 ((n : ℝ) + 2) B
    (sourceCutoff_laplacian_eq_zero_outside n φ hp) hb (commonSourceIndex n)
  have he : commonSourceReading φ n -
      xiCurrentPairing (fun z => sourceCutoff n z * φ z) =
      Real.pi⁻¹ * ((∫ z, (sourceCutoff n z * φ z) *
        xiCurvatureDensity (sourceRegulator (commonSourceIndex n)) z) -
        (1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ (fun w => sourceCutoff n w * φ w) z) := by
    unfold commonSourceReading xiCompactSourceReading xiCurrentPairing
    ring
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr Real.pi_pos)]
  calc
    Real.pi⁻¹ * |(∫ z, (sourceCutoff n z * φ z) *
        xiCurvatureDensity (sourceRegulator (commonSourceIndex n)) z) -
        (1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ (fun w => sourceCutoff n w * φ w) z| ≤
        Real.pi⁻¹ * ((1 / 2 : ℝ) * B *
          xiLocalLogError 0 ((n : ℝ) + 2) (commonSourceIndex n)) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr Real.pi_pos.le)
    _ ≤ Real.pi⁻¹ * ((1 / 2 : ℝ) * B * sourceLocalAccuracy n) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.pi_pos.le)
      exact mul_le_mul_of_nonneg_left (commonSourceIndex_local_accuracy n).le
        (mul_nonneg (by norm_num) hB)
    _ = _ := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry
