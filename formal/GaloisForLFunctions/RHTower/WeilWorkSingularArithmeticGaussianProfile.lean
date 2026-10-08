import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianBound
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The actual source Gaussian profile in Mellin normalization

The signed upper estimate and the absolute large-parameter estimate come
from full Weil positivity. They concern the literal convolution coefficients.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

def sourceGaussianProfile (lam : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, sourceSquareCoeff lam n * (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ)

private theorem gaussW_mellin_scale {t : ℝ} (ht : 0 < t) (n : ℕ) :
    gaussW (Real.sqrt (4 * Real.pi / t)) n = Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) := by
  rw [gaussW, Real.sq_sqrt (by positivity)]
  congr 1
  field_simp

theorem hasSum_sourceGaussianProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => sourceSquareCoeff lam n *
      (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ)) (sourceGaussianProfile lam t) := by
  obtain ⟨C, _, hC⟩ := exists_norm_source_gaussW_le hW
  have h := (hC (Real.sqrt (4 * Real.pi / t)) (Real.sqrt_pos.mpr (by positivity))).1
  simp_rw [gaussW_mellin_scale ht] at h
  exact h.hasSum

theorem exists_norm_sourceGaussianProfile_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖sourceGaussianProfile lam t‖ ≤ C / t := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_source_gaussW_le hW
  refine ⟨C * (4 * Real.pi), by positivity, fun t ht => ?_⟩
  have h := (hC (Real.sqrt (4 * Real.pi / t)) (Real.sqrt_pos.mpr (by positivity))).2
  simp_rw [gaussW_mellin_scale ht, Real.sq_sqrt (by positivity : 0 ≤ 4 * Real.pi / t)] at h
  simpa only [sourceGaussianProfile, mul_div_assoc] using h

theorem exists_re_sourceGaussianProfile_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (sourceGaussianProfile lam t).re ≤ C * t ^ (-5 / 12 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_re_source_gaussW_le hW
  refine ⟨C * (4 * Real.pi) ^ (5 / 12 : ℝ), by positivity, fun t ht ht1 => ?_⟩
  have hscale : 1 ≤ Real.sqrt (4 * Real.pi / t) := by
    apply Real.one_le_sqrt.mpr
    apply (le_div_iff₀ ht).mpr
    nlinarith [Real.pi_gt_three]
  have h := hC (Real.sqrt (4 * Real.pi / t)) hscale
  simp_rw [gaussW_mellin_scale ht] at h
  have he : Real.sqrt (4 * Real.pi / t) ^ (5 / 6 : ℝ) =
      (4 * Real.pi) ^ (5 / 12 : ℝ) * t ^ (-5 / 12 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num only [show (1 / 2 : ℝ) * (5 / 6) = 5 / 12 by norm_num]
    rw [Real.div_rpow (by positivity) ht.le, div_eq_mul_inv, Real.rpow_neg ht.le]
  rw [he] at h
  simpa only [sourceGaussianProfile, mul_assoc] using h

end RHTower.WeilSingularArithmetic
