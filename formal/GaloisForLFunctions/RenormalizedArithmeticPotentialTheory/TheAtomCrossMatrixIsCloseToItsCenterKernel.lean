import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanDensityHasQuadraticIncrementControl
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOfTheMarkovFormAtTheSpacing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLogarithmicCenterKernelIsHarmonic
import GaloisForLFunctions.HTGeometry.IntegerLogarithmicWindowGap

/-!
# The literal atom cross matrix and its center-density approximation

The exact integral error is controlled by the variation of the Levy density
across the atom window. The inverse-square increment bound and the retained
integer gap turn this into a summable discrete error, for signed profiles and
every strictly separated width ratio.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis HTGeometry

/-- The normalized literal cross entry minus its center-density value, with zero diagonal. -/
def atomCrossErrorKernel (g : ℝ → ℝ) (n j : ℕ) : ℝ :=
  if n = j then 0 else
    atomCrossTerm g |Real.log j - Real.log n| / (∫ u, g u ^ 2) -
      ((∫ u, g u) ^ 2 / (∫ u, g u ^ 2)) * archimedeanCenterKernel n j

@[simp] theorem atomCrossErrorKernel_self (g : ℝ → ℝ) (n : ℕ) :
    atomCrossErrorKernel g n n = 0 := by simp only [atomCrossErrorKernel, if_true]

theorem atomCrossErrorKernel_comm (g : ℝ → ℝ) (n j : ℕ) :
    atomCrossErrorKernel g n j = atomCrossErrorKernel g j n := by
  simp only [atomCrossErrorKernel, eq_comm, abs_sub_comm, archimedeanCenterKernel_comm]

/-- Each normalized cross replacement error has a reciprocal integer-square majorant. -/
theorem abs_atomCrossErrorKernel_le {g : ℝ → ℝ} {w c : ℝ} {n j N : ℕ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hG : 0 < ∫ u, g u ^ 2)
    (hw0 : 0 ≤ w) (hc : 0 ≤ c) (hc1 : c < 1) (hw : w ≤ c / N)
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    |atomCrossErrorKernel g n j| ≤
      (38 * w * (∫ u, |g u|) ^ 2 / (∫ u, g u ^ 2) / (1 - c) ^ 2) *
        (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
  by_cases hnj : n = j
  · subst j
    simp only [atomCrossErrorKernel_self, abs_zero, sub_self, abs_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), div_zero]
    exact le_rfl
  have hnz : n ≠ 0 := by have h := mem_Icc.mp hn; omega
  have hjz : j ≠ 0 := by have h := mem_Icc.mp hj; omega
  have hws : w < |Real.log j - Real.log n| := by
    have h := integer_log_gap_sub_window_pos hn hj hnj hc hc1 hw
    rw [abs_sub_comm] at h
    linarith only [h]
  have herr := abs_crossTerm_sub_le hg hgc hsupp hw0 hws
  have hvar := archLevyDensity_window_sub_le hw0 hws
  have hinv := inv_sq_integer_log_gap_sub_window_le hn hj hnj hc hc1 hw
  rw [abs_sub_comm (Real.log n) (Real.log j)] at hinv
  rw [atomCrossErrorKernel, if_neg hnj, archimedeanCenterKernel,
    if_neg (by simp only [hnj, hnz, hjz, or_self, not_false_eq_true])]
  have heq : atomCrossTerm g |Real.log j - Real.log n| / (∫ u, g u ^ 2) -
      ((∫ u, g u) ^ 2 / (∫ u, g u ^ 2)) * archLevyDensity |Real.log j - Real.log n| =
      (atomCrossTerm g |Real.log j - Real.log n| -
        archLevyDensity |Real.log j - Real.log n| * (∫ u, g u) ^ 2) / (∫ u, g u ^ 2) := by ring
  rw [heq, abs_div, abs_of_pos hG]
  calc
    _ ≤ ((38 * w / (|Real.log j - Real.log n| - w) ^ 2) * (∫ u, |g u|) ^ 2) /
        (∫ u, g u ^ 2) :=
      div_le_div_of_nonneg_right
        (herr.trans (mul_le_mul_of_nonneg_right hvar (sq_nonneg _))) hG.le
    _ = (38 * w * (∫ u, |g u|) ^ 2 / (∫ u, g u ^ 2)) *
        (1 / (|Real.log j - Real.log n| - w) ^ 2) := by ring
    _ ≤ (38 * w * (∫ u, |g u|) ^ 2 / (∫ u, g u ^ 2)) *
        ((max (n : ℝ) j) ^ 2 / ((1 - c) ^ 2 * |(n : ℝ) - j| ^ 2)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The absolute mass of a dilated profile scales exactly with its width. -/
theorem integral_abs_atomDilate {φ : ℝ → ℝ} {w : ℝ} (hw : 0 < w) :
    (∫ u, |atomDilate φ w u|) = w * ∫ u, |φ u| := by
  have h := MeasureTheory.Measure.integral_comp_div (fun x => |φ x|) w
  simpa only [atomDilate, smul_eq_mul, abs_of_pos hw] using h

/-- At width `w<=c/N`, the normalized cross error is quadratic in `w`. -/
theorem abs_atomCrossErrorKernel_atomDilate_le {φ : ℝ → ℝ} {w c : ℝ} {n j N : ℕ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) (hw0 : 0 < w) (hc : 0 ≤ c) (hc1 : c < 1)
    (hw : w ≤ c / N) (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    |atomCrossErrorKernel (atomDilate φ w) n j| ≤
      (38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c) ^ 2)) * w ^ 2 *
        (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
  obtain ⟨hg, hsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hG : 0 < ∫ u, atomDilate φ w u ^ 2 := by
    rw [integral_atomDilate_sq hw0]
    exact mul_pos hw0 hφ0
  have h := abs_atomCrossErrorKernel_le hg.continuous hgc hsupp hG hw0.le hc hc1 hw hn hj
  rw [integral_abs_atomDilate hw0, integral_atomDilate_sq hw0] at h
  convert h using 1
  field_simp [hw0.ne', hφ0.ne', (sub_pos.mpr hc1).ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
