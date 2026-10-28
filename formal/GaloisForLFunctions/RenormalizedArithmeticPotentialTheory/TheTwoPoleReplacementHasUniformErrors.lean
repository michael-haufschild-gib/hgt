import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleMomentsHaveQuadraticDilationError
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilTrialEnergiesAreSimpleAndProper
import GaloisForLFunctions.HTGeometry.FiniteTwoPoleKernelBounds

/-!
# Uniform errors in replacing both actual pole moments

At width `c/N`, the quadratic scalar error compensates the squared-horizon
form cost of the two pole outer products. Its action on every bounded pole-gauge
profile is uniformly square bounded. Both bounds concern the actual signed
exponential moments.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis HTGeometry

/-- The difference between the actual normalized two-pole product and its center value. -/
def atomPoleErrorCoefficient (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) *
    atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) /
      (∫ u, atomDilate φ (c / N) u ^ 2) - completeWeilPoleShift φ c / N

theorem atomPoleMomentErrorConstant_nonneg (φ : ℝ → ℝ) :
    0 ≤ atomPoleMomentErrorConstant φ := by
  unfold atomPoleMomentErrorConstant
  exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (integral_nonneg fun u => sq_nonneg _)

/-- The actual scalar coefficient error is quadratic in `c/N`. -/
theorem abs_atomPoleErrorCoefficient_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {N : ℕ} (hN : 1 ≤ N) :
    |atomPoleErrorCoefficient φ c N| ≤ atomPoleMomentErrorConstant φ * (c / N) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr
    (hc1.le.trans (by exact_mod_cast hN))
  have h := abs_dilated_pole_product_sub_le hφ hsupp hM hw0 hw1
  have heq : atomPoleErrorCoefficient φ c N =
      atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) *
        atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) /
          (∫ u, atomDilate φ (c / N) u ^ 2) -
        (c / N) * (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) := by
    simp only [atomPoleErrorCoefficient, completeWeilPoleShift]
    ring
  rw [heq]
  exact h

/-- The two-pole replacement has a horizon-independent quadratic-form cost. -/
theorem abs_atomPoleError_quadratic_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j *
      (atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n))| ≤
      (2 * atomPoleMomentErrorConstant φ * c ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := abs_atomPoleErrorCoefficient_le hφ hsupp hM hc0 hc1 hN
  calc
    _ ≤ 2 * |atomPoleErrorCoefficient φ c N| * (N : ℝ) ^ 2 *
        ∑ n ∈ Icc 1 N, x n ^ 2 := abs_twoPoleKernel_quadratic_le N x _
    _ ≤ 2 * (atomPoleMomentErrorConstant φ * (c / N) ^ 2) * (N : ℝ) ^ 2 *
        ∑ n ∈ Icc 1 N, x n ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun n _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (sq_nonneg _)
    _ = _ := by field_simp [hN0.ne']

/-- The pole replacement has bounded unnormalized square residual on every bounded pole profile. -/
theorem sum_sq_atomPoleError_poleProfile_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {N : ℕ} (hN : 1 ≤ N) {a : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ j ∈ Icc 1 N, |a j| ≤ A) :
    (∑ n ∈ Icc 1 N, (atomPoleErrorCoefficient φ c N * ∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
        (a j / Real.sqrt j)) ^ 2) ≤
      4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2 * c ^ 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := abs_atomPoleErrorCoefficient_le hφ hsupp hM hc0 hc1 hN
  have hs := mul_self_le_mul_self (abs_nonneg _) hd
  rw [← sq, sq_abs, ← sq] at hs
  calc
    _ ≤ 4 * (atomPoleErrorCoefficient φ c N) ^ 2 * A ^ 2 * (N : ℝ) ^ 4 :=
      sum_sq_twoPoleKernel_poleProfile_le hA N ha _
    _ ≤ 4 * (atomPoleMomentErrorConstant φ * (c / N) ^ 2) ^ 2 * A ^ 2 * (N : ℝ) ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by field_simp [hN0.ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
