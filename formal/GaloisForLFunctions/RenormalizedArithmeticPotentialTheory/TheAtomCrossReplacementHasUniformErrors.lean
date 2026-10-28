import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAtomCrossMatrixIsCloseToItsCenterKernel
import GaloisForLFunctions.HTGeometry.FiniteKernelErrorFromDistanceRows

/-!
# Uniform errors in replacing the literal atom cross matrix

At a fixed separated ratio, the actual cross-integral replacement has bounded
quadratic-form cost on every vector and bounded square residual on every fixed
bounded pole profile. These estimates use the actual signed atom integrals.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis HTGeometry

/-- The profile-dependent coefficient of the discrete cross-integral error. -/
def atomCrossErrorConstant (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c) ^ 2)

theorem atomCrossErrorConstant_nonneg (φ : ℝ → ℝ) (c : ℝ) :
    0 ≤ atomCrossErrorConstant φ c := by
  unfold atomCrossErrorConstant
  have hM : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
  positivity

/-- The actual cross replacement is uniformly bounded as a quadratic form at fixed spacing. -/
theorem abs_atomCrossError_quadratic_at_spacing_le {φ : ℝ → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) (hc0 : 0 < c) (hc1 : c < 1)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      x n * x j * atomCrossErrorKernel (atomDilate φ (c / N)) n j| ≤
        (4 * atomCrossErrorConstant φ c * c ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hN0
  have hentry := fun (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ Icc 1 N) =>
    abs_atomCrossErrorKernel_atomDilate_le
    hφ hφsupp hφ0 hw hc0.le hc1 le_rfl hn hj
  have h := abs_kernel_quadratic_le_of_integer_distance
    (mul_nonneg (atomCrossErrorConstant_nonneg φ c) (sq_nonneg (c / (N : ℝ))))
    hentry (fun n _ j _ => atomCrossErrorKernel_comm _ n j) x
  change _ ≤ (4 * (atomCrossErrorConstant φ c * (c / (N : ℝ)) ^ 2) * (N : ℝ) ^ 2) *
    (∑ n ∈ Icc 1 N, x n ^ 2) at h
  convert h using 1
  field_simp [hN0.ne']

/-- The unnormalized actual cross replacement has uniformly bounded residual on a pole profile. -/
theorem sum_sq_atomCrossError_at_spacing_le {φ : ℝ → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) (hc0 : 0 < c) (hc1 : c < 1)
    {N : ℕ} (hN : 1 ≤ N) {a : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ j ∈ Icc 1 N, |a j| ≤ A) :
    (∑ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, atomCrossErrorKernel (atomDilate φ (c / N)) n j *
        (a j / Real.sqrt j)) ^ 2) ≤
      (36 * atomCrossErrorConstant φ c * A * c ^ 2) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hN0
  have hentry := fun (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ Icc 1 N) =>
    abs_atomCrossErrorKernel_atomDilate_le
    hφ hφsupp hφ0 hw hc0.le hc1 le_rfl hn hj
  have h := sum_sq_kernel_poleProfile_le
    (mul_nonneg (atomCrossErrorConstant_nonneg φ c) (sq_nonneg (c / (N : ℝ))))
    hentry hA ha
  change _ ≤ (36 * (atomCrossErrorConstant φ c * (c / (N : ℝ)) ^ 2) * A) ^ 2 * (N : ℝ) ^ 4 at h
  convert h using 1
  field_simp [hN0.ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
