import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixHasAnExactErrorDecomposition
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCorrectionSelectsTheConstantRamanujanMode
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAtomCrossReplacementHasUniformErrors
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.HorizonKernelEuclideanIdentities
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# The complete center and replacement errors on normalized Ramanujan modes

Literal finite-row square bounds become Euclidean residual bounds on the
actual horizon. Division by the square root of the logarithmic mass makes each
bounded unnormalized error vanish in norm. The center correction retains only
the conductor-one charge shift.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis

/-- A uniformly square-bounded horizon vector vanishes under logarithmic normalization. -/
theorem tendsto_horizon_normalized_norm_of_sq_bounded
    (r : ∀ N : ℕ, EuclideanSpace ℝ (PrimeHorizonIndex N)) {C : ℝ}
    (hC : ∀ᶠ N : ℕ in atTop, ‖r N‖ ^ 2 ≤ C) :
    Tendsto (fun N : ℕ => ‖(Real.sqrt (Real.log N))⁻¹ • r N‖) atTop (𝓝 0) := by
  have heq (N : ℕ) : ‖(Real.sqrt (Real.log N))⁻¹ • r N‖ ^ 2 = ‖r N‖ ^ 2 / Real.log N := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (Real.log_natCast_nonneg N)]
    ring
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hs : Tendsto (fun N : ℕ => ‖(Real.sqrt (Real.log N))⁻¹ • r N‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => sq_nonneg _)
      (hC.mono fun N hN => ?_) hmaj
    rw [heq]
    exact div_le_div_of_nonneg_right hN (Real.log_natCast_nonneg N)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

/-- The exact center matrix has a uniformly bounded unnormalized Ramanujan residual. -/
theorem exists_fullWeilCenterMatrix_residual_bound {m : ℕ} (hm : 0 < m) (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (ramanujanHorizonVector m N) -
        (if m = 1 then α else 0) • ramanujanHorizonVector m N‖ ^ 2 ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_centerCorrection_ramanujan_residual_bound hm α
  refine ⟨C, hC, fun N => ?_⟩
  change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => (α / N) *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N) -
      (if m = 1 then α else 0) • horizonProfileVector (ramanujanPoleProfile m) N‖ ^ 2 ≤ C
  rw [horizonKernelMatrix_profile_residual_norm_sq]
  simpa only [mul_assoc, ← mul_sum] using hbound N

/-- The center correction on a normalized Ramanujan mode tends to its ground charge shift. -/
theorem tendsto_fullWeilCenterMatrix_ramanujan_residual_norm {m : ℕ}
    (hm : 0 < m) (α : ℝ) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_fullWeilCenterMatrix_residual_bound hm α
  have h := tendsto_horizon_normalized_norm_of_sq_bounded
    (fun N => Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (ramanujanHorizonVector m N) -
      (if m = 1 then α else 0) • ramanujanHorizonVector m N)
    (Eventually.of_forall hbound)
  have heq (N : ℕ) :
      Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N =
      (Real.sqrt (Real.log N))⁻¹ •
        (Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (ramanujanHorizonVector m N) -
          (if m = 1 then α else 0) • ramanujanHorizonVector m N) := by
    simp only [normalizedRamanujanHorizonVector, map_smul]
    rw [smul_comm (if m = 1 then α else 0) (Real.sqrt (Real.log N))⁻¹, smul_sub]
  simpa only [heq] using h

/-- The literal atom-cross replacement vanishes in norm on every normalized Ramanujan mode. -/
theorem tendsto_fullWeilCrossErrorMatrix_ramanujan_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 ≤
        (36 * atomCrossErrorConstant φ c * A * c ^ 2) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (atomCrossErrorKernel (atomDilate φ (c / N))) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    exact sum_sq_atomCrossError_at_spacing_le hφ hsupp hM hc0 hc1 hN hA
      (fun j _ => abs_normalizedRamanujanMode_le hm j)
  have h := tendsto_horizon_normalized_norm_of_sq_bounded
    (fun N => Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (ramanujanHorizonVector m N)) hb
  simpa only [normalizedRamanujanHorizonVector, map_smul] using h

/-- The error in both actual pole moments vanishes in norm on every normalized Ramanujan mode. -/
theorem tendsto_fullWeilPoleErrorMatrix_ramanujan_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 ≤
        4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2 * c ^ 4 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    simpa only [mul_assoc, ← mul_sum, ramanujanPoleProfile] using
      sum_sq_atomPoleError_poleProfile_le hφ hsupp hM hc0 hc1 hN hA
        (fun j _ => abs_normalizedRamanujanMode_le hm j)
  have h := tendsto_horizon_normalized_norm_of_sq_bounded
    (fun N => Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector m N)) hb
  simpa only [normalizedRamanujanHorizonVector, map_smul] using h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
