import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheWeilReplacementErrorsVanishOnRamanujanModes

/-!
# Ramanujan quasimodes of the actual complete Weil matrix

The exact matrix decomposition combines the prime residual with the common
Robin self-error, the joint center cancellation, and both literal integral
replacement errors. Every term vanishes in norm on the logarithmically
normalized Ramanujan vector throughout `0<c<1`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics

private theorem completeWeilMatrix_ramanujan_residual_decomposition
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hsep : c / N < atomSpacing N) (m : ℕ) :
    Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      completeWeilAdjunctionEnergy φ c m • normalizedRamanujanHorizonVector m N =
    -(Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) +
      completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N +
      (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N) -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N) +
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N) := by
  have hone : Matrix.toEuclideanLin
      (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (normalizedRamanujanHorizonVector m N) = normalizedRamanujanHorizonVector m N := by
    ext i
    change (Matrix.mulVec (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (fun j => normalizedRamanujanHorizonVector m N j)) i = normalizedRamanujanHorizonVector m N i
    rw [Matrix.one_mulVec]
  have h := congrArg
    (fun A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ =>
      Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N))
    (completeWeilMatrix_eq_decomposition hφ hsupp hM hc hN hsep)
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hone] at h
  rw [h]
  simp only [completeWeilAdjunctionEnergy]
  module

private theorem norm_five_residuals_le {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q : E) :
    ‖-p + s + c - x + q‖ ≤ ‖p‖ + ‖s‖ + ‖c‖ + ‖x‖ + ‖q‖ := by
  have h₁ := norm_add_le (-p) s
  have h₂ := norm_add_le (-p + s) c
  have h₃ := norm_sub_le (-p + s + c) x
  have h₄ := norm_add_le (-p + s + c - x) q
  rw [norm_neg] at h₁
  linarith only [h₁, h₂, h₃, h₄]

/-- Every positive-conductor Ramanujan vector is a norm quasimode of the literal complete Weil matrix. -/
theorem tendsto_completeWeilMatrix_ramanujan_residual_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completeWeilAdjunctionEnergy φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  have hp := tendsto_normalizedRamanujanHorizonVector_residual_norm hm
  have hv : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖) atTop (𝓝 1) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
      (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).sqrt
  have hs := ((tendsto_completeWeilSelfError hφ hsupp hM hc0 hc1).abs).mul hv
  have hc := tendsto_fullWeilCenterMatrix_ramanujan_residual_norm hm (completeWeilPoleShift φ c)
  have hx := tendsto_fullWeilCrossErrorMatrix_ramanujan_norm hφ hsupp hM hc0 hc1 hm
  have hq := tendsto_fullWeilPoleErrorMatrix_ramanujan_norm hφ hsupp hM hc0 hc1 hm
  have hlim := (((hp.add hs).add hc).add hx).add hq
  simp only [abs_zero, zero_mul, zero_add] at hlim
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) _ hlim
  filter_upwards [eventually_div_horizon_lt_atomSpacing hc0 hc1, eventually_ge_atTop 1]
    with N hsep hN
  rw [completeWeilMatrix_ramanujan_residual_decomposition hφ hsupp hM hc0 hN hsep.2.2]
  simpa only [norm_smul, Real.norm_eq_abs] using norm_five_residuals_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
