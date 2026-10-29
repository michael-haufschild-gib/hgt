import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixKeepsItsBoundaryCorrection
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheReplacementErrorsVanishUniformlyThroughTouching

/-!
# Uniform actual Ramanujan quasimodes through touching

The complete norm residual retains six terms: prime, self, center, cross,
both poles, and the boundary prime correction. Each has a common smallness
horizon throughout `(0,1]`, including arbitrarily small width ratios.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory

private theorem completeWeil_ramanujan_residual_decomposition_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      completeWeilAdjunctionEnergy φ c m • normalizedRamanujanHorizonVector m N =
    -(Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) +
      completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N +
      (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N) -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N) +
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (normalizedRamanujanHorizonVector m N) := by
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
    (completeWeilMatrix_eq_decomposition_at_touching hφ hsupp hM hc0 hc1 hN)
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hone] at h
  rw [h]
  simp only [completeWeilAdjunctionEnergy]
  module

private theorem norm_six_residuals_le {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q r : E) :
    ‖-p + s + c - x + q - r‖ ≤ ‖p‖ + ‖s‖ + ‖c‖ + ‖x‖ + ‖q‖ + ‖r‖ := by
  have h₁ := norm_add_le (-p) s
  have h₂ := norm_add_le (-p + s) c
  have h₃ := norm_sub_le (-p + s + c) x
  have h₄ := norm_add_le (-p + s + c - x) q
  have h₅ := norm_sub_le (-p + s + c - x + q) r
  rw [norm_neg] at h₁
  linarith only [h₁, h₂, h₃, h₄, h₅]

/-- Each positive-conductor mode has a small actual complete norm residual with
one horizon valid simultaneously for every ratio through one. -/
theorem eventually_completeWeil_ramanujan_residual_small_uniformly {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completeWeilAdjunctionEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  have hε6 : 0 < ε / 6 := by positivity
  have hε12 : 0 < ε / 12 := by positivity
  have hp := (tendsto_normalizedRamanujanHorizonVector_residual_norm hm).eventually
    (gt_mem_nhds hε6)
  have hv : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖) atTop (𝓝 1) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
      (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).sqrt
  filter_upwards [hp,
    eventually_completeWeilSelfError_ramanujan_small_uniformly hφ hsupp hM hm hε6,
    eventually_fullWeilCenter_ramanujan_small_uniformly (φ := φ) hm hε6,
    eventually_fullWeilCrossError_ramanujan_small_uniformly hφ hsupp hM hm hε6,
    eventually_fullWeilPoleError_ramanujan_small_uniformly hφ hsupp hM hm hε6,
    eventually_fullWeilNonRatioMatrix_action_small_uniformly hφ hsupp hM hε12,
    hv.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)), eventually_ge_atTop 1]
    with N hpN hsN hcN hxN hqN hrN hvN hN
  intro c hc0 hc1
  have hs := hsN c hc0 hc1
  have hcenter := hcN c hc0 hc1
  have hx := hxN c hc0 hc1
  have hq := hqN c hc0 hc1
  have hr := hrN c hc0 hc1 (normalizedRamanujanHorizonVector m N)
  have hrcost := mul_le_mul_of_nonneg_left hvN.le hε12.le
  rw [completeWeil_ramanujan_residual_decomposition_at_touching hφ hsupp hM hc0 hc1 hN]
  have hsum := norm_six_residuals_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (normalizedRamanujanHorizonVector m N))
  linarith only [hsum, hpN, hs, hcenter, hx, hq, hr, hrcost]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeil_ramanujan_residual_small_uniformly
