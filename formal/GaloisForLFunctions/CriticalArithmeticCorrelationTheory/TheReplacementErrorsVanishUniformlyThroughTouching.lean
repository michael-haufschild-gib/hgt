import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSelfAndPoleErrorsStayUniformAtTouching
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheWeilReplacementErrorsVanishOnRamanujanModes

/-!
# Uniform norm decay of the complete replacement errors

One square-residual budget controls every ratio through touching. Logarithmic
normalization makes that budget vanish uniformly on each fixed Ramanujan mode.
The common self remainder and the charge-linear center residual have the same
uniformity.
-/

noncomputable section

open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory

private theorem normalized_residual_small_of_uniform_sq_bound
    (r : ℝ → (N : ℕ) → EuclideanSpace ℝ (PrimeHorizonIndex N)) {C : ℝ}
    (hb : ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 → ‖r c N‖ ^ 2 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖(Real.sqrt (Real.log N))⁻¹ • r c N‖ ≤ ε := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  filter_upwards [hb, hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with N hN hsmall
  intro c hc0 hc1
  have heq : ‖(Real.sqrt (Real.log N))⁻¹ • r c N‖ ^ 2 = ‖r c N‖ ^ 2 / Real.log N := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (Real.log_natCast_nonneg N)]
    ring
  have hs : ‖(Real.sqrt (Real.log N))⁻¹ • r c N‖ ^ 2 ≤ C / Real.log N := by
    rw [heq]
    exact div_le_div_of_nonneg_right (hN c hc0 hc1) (Real.log_natCast_nonneg N)
  nlinarith only [hs, hsmall, hε, norm_nonneg ((Real.sqrt (Real.log N))⁻¹ • r c N)]

/-- The actual cross error vanishes on each normalized mode with one horizon for all ratios. -/
theorem eventually_fullWeilCrossError_ramanujan_small_uniformly {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ≤ ε := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_crossError_poleResidual_at_touching hφ hsupp hM
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N)
        (ramanujanHorizonVector m N)‖ ^ 2 ≤ (36 * C * A) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro c hc0 hc1
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (atomCrossErrorKernel (atomDilate φ (c / N))) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have h := hb c hc0 hc1 N hN (normalizedRamanujanMode m) A hA
      (fun j _ => abs_normalizedRamanujanMode_le hm j)
    have hcSq : c ^ 2 ≤ 1 := by
      simpa only [← pow_two, one_pow] using mul_le_mul hc1 hc1 hc0.le zero_le_one
    have hle : 36 * C * A * c ^ 2 ≤ 36 * C * A := by
      exact (mul_le_mul_of_nonneg_left hcSq (by positivity)).trans_eq (mul_one _)
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ 36 * C * A * c ^ 2) hle
    exact h.trans (by simpa only [← sq] using hs)
  have h := normalized_residual_small_of_uniform_sq_bound
    (fun c N => Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N)
      (ramanujanHorizonVector m N)) hbound hε
  simpa only [normalizedRamanujanHorizonVector, map_smul] using h

/-- Both actual pole moments have uniformly vanishing normalized-mode error through touching. -/
theorem eventually_fullWeilPoleError_ramanujan_small_uniformly {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ≤ ε := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (ramanujanHorizonVector m N)‖ ^ 2 ≤ 4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro c hc0 hc1
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have h := sum_sq_atomPoleError_poleProfile_le_at_touching hφ hsupp hM hc0 hc1 hN hA
      (fun j _ => abs_normalizedRamanujanMode_le hm j)
    have hcSq : c ^ 2 ≤ 1 := by
      simpa only [← pow_two, one_pow] using mul_le_mul hc1 hc1 hc0.le zero_le_one
    have hc4 : c ^ 4 ≤ 1 := by
      have hs := mul_self_le_mul_self (sq_nonneg c) hcSq
      nlinarith only [hs]
    have hle := mul_le_mul_of_nonneg_left hc4
      (by positivity : 0 ≤ 4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2)
    exact (by simpa only [mul_assoc, ← mul_sum, ramanujanPoleProfile] using h).trans
      (by simpa only [mul_one] using hle)
  have h := normalized_residual_small_of_uniform_sq_bound
    (fun c N => Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (ramanujanHorizonVector m N)) hbound hε
  simpa only [normalizedRamanujanHorizonVector, map_smul] using h

/-- The common self remainder vanishes uniformly on each normalized arithmetic mode. -/
theorem eventually_completeWeilSelfError_ramanujan_small_uniformly {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  have hv : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖) atTop (𝓝 1) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
      (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).sqrt
  have hlim : Tendsto (fun N : ℕ =>
      (Real.exp (1 / 2) / 2 / (N : ℝ)) * ‖normalizedRamanujanHorizonVector m N‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).mul hv
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds hε)] with N hN hsmall
  intro c hc0 hc1
  rw [norm_smul, Real.norm_eq_abs]
  have hs := abs_completeWeilSelfError_le_at_touching hφ hsupp hM hc0 hc1 hN
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hcost : Real.exp (1 / 2) / 2 * (c / N) ≤ Real.exp (1 / 2) / 2 / N := by
    have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc1 hn)
      (show 0 ≤ Real.exp (1 / 2) / 2 by positivity)
    simpa only [mul_one_div] using h
  exact (mul_le_mul_of_nonneg_right (hs.trans hcost) (norm_nonneg _)).trans hsmall.le

/-- The center residual is linear in the bounded width ratio after retaining its ground charge. -/
theorem eventually_fullWeilCenter_ramanujan_small_uniformly {φ : ℝ → ℝ}
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  have hlim := tendsto_fullWeilCenterMatrix_ramanujan_residual_norm hm (completeWeilPoleShift φ 1)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hsmall
  intro c hc0 hc1
  have hcharge : completeWeilPoleShift φ c = c * completeWeilPoleShift φ 1 := by
    unfold completeWeilPoleShift
    ring
  have hmatrix : fullWeilCenterMatrix (completeWeilPoleShift φ c) N =
      c • fullWeilCenterMatrix (completeWeilPoleShift φ 1) N := by
    ext n j
    simp only [fullWeilCenterMatrix, Matrix.smul_apply, smul_eq_mul, hcharge]
    ring
  have hif : (if m = 1 then completeWeilPoleShift φ c else 0) =
      c * (if m = 1 then completeWeilPoleShift φ 1 else 0) := by
    rw [hcharge]
    split_ifs <;> ring
  rw [hmatrix, hif, map_smul, LinearMap.smul_apply, mul_smul, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
  exact ((mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)).trans_eq (one_mul _)).trans hsmall.le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_fullWeilCrossError_ramanujan_small_uniformly
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_fullWeilPoleError_ramanujan_small_uniformly
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeilSelfError_ramanujan_small_uniformly
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_fullWeilCenter_ramanujan_small_uniformly
