import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheReplacementErrorsVanishAtEveryOverlap

/-!
# Replacement errors vanish uniformly on bounded overlap

The self remainder is uniformly linear in the width; the center residual is exactly linear
in the overlap. The literal two-pole and separated cross sources have squared unnormalized
bounds of order at most the fourth power of the maximal overlap. Logarithmic normalization
therefore gives one smallness horizon for every ratio in a bounded interval.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory HTGeometry

private theorem normalized_residual_small_of_uniform_sq_bound
    (K : ℝ) (r : ℝ → (N : ℕ) → EuclideanSpace ℝ (PrimeHorizonIndex N)) {C : ℝ}
    (hb : ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K → ‖r c N‖ ^ 2 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
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

/-- Both actual pole moments have a common normalized-mode error bound over bounded overlap. -/
theorem eventually_fullWeilPoleError_norm_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ≤ ε := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  have hb : ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 ≤
        4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2 * K ^ 4 := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈K⌉₊] with N hN hcN
    intro c hc0 hcK
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcN' : c ≤ N := hcK.trans ((Nat.le_ceil K).trans (by exact_mod_cast hcN))
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hd := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc0 hN hcN'
    have hs := mul_self_le_mul_self (abs_nonneg _) hd
    rw [← sq, sq_abs, ← sq] at hs
    have hprof : ∀ j ∈ Icc 1 N, |normalizedRamanujanMode m j| ≤ A :=
      fun j _ => abs_normalizedRamanujanMode_le hm j
    calc (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, atomPoleErrorCoefficient φ c N *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * ramanujanPoleProfile m j) ^ 2)
        = ∑ n ∈ Icc 1 N, (atomPoleErrorCoefficient φ c N * ∑ j ∈ Icc 1 N,
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 := by
          refine sum_congr rfl fun n _ => ?_
          rw [mul_sum]
          congr 1
          refine sum_congr rfl fun j _ => ?_
          simp only [ramanujanPoleProfile]
          ring
      _ ≤ 4 * (atomPoleErrorCoefficient φ c N) ^ 2 * A ^ 2 * (N : ℝ) ^ 4 :=
          sum_sq_twoPoleKernel_poleProfile_le hA N hprof _
      _ ≤ 4 * (atomPoleMomentErrorConstant φ * (c / N) ^ 2) ^ 2 * A ^ 2 * (N : ℝ) ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2 * c ^ 4 := by field_simp [hN0.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le hcK 4) (by positivity)
  have h := normalized_residual_small_of_uniform_sq_bound K
    (fun c N => Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector m N)) hb hε
  simpa only [normalizedRamanujanHorizonVector, map_smul] using h

/-- The actual far cross error has one vanishing norm bound throughout bounded overlap. -/
theorem eventually_separatedCrossError_norm_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ≤ ε := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  set K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hb : ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 ≤
        (36 * K₀ * A * K ^ 2) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro c hc0 hcK
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => if 2 * (c / N) < |Real.log j - Real.log n| then
        atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hentry := fun (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ Icc 1 N) =>
      abs_separatedCrossError_le hφ hsupp hM hc0 hN hn hj
    have h := sum_sq_kernel_poleProfile_le (mul_nonneg hK₀0 (sq_nonneg (c / (N : ℝ)))) hentry hA
      (fun j _ => abs_normalizedRamanujanMode_le hm j)
    calc (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, (if 2 * (c / N) < |Real.log j - Real.log n| then
          atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) * ramanujanPoleProfile m j) ^ 2)
        = ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, (if 2 * (c / N) < |Real.log j - Real.log n| then
          atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 := by
          refine sum_congr rfl fun n _ => ?_
          congr 1
      _ ≤ (36 * (K₀ * (c / N) ^ 2) * A) ^ 2 * (N : ℝ) ^ 4 := h
      _ = (36 * K₀ * A * c ^ 2) ^ 2 := by field_simp [hN0.ne']
      _ ≤ _ := by
        have hsq : c ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hc0.le hcK 2
        have hcoef := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 36 * K₀ * A by positivity)
        exact pow_le_pow_left₀ (by positivity) hcoef 2
  have h := normalized_residual_small_of_uniform_sq_bound K
    (fun c N => Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (ramanujanHorizonVector m N)) hb hε
  simpa only [normalizedRamanujanHorizonVector, map_smul] using h

/-- The self-energy remainder is uniformly small on every bounded overlap interval. -/
theorem eventually_completeWeilSelfError_norm_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  have hv : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖) atTop (𝓝 1) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
      (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).sqrt
  have hlim : Tendsto (fun N : ℕ =>
      (Real.exp (1 / 2) / 2 * K / (N : ℝ)) * ‖normalizedRamanujanHorizonVector m N‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).mul hv
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈K⌉₊, hlim.eventually (gt_mem_nhds hε)] with N hN hNK hsmall
  intro c hc0 hcK
  rw [norm_smul, Real.norm_eq_abs]
  have hcN : c ≤ (N : ℝ) := hcK.trans ((Nat.le_ceil K).trans (by exact_mod_cast hNK))
  have hs := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc0 hN hcN
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hcost : Real.exp (1 / 2) / 2 * (c / N) ≤ Real.exp (1 / 2) / 2 * K / N := by
    have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcK hn)
      (show 0 ≤ Real.exp (1 / 2) / 2 by positivity)
    simpa only [mul_div_assoc] using h
  exact (mul_le_mul_of_nonneg_right (hs.trans hcost) (norm_nonneg _)).trans hsmall.le

/-- The center source retains its charge and is uniformly controlled by its unit-overlap residual. -/
theorem eventually_fullWeilCenter_norm_uniform_overlap {φ : ℝ → ℝ}
    {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  have hlim := tendsto_fullWeilCenterMatrix_ramanujan_residual_norm hm (completeWeilPoleShift φ 1)
  filter_upwards [hlim.eventually (ge_mem_nhds (div_pos hε hK))] with N hsmall
  intro c hc0 hcK
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
  calc
    _ ≤ K * ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) N)
        (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ 1 else 0) • normalizedRamanujanHorizonVector m N‖ :=
      mul_le_mul_of_nonneg_right hcK (norm_nonneg _)
    _ ≤ K * (ε / K) := mul_le_mul_of_nonneg_left hsmall hK.le
    _ = ε := by field_simp

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_fullWeilPoleError_norm_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_separatedCrossError_norm_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeilSelfError_norm_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_fullWeilCenter_norm_uniform_overlap
