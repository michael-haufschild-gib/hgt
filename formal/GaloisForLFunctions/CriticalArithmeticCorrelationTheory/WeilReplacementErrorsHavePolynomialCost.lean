import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheReplacementErrorsVanishUniformlyOnBoundedOverlap

/-!
# Polynomial overlap bounds for the complete Weil replacements

Raw pole and separated-cross bounds lose only fourth powers of overlap after
normalization. The center residual scales exactly linearly with its charge,
and the self remainder is controlled by the physical width `c/N`.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory HTGeometry

private theorem normalized_matrix_action_norm_sq {N : ℕ} (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
    (m : ℕ) :
    ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
      ‖Matrix.toEuclideanLin A (ramanujanHorizonVector m N)‖ ^ 2 / Real.log N := by
  rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

/-- The actual two-pole replacement has fourth-power overlap cost in normalized squared norm. -/
theorem exists_fullWeilPoleError_norm_sq_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 < c → ∀ N : ℕ, 1 ≤ N → c ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ C * c ^ 4 / Real.log N := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  refine ⟨4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2, by positivity, ?_⟩
  intro c hc0 N hN hcN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 ≤
      4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2 * c ^ 4 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hd := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc0 hN hcN
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
  rw [normalized_matrix_action_norm_sq]
  exact div_le_div_of_nonneg_right hb (Real.log_natCast_nonneg N)

/-- The separated cross replacement has fourth-power overlap cost at every positive horizon. -/
theorem exists_separatedCrossError_norm_sq_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 < c → ∀ N : ℕ, 1 ≤ N →
      ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ C * c ^ 4 / Real.log N := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  set K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨(36 * K₀ * A) ^ 2, by positivity, ?_⟩
  intro c hc0 N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 ≤
      (36 * K₀ * A) ^ 2 * c ^ 4 := by
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
      _ = _ := by ring
  rw [normalized_matrix_action_norm_sq]
  exact div_le_div_of_nonneg_right hb (Real.log_natCast_nonneg N)

/-- The exact center residual scales quadratically in overlap in squared norm. -/
theorem exists_fullWeilCenter_norm_sq_polynomial_bound (φ : ℝ → ℝ) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, ∀ N : ℕ,
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        C * c ^ 2 / Real.log N := by
  obtain ⟨C, hC, hbound⟩ := exists_fullWeilCenterMatrix_residual_bound hm (completeWeilPoleShift φ 1)
  refine ⟨C, hC, ?_⟩
  intro c N
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
  have hnorm :
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ 1 else 0) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        C / Real.log N := by
    simp only [normalizedRamanujanHorizonVector, map_smul]
    rw [smul_comm (if m = 1 then completeWeilPoleShift φ 1 else 0) (Real.sqrt (Real.log N))⁻¹,
      ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (Real.log_natCast_nonneg N)]
    have h := div_le_div_of_nonneg_right (hbound N) (Real.log_natCast_nonneg N)
    simpa only [div_eq_mul_inv, mul_comm] using h
  rw [hmatrix, hif, map_smul, LinearMap.smul_apply, mul_smul, ← smul_sub,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact (mul_le_mul_of_nonneg_left hnorm (sq_nonneg c)).trans_eq (by ring)

/-- The self remainder is quadratic in physical width after taking squared norm. -/
theorem exists_completeWeilSelfError_norm_sq_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) →
      ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        C * c ^ 2 / (N : ℝ) ^ 2 := by
  let A : ℝ := Real.exp (1 / 2) / 2
  refine ⟨2 * A ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).eventually
      (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with N hN hv
  intro c hc hcN
  have hs := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc hN hcN
  have hsq := mul_self_le_mul_self (abs_nonneg _) hs
  rw [← sq, sq_abs, ← sq] at hsq
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (A * (c / N)) ^ 2 * 2 := mul_le_mul hsq hv.le (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_fullWeilPoleError_norm_sq_polynomial_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_separatedCrossError_norm_sq_polynomial_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_fullWeilCenter_norm_sq_polynomial_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeilSelfError_norm_sq_polynomial_bound
