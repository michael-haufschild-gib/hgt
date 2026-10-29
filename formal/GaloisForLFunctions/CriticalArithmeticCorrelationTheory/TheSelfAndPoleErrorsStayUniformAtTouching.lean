import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTouchingCrossMatrixHasAUniformErrorBudget

/-!
# Self and pole remainders through touching

The actual Robin remainder and the product of both exponential pole moments
need only a dilation width at most one. Their quantitative bounds therefore
hold simultaneously at every width ratio in `(0,1]`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  ArithmeticElectrostatics HTGeometry
open _root_.RHTower (gammaHardyPhaseRate levyEnergy)

private theorem completeWeil_self_scalar_identity (φ : ℝ → ℝ) {c : ℝ}
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    2 * gammaHardyPhaseRate 0 + Real.log (1 / (c / N)) + profileRobin φ - Real.log N =
      completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (1 / (c / N)) - Real.log N = -Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hN0.ne']
    ring
  have hs : completeWeilSelfFinitePart φ c =
      -Real.log (2 * Real.pi) - Real.log c + bumpRobin φ 1 / (∫ u, φ u ^ 2) := by
    rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
      Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc.ne']
    ring
  have h := finitePart_profileRobin_eq φ
  rw [hs]
  linarith only [h, hlog]

/-- The actual normalized self remainder is linear in width, including ratio one. -/
theorem abs_completeWeilSelfError_le_at_touching {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 * (c / N) := by
  have hcs : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hφ (by norm_num)
  have hLip : ∀ u v, |φ u - φ v| ≤ (K : ℝ) * |u - v| := by
    intro u v
    simpa only [Real.dist_eq] using hK.dist_le_mul u v
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr
    (hc1.trans (by exact_mod_cast hN))
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]
    exact mul_pos hw0 hM
  have h := abs_levyEnergy_atomDilate_sub_le hφ hsupp hM hw0 hw1 hLip
  have heq : completeWeilSelfError φ c N =
      (levyEnergy (atomDilate φ (c / N)) -
        (Real.log (1 / (c / N)) + profileRobin φ) *
          ∫ u, atomDilate φ (c / N) u ^ 2) / (∫ u, atomDilate φ (c / N) u ^ 2) := by
    rw [completeWeilSelfError, ← completeWeil_self_scalar_identity φ hc0 hN]
    field_simp [hG.ne']
    ring
  rw [heq, abs_div, abs_of_pos hG, div_le_iff₀ hG]
  exact h

/-- The product of the two actual pole moments has quadratic scalar error through touching. -/
theorem abs_atomPoleErrorCoefficient_le_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    |atomPoleErrorCoefficient φ c N| ≤ atomPoleMomentErrorConstant φ * (c / N) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr
    (hc1.trans (by exact_mod_cast hN))
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

/-- Both actual pole moments have a uniform whole-form budget at every ratio up to one. -/
theorem abs_fullWeilPoleErrorMatrix_inner_le_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) x, x⟫| ≤
      (2 * atomPoleMomentErrorConstant φ * c ^ 2) * ‖x‖ ^ 2 := by
  change |⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N) x, x⟫| ≤ _
  rw [horizonKernelMatrix_inner, ← sum_primeHorizonExtension_sq]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := abs_atomPoleErrorCoefficient_le_at_touching hφ hsupp hM hc0 hc1 hN
  calc
    _ ≤ 2 * |atomPoleErrorCoefficient φ c N| * (N : ℝ) ^ 2 *
        ∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2 :=
      abs_twoPoleKernel_quadratic_le N (primeHorizonExtension x) _
    _ ≤ 2 * (atomPoleMomentErrorConstant φ * (c / N) ^ 2) * (N : ℝ) ^ 2 *
        ∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun n _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (sq_nonneg _)
    _ = _ := by field_simp [hN0.ne']

/-- The actual pole error has bounded square residual on each bounded pole profile. -/
theorem sum_sq_atomPoleError_poleProfile_le_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {a : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ j ∈ Icc 1 N, |a j| ≤ A) :
    (∑ n ∈ Icc 1 N, (atomPoleErrorCoefficient φ c N * ∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
        (a j / Real.sqrt j)) ^ 2) ≤
      4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2 * c ^ 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := abs_atomPoleErrorCoefficient_le_at_touching hφ hsupp hM hc0 hc1 hN
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

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_completeWeilSelfError_le_at_touching
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_fullWeilPoleErrorMatrix_inner_le_at_touching
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_sq_atomPoleError_poleProfile_le_at_touching
