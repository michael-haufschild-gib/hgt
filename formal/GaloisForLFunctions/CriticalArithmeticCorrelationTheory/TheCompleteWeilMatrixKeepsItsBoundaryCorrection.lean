import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheActualArchimedeanMatrixReachesTouching
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNonRatioMatrixIsTheActualPrimeCorrection

/-!
# The complete source retains the boundary correction

Through width ratio one, the exact complete matrix consists of its prime
energy, self finite part, center correction, cross and pole errors, and the
literal non-ratio prime matrix. The last term has a negative sign because
the explicit formula subtracts the prime source.
-/

noncomputable section

open MeasureTheory Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory

private theorem integral_atomDilate (φ : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ u, atomDilate φ w u) = w * ∫ u, φ u := by
  simpa only [atomDilate, smul_eq_mul, abs_of_pos hw] using
    MeasureTheory.Measure.integral_comp_div φ w

private theorem pole_product_eq_center_add_error (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    ((∫ u, atomDilate φ (c / N) u * Real.exp (-(u / 2))) *
      (∫ u, atomDilate φ (c / N) u * Real.exp (u / 2)) /
        (∫ u, atomDilate φ (c / N) u ^ 2)) =
      atomPoleErrorCoefficient φ c N + completeWeilPoleShift φ c / N := by
  have hneg : atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) =
      ∫ u, atomDilate φ (c / N) u * Real.exp (-(u / 2)) := by
    unfold atomExponentialMoment
    congr 1
    funext u
    congr 2
    ring
  have hpos : atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) =
      ∫ u, atomDilate φ (c / N) u * Real.exp (u / 2) := by
    unfold atomExponentialMoment
    congr 1
    funext u
    congr 2
    ring
  rw [atomPoleErrorCoefficient, hneg, hpos]
  ring

/-- The full matrix through touching includes its actual non-ratio prime correction. -/
theorem completeWeilMatrix_eq_decomposition_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    completeWeilMatrix φ c N =
      (Real.log N + completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) • (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) -
      fullPrimeMatrix N + fullWeilCenterMatrix (completeWeilPoleShift φ c) N -
        fullWeilCrossErrorMatrix φ c N + fullWeilPoleErrorMatrix φ c N -
          fullWeilNonRatioMatrix φ c N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := div_pos hc0 hN0
  have hwN : c / (N : ℝ) ≤ 1 / N := div_le_div_of_nonneg_right hc1 hN0.le
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hcharge : (∫ u, atomDilate φ (c / N) u) ^ 2 /
      (∫ u, atomDilate φ (c / N) u ^ 2) = completeWeilPoleShift φ c / N := by
    rw [integral_atomDilate φ hw, integral_atomDilate_sq hw, completeWeilPoleShift]
    field_simp [hN0.ne', hc0.ne', hM.ne']
  ext n j
  rw [completeWeilMatrix, normalizedFullWeilHorizonMatrix_apply_at_touching hgs hwN hG.ne',
    pole_product_eq_center_add_error]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, fullPrimeMatrix, fullWeilCenterMatrix, fullWeilCrossErrorMatrix,
    fullWeilPoleErrorMatrix, fullWeilNonRatioMatrix_apply, atomCrossErrorKernel, hcharge]
  by_cases hnj : n = j
  · subst j
    simp only [ite_true, archimedeanCenterKernel_self, completeWeilSelfError]
    ring
  · have hval : (n : ℕ) ≠ (j : ℕ) := fun h => hnj (Subtype.ext h)
    rw [if_neg hval, if_neg hnj, if_neg hval]
    ring

private theorem identity_matrix_action {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

/-- The exact complete energy through touching subtracts the actual non-ratio source. -/
theorem completeWeilEnergy_eq_decomposition_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N x = renormalizedPrimeEnergy N x +
      (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) * ‖x‖ ^ 2 +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) x, x⟫ -
      ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) x, x⟫ +
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) x, x⟫ -
      ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x, x⟫ := by
  rw [completeWeilEnergy, completeWeilMatrix_eq_decomposition_at_touching hφ hsupp hM hc0 hc1 hN]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, identity_matrix_action, inner_add_left, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, renormalizedPrimeEnergy]
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.completeWeilMatrix_eq_decomposition_at_touching
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.completeWeilEnergy_eq_decomposition_at_touching
