import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullWeilMatrixSplitsAtTheSpacing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTwoPoleReplacementHasUniformErrors
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilSelfEnergyHasItsFinitePart

/-!
# Exact center and error decomposition of the complete Weil matrix

At width `c/N`, the literal matrix is the logarithmic prime energy plus its
common self finite part, the joint center correction, and the two explicitly
bounded integral replacement errors. The decomposition includes both actual
pole products and retains the zero diagonal of the cross kernel.
-/

noncomputable section

open MeasureTheory Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The actual complete Weil matrix at a fixed width ratio, in atom-mass normalization. -/
def completeWeilMatrix (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  normalizedFullWeilHorizonMatrix (atomDilate φ (c / N)) N

theorem completeWeilMatrix_isHermitian (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (completeWeilMatrix φ c N).IsHermitian :=
  normalizedFullWeilHorizonMatrix_isHermitian _ _

/-- The joint two-pole and center-collar correction. -/
def fullWeilCenterMatrix (α : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => (α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)

theorem fullWeilCenterMatrix_isHermitian (α : ℝ) (N : ℕ) :
    (fullWeilCenterMatrix α N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro n j
  change fullWeilCenterMatrix α N j n = fullWeilCenterMatrix α N n j
  simp only [fullWeilCenterMatrix, arithmeticPoleKernel, archimedeanCenterKernel_comm (j : ℕ) n]
  ring

/-- The literal normalized archimedean cross-integral replacement error. -/
def fullWeilCrossErrorMatrix (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => atomCrossErrorKernel (atomDilate φ (c / N)) n j

/-- The error in replacing the product of both actual exponential pole moments. -/
def fullWeilPoleErrorMatrix (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => atomPoleErrorCoefficient φ c N * arithmeticPoleKernel n j

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

/-- Every separated matrix entry has the exact common-self, prime, center, and error decomposition. -/
theorem completeWeilMatrix_eq_decomposition {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hsep : c / N < atomSpacing N) :
    completeWeilMatrix φ c N =
      (Real.log N + completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) • (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) -
      fullPrimeMatrix N + fullWeilCenterMatrix (completeWeilPoleShift φ c) N -
        fullWeilCrossErrorMatrix φ c N + fullWeilPoleErrorMatrix φ c N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := div_pos hc hN0
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hcharge : (∫ u, atomDilate φ (c / N) u) ^ 2 /
      (∫ u, atomDilate φ (c / N) u ^ 2) = completeWeilPoleShift φ c / N := by
    rw [integral_atomDilate φ hw, integral_atomDilate_sq hw, completeWeilPoleShift]
    field_simp [hN0.ne', hc.ne', hM.ne']
  ext n j
  rw [completeWeilMatrix, normalizedFullWeilHorizonMatrix_apply_of_separated hgs hsep hG.ne',
    pole_product_eq_center_add_error]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, fullPrimeMatrix, fullWeilCenterMatrix, fullWeilCrossErrorMatrix,
    fullWeilPoleErrorMatrix, atomCrossErrorKernel, hcharge]
  by_cases hnj : n = j
  · subst j
    simp only [ite_true, archimedeanCenterKernel_self, completeWeilSelfError]
    ring
  · have hval : (n : ℕ) ≠ (j : ℕ) := fun h => hnj (Subtype.ext h)
    rw [if_neg hval, if_neg hnj, if_neg hval]
    ring

/-- The canonical complete matrix is the normalized actual Weil functional. -/
theorem completeWeilMatrix_inner_eq_weilQuad {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, x⟫ =
      weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) /
        (∫ u, atomDilate φ (c / N) u ^ 2) := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  exact normalizedFullWeilHorizonMatrix_inner_eq_weilQuad hg hgs hw.le N x

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
