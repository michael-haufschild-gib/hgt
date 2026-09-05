import GaloisForLFunctions.HilbertMetric.PseudospectrumSimilarity
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianCurvatureHilbertPhase

/-!
# Krejčiřík metric for the transverse valuation Gaussian similarity

Proposition 2 of Krejčiřík--Siegl--Tater--Viola, arXiv:1402.1082, applies to the
positive-square-root similarity already used to measure transverse Xi valuation curvature.
Every collision-free shift packet therefore carries an explicit positive metric in which the
displayed operator is self-adjoint.  At rank two this holds simultaneously with the existing
strict Euclidean nonnormality theorem.
-/

open scoped Matrix Matrix.Norms.L2Operator
open GaloisForLFunctions.HilbertMetric

namespace RHTower

noncomputable section

/-- Positive exponential Gram used in the transverse valuation square-root similarity. -/
def xiTransversePrimeValuationExponentialMetric
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  rankOneSchurExponentialPath
    (finiteGaussianDistanceGram
      (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p) 1)
    (fun j => (shift j : ℝ)) (2 * t)

/-- Inverse exponential Gram giving the Krejčiřík metric for a transverse valuation packet. -/
def xiTransversePrimeValuationKrejcirikMetric
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (xiTransversePrimeValuationExponentialMetric shift p t)⁻¹

/-- Collision freedom makes the exponential Gram strictly positive. -/
theorem xiTransversePrimeValuationExponentialMetric_posDef_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (t : ℝ) (ht : 0 ≤ t) :
    (xiTransversePrimeValuationExponentialMetric shift p t).PosDef := by
  have hbase :
      (finiteGaussianDistanceGram
        (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p) 1).PosDef :=
    finiteGaussianDistanceGram_one_posDef_of_injective _
      (xiTransversePrimeFirstValuationGaussianFeature_injective_of_injective
        shift p hinjective)
  exact rankOneSchurExponentialPath_posDef
    (finiteGaussianDistanceGram
      (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p) 1)
    (fun j => (shift j : ℝ)) hbase (2 * t) (mul_nonneg (by norm_num) ht)

/-- Collision freedom makes the transverse Krejčiřík metric strictly positive. -/
theorem xiTransversePrimeValuationKrejcirikMetric_posDef_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (t : ℝ) (ht : 0 ≤ t) :
    (xiTransversePrimeValuationKrejcirikMetric shift p t).PosDef := by
  exact (xiTransversePrimeValuationExponentialMetric_posDef_of_injective
    shift p hinjective t ht).inv

/-- Proposition 2: every collision-free transverse valuation Gaussian similarity is
self-adjoint in its explicit positive Krejčiřík metric. -/
theorem xiTransversePrimeValuationGaussianSimilarity_metric_relation_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (t : ℝ) (ht : 0 ≤ t) :
    xiTransversePrimeValuationKrejcirikMetric shift p t *
        xiTransversePrimeValuationRankOneGaussianSimilarity shift p t =
      (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t).transpose *
        xiTransversePrimeValuationKrejcirikMetric shift p t := by
  have hmetric := xiTransversePrimeValuationExponentialMetric_posDef_of_injective
    shift p hinjective t ht
  simpa [xiTransversePrimeValuationKrejcirikMetric,
    xiTransversePrimeValuationExponentialMetric,
    xiTransversePrimeValuationRankOneGaussianSimilarity] using
    matrixSqrtSimilarity_metric_relation
      (xiTransversePrimeValuationExponentialMetric shift p t) hmetric
      (rankOneLabelDiagonal (fun j => (shift j : ℝ)))
      (rankOneLabelDiagonal_transpose _)

/-- Collision-free transverse valuation similarity has exactly the spectrum of its diagonal
shift observable. -/
theorem xiTransversePrimeValuationGaussianSimilarity_spectrum_eq_labelDiagonal_of_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (t : ℝ) (ht : 0 ≤ t) :
    spectrum ℝ (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) =
      spectrum ℝ (rankOneLabelDiagonal (fun j => (shift j : ℝ))) := by
  have hmetric := xiTransversePrimeValuationExponentialMetric_posDef_of_injective
    shift p hinjective t ht
  simpa [xiTransversePrimeValuationExponentialMetric,
    xiTransversePrimeValuationRankOneGaussianSimilarity] using
    matrixSqrtSimilarity_spectrum_eq
      (xiTransversePrimeValuationExponentialMetric shift p t) hmetric
      (rankOneLabelDiagonal (fun j => (shift j : ℝ)))

/-- Equation (8) for every nonempty collision-free transverse valuation packet. -/
theorem xiTransversePrimeValuationGaussianSimilarity_pseudospectrum_sandwich_of_injective
    {N : ℕ} [Nonempty (Fin N)] (shift : Fin N → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective shift) (t : ℝ) (ht : 0 ≤ t)
    (ε : PseudospectralScale) :
    normResolventPseudospectrum ℝ
          (ε.divConditionNumber
            (matrixSqrtUnit
              (xiTransversePrimeValuationExponentialMetric shift p t)
              (xiTransversePrimeValuationExponentialMetric_posDef_of_injective
                shift p hinjective t ht)))
          (rankOneLabelDiagonal (fun j => (shift j : ℝ))) ⊆
        normResolventPseudospectrum ℝ ε
          (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) ∧
      normResolventPseudospectrum ℝ ε
          (xiTransversePrimeValuationRankOneGaussianSimilarity shift p t) ⊆
        normResolventPseudospectrum ℝ
          (ε.mulConditionNumber
            (matrixSqrtUnit
              (xiTransversePrimeValuationExponentialMetric shift p t)
              (xiTransversePrimeValuationExponentialMetric_posDef_of_injective
                shift p hinjective t ht)))
          (rankOneLabelDiagonal (fun j => (shift j : ℝ))) := by
  have hmetric := xiTransversePrimeValuationExponentialMetric_posDef_of_injective
    shift p hinjective t ht
  simpa [xiTransversePrimeValuationExponentialMetric,
    xiTransversePrimeValuationRankOneGaussianSimilarity] using
    matrixSqrtSimilarity_pseudospectrum_sandwich ε
      (xiTransversePrimeValuationExponentialMetric shift p t) hmetric
      (rankOneLabelDiagonal (fun j => (shift j : ℝ)))

/-- Concrete collision-free rank-two shift packet. -/
def krejcirikXiTransverseRankTwoShift (j : Fin 2) : ℕ := j.val

/-- Prime two as a closed transverse valuation parameter. -/
def krejcirikXiPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem krejcirikXiTransverseRankTwoShift_injective :
    Function.Injective krejcirikXiTransverseRankTwoShift := by
  intro i j hij
  exact Fin.ext hij

/-- Closed rank-two instance of the positive Krejčiřík metric. -/
theorem krejcirikXiTransverseRankTwoMetric_posDef :
    (xiTransversePrimeValuationKrejcirikMetric
      krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1).PosDef := by
  exact xiTransversePrimeValuationKrejcirikMetric_posDef_of_injective
    krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo
    krejcirikXiTransverseRankTwoShift_injective 1 (by norm_num)

/-- Closed rank-two transverse valuation operator is self-adjoint in its positive metric. -/
theorem krejcirikXiTransverseRankTwoSimilarity_metric_relation :
    xiTransversePrimeValuationKrejcirikMetric
        krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1 *
        xiTransversePrimeValuationRankOneGaussianSimilarity
          krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1 =
      (xiTransversePrimeValuationRankOneGaussianSimilarity
        krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1).transpose *
        xiTransversePrimeValuationKrejcirikMetric
          krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1 := by
  exact xiTransversePrimeValuationGaussianSimilarity_metric_relation_of_injective
    krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo
    krejcirikXiTransverseRankTwoShift_injective 1 (by norm_num)

/-- Closed rank-two transverse valuation operator has exactly the spectrum of its shift
observable. -/
theorem krejcirikXiTransverseRankTwoSimilarity_spectrum_eq_labelDiagonal :
    spectrum ℝ
        (xiTransversePrimeValuationRankOneGaussianSimilarity
          krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1) =
      spectrum ℝ
        (rankOneLabelDiagonal
          (fun j => (krejcirikXiTransverseRankTwoShift j : ℝ))) := by
  exact
    xiTransversePrimeValuationGaussianSimilarity_spectrum_eq_labelDiagonal_of_injective
      krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo
      krejcirikXiTransverseRankTwoShift_injective 1 (by norm_num)

/-- Closed rank-two instance of the condition-number pseudospectral sandwich. -/
theorem krejcirikXiTransverseRankTwoSimilarity_pseudospectrum_sandwich
    (ε : PseudospectralScale) :
    normResolventPseudospectrum ℝ
          (ε.divConditionNumber
            (matrixSqrtUnit
              (xiTransversePrimeValuationExponentialMetric
                krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1)
              (xiTransversePrimeValuationExponentialMetric_posDef_of_injective
                krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo
                krejcirikXiTransverseRankTwoShift_injective 1 (by norm_num))))
          (rankOneLabelDiagonal
            (fun j => (krejcirikXiTransverseRankTwoShift j : ℝ))) ⊆
        normResolventPseudospectrum ℝ ε
          (xiTransversePrimeValuationRankOneGaussianSimilarity
            krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1) ∧
      normResolventPseudospectrum ℝ ε
          (xiTransversePrimeValuationRankOneGaussianSimilarity
            krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1) ⊆
        normResolventPseudospectrum ℝ
          (ε.mulConditionNumber
            (matrixSqrtUnit
              (xiTransversePrimeValuationExponentialMetric
                krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1)
              (xiTransversePrimeValuationExponentialMetric_posDef_of_injective
                krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo
                krejcirikXiTransverseRankTwoShift_injective 1 (by norm_num))))
          (rankOneLabelDiagonal
            (fun j => (krejcirikXiTransverseRankTwoShift j : ℝ))) := by
  exact
    xiTransversePrimeValuationGaussianSimilarity_pseudospectrum_sandwich_of_injective
      krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo
      krejcirikXiTransverseRankTwoShift_injective 1 (by norm_num) ε

/-- The same closed operator is nonnormal in the displayed Euclidean coordinates. -/
theorem krejcirikXiTransverseRankTwoSimilarity_isNonnormal :
    matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity
        krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo 1) ≠ 0 := by
  exact
    (xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_ne_zero_iff_of_injective
      krejcirikXiTransverseRankTwoShift krejcirikXiPrimeTwo
      krejcirikXiTransverseRankTwoShift_injective 1 (by norm_num)).2 (by norm_num)

end

end RHTower
