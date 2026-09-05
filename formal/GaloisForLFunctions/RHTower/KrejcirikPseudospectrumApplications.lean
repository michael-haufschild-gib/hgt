import GaloisForLFunctions.HilbertMetric.PseudospectrumSimilarity
import GaloisForLFunctions.RHTower.SuzukiOnePrimeTerminalSimilarityTransport
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixMomentNeutralIndexAmplification
import GaloisForLFunctions.RHTower.HermiteEvenGaussianMetricCurvature

/-!
# Krejčiřík pseudospectral and metric applications

The bounded-similarity results surrounding equations (6)--(8) and Proposition 2 of
Krejčiřík--Siegl--Tater--Viola, arXiv:1402.1082, apply directly to three existing HGT models.

* The Suzuki one-prime terminal adjacency has a positive metric, the spectrum of its symmetric
  representative, and a condition-number pseudospectral sandwich.
* Every Deninger Gamma-six coefficient-faithful block has the analogous positive metric, real
  spectrum, and real-axis pseudospectral sandwich, at every shell and horizontal rate.
* The rank-two Hermite Gaussian similarity is simultaneously metric-self-adjoint and nonnormal in
  its displayed Euclidean coordinates.

All statements are finite-dimensional and use existing exact similarities; no spectral
computation or added analytic assumption is needed.
-/

open scoped Matrix Matrix.Norms.L2Operator
open scoped ComplexOrder
open GaloisForLFunctions.HilbertMetric

namespace RHTower

noncomputable section

/-- Positive metric induced by the inverse Suzuki terminal similarity. -/
def onePrimeTerminalKrejcirikMetric : Matrix (Fin 2) (Fin 2) ℂ :=
  onePrimeTerminalSimilarityInvᴴ * onePrimeTerminalSimilarityInv

/-- The nonsingular matrix inverse agrees with the displayed Suzuki inverse. -/
theorem onePrimeTerminalSimilarity_inverse :
    onePrimeTerminalSimilarity⁻¹ = onePrimeTerminalSimilarityInv := by
  calc
    onePrimeTerminalSimilarity⁻¹ =
        (onePrimeTerminalSimilarityUnit : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ :=
      congrArg Inv.inv coe_onePrimeTerminalSimilarityUnit.symm
    _ = ((onePrimeTerminalSimilarityUnit⁻¹ :
          (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) :=
      (Matrix.coe_units_inv onePrimeTerminalSimilarityUnit).symm
    _ = onePrimeTerminalSimilarityInv :=
      coe_onePrimeTerminalSimilarityUnit_inv

/-- The Suzuki similarity metric is strictly positive definite. -/
theorem onePrimeTerminalKrejcirikMetric_posDef :
    onePrimeTerminalKrejcirikMetric.PosDef := by
  rw [onePrimeTerminalKrejcirikMetric]
  apply Matrix.PosDef.conjTranspose_mul_self
  rw [Matrix.mulVec_injective_iff_isUnit,
    ← coe_onePrimeTerminalSimilarityUnit_inv]
  exact onePrimeTerminalSimilarityUnit⁻¹ |>.isUnit

/-- Proposition 2: the literal Suzuki adjacency is self-adjoint in its positive metric. -/
theorem onePrimeTerminalAdjacency_metric_relation :
    star onePrimeTerminalAdjacency * onePrimeTerminalKrejcirikMetric =
      onePrimeTerminalKrejcirikMetric * onePrimeTerminalAdjacency := by
  have hconj :
      onePrimeTerminalSimilarityInv * onePrimeTerminalAdjacency *
          onePrimeTerminalSimilarity =
        onePrimeTerminalSymmetricAdjacency := by
    rw [onePrimeTerminalAdjacency_eq_similarity]
    calc
      onePrimeTerminalSimilarityInv *
            (onePrimeTerminalSimilarity * onePrimeTerminalSymmetricAdjacency *
              onePrimeTerminalSimilarityInv) *
          onePrimeTerminalSimilarity =
          (onePrimeTerminalSimilarityInv * onePrimeTerminalSimilarity) *
            onePrimeTerminalSymmetricAdjacency *
              (onePrimeTerminalSimilarityInv * onePrimeTerminalSimilarity) := by
            noncomm_ring
      _ = onePrimeTerminalSymmetricAdjacency := by
        rw [onePrimeTerminalSimilarityInv_mul]
        simp
  have hself : IsSelfAdjoint (
      ((onePrimeTerminalSimilarityUnit⁻¹ :
          (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) *
        onePrimeTerminalAdjacency *
          (((onePrimeTerminalSimilarityUnit⁻¹)⁻¹ :
            (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [show
      ((onePrimeTerminalSimilarityUnit⁻¹ :
          (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) *
        onePrimeTerminalAdjacency *
          (((onePrimeTerminalSimilarityUnit⁻¹)⁻¹ :
            (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) =
        onePrimeTerminalSymmetricAdjacency by
          simpa [onePrimeTerminalSimilarity_inverse] using hconj]
    exact onePrimeTerminalSymmetricAdjacency_isHermitian
  simpa [onePrimeTerminalKrejcirikMetric, onePrimeTerminalSimilarity_inverse,
    Matrix.star_eq_conjTranspose] using
    units_conjugate_metric_relation
      (u := onePrimeTerminalSimilarityUnit⁻¹)
      onePrimeTerminalAdjacency hself

/-- Bounded similarity preserves the exact spectrum of the Suzuki terminal block. -/
theorem onePrimeTerminalAdjacency_spectrum_eq_symmetric :
    spectrum ℂ onePrimeTerminalAdjacency =
      spectrum ℂ onePrimeTerminalSymmetricAdjacency := by
  have h := spectrum.units_conjugate
    (R := ℂ) (A := Matrix (Fin 2) (Fin 2) ℂ)
    (u := onePrimeTerminalSimilarityUnit)
    (a := onePrimeTerminalSymmetricAdjacency)
  calc
    spectrum ℂ onePrimeTerminalAdjacency =
        spectrum ℂ (onePrimeTerminalSimilarity *
          onePrimeTerminalSymmetricAdjacency *
            onePrimeTerminalSimilarityInv) :=
      congrArg (spectrum ℂ) onePrimeTerminalAdjacency_eq_similarity
    _ = spectrum ℂ onePrimeTerminalSymmetricAdjacency := by
      simpa only [coe_onePrimeTerminalSimilarityUnit,
        coe_onePrimeTerminalSimilarityUnit_inv] using h

/-- Equation (8) specialized to the literal Suzuki terminal adjacency. -/
theorem onePrimeTerminalAdjacency_pseudospectrum_sandwich
    (ε : PseudospectralScale) :
      normResolventPseudospectrum ℂ
          (ε.divConditionNumber onePrimeTerminalSimilarityUnit)
          onePrimeTerminalSymmetricAdjacency ⊆
        normResolventPseudospectrum ℂ ε onePrimeTerminalAdjacency ∧
      normResolventPseudospectrum ℂ ε onePrimeTerminalAdjacency ⊆
        normResolventPseudospectrum ℂ
          (ε.mulConditionNumber onePrimeTerminalSimilarityUnit)
          onePrimeTerminalSymmetricAdjacency := by
  have h := normResolventPseudospectrum_similarity_sandwich
      (𝕜 := ℂ) ε onePrimeTerminalSimilarityUnit
        onePrimeTerminalSymmetricAdjacency
  have hconj :
      (onePrimeTerminalSimilarityUnit : Matrix (Fin 2) (Fin 2) ℂ) *
          onePrimeTerminalSymmetricAdjacency *
            ((onePrimeTerminalSimilarityUnit⁻¹ :
              (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) =
        onePrimeTerminalAdjacency := by
    simpa only [coe_onePrimeTerminalSimilarityUnit,
      coe_onePrimeTerminalSimilarityUnit_inv] using
        onePrimeTerminalAdjacency_eq_similarity.symm
  rw [hconj] at h
  exact h

/-- The displayed Deninger balancing gauge also has the displayed two-sided inverse. -/
theorem deningerGammaSixHyperbolicBalancingGauge_mul_inv
    (delta : ℝ) (m : ℕ) :
    deningerGammaSixHyperbolicBalancingGauge delta m *
        deningerGammaSixHyperbolicBalancingGaugeInv delta m = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerGammaSixHyperbolicBalancingGauge,
      deningerGammaSixHyperbolicBalancingGaugeInv,
      Matrix.mul_apply, Fin.sum_univ_two]
  rw [← Real.rpow_add (by positivity : 0 < ((6 : ℝ) ^ m)⁻¹)]
  norm_num

/-- The inverse balancing gauge bundled as a matrix unit. -/
def deningerGammaSixHyperbolicBalancingUnit
    (delta : ℝ) (m : ℕ) : (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  val := deningerGammaSixHyperbolicBalancingGaugeInv delta m
  inv := deningerGammaSixHyperbolicBalancingGauge delta m
  val_inv := deningerGammaSixHyperbolicBalancingGaugeInv_mul delta m
  inv_val := deningerGammaSixHyperbolicBalancingGauge_mul_inv delta m

@[simp] theorem coe_deningerGammaSixHyperbolicBalancingUnit
    (delta : ℝ) (m : ℕ) :
    (deningerGammaSixHyperbolicBalancingUnit delta m :
      Matrix (Fin 2) (Fin 2) ℝ) =
        deningerGammaSixHyperbolicBalancingGaugeInv delta m := rfl

@[simp] theorem coe_deningerGammaSixHyperbolicBalancingUnit_inv
    (delta : ℝ) (m : ℕ) :
    (((deningerGammaSixHyperbolicBalancingUnit delta m)⁻¹ :
      (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Matrix (Fin 2) (Fin 2) ℝ) =
        deningerGammaSixHyperbolicBalancingGauge delta m := rfl

/-- The nonsingular inverse of the inverse gauge is the forward gauge. -/
theorem deningerGammaSixHyperbolicBalancingGaugeInv_inverse
    (delta : ℝ) (m : ℕ) :
    (deningerGammaSixHyperbolicBalancingGaugeInv delta m)⁻¹ =
      deningerGammaSixHyperbolicBalancingGauge delta m := by
  calc
    (deningerGammaSixHyperbolicBalancingGaugeInv delta m)⁻¹ =
        (deningerGammaSixHyperbolicBalancingUnit delta m :
          Matrix (Fin 2) (Fin 2) ℝ)⁻¹ :=
      congrArg Inv.inv
        (coe_deningerGammaSixHyperbolicBalancingUnit delta m).symm
    _ = (((deningerGammaSixHyperbolicBalancingUnit delta m)⁻¹ :
          (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      (Matrix.coe_units_inv
        (deningerGammaSixHyperbolicBalancingUnit delta m)).symm
    _ = deningerGammaSixHyperbolicBalancingGauge delta m :=
      coe_deningerGammaSixHyperbolicBalancingUnit_inv delta m

/-- The balanced Deninger Gamma-six block is self-adjoint over the real star algebra. -/
theorem deningerGammaSixCriticalHyperbolicBlock_isSelfAdjoint (m : ℕ) :
    IsSelfAdjoint (deningerGammaSixCriticalHyperbolicBlock m) := by
  change star (deningerGammaSixCriticalHyperbolicBlock m) =
    deningerGammaSixCriticalHyperbolicBlock m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerGammaSixCriticalHyperbolicBlock, Matrix.star_apply]

/-- Positive metric induced by the inverse Deninger balancing gauge. -/
def deningerGammaSixKrejcirikMetric (delta : ℝ) (m : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (deningerGammaSixHyperbolicBalancingGaugeInv delta m)ᴴ *
    deningerGammaSixHyperbolicBalancingGaugeInv delta m

/-- The Deninger balancing metric is strictly positive at every rate and shell. -/
theorem deningerGammaSixKrejcirikMetric_posDef (delta : ℝ) (m : ℕ) :
    (deningerGammaSixKrejcirikMetric delta m).PosDef := by
  rw [deningerGammaSixKrejcirikMetric]
  apply Matrix.PosDef.conjTranspose_mul_self
  rw [Matrix.mulVec_injective_iff_isUnit,
    ← coe_deningerGammaSixHyperbolicBalancingUnit delta m]
  exact (deningerGammaSixHyperbolicBalancingUnit delta m).isUnit

/-- Proposition 2 for every coefficient-faithful Deninger Gamma-six block. -/
theorem deningerGammaSixCoefficientFaithful_metric_relation
    (delta : ℝ) (m : ℕ) :
    star (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m) *
        deningerGammaSixKrejcirikMetric delta m =
      deningerGammaSixKrejcirikMetric delta m *
        deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m := by
  have hself : IsSelfAdjoint (
      ((deningerGammaSixHyperbolicBalancingUnit delta m :
          (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Matrix (Fin 2) (Fin 2) ℝ) *
        deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m *
          (((deningerGammaSixHyperbolicBalancingUnit delta m)⁻¹ :
            (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [show
      ((deningerGammaSixHyperbolicBalancingUnit delta m :
          (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Matrix (Fin 2) (Fin 2) ℝ) *
        deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m *
          (((deningerGammaSixHyperbolicBalancingUnit delta m)⁻¹ :
            (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Matrix (Fin 2) (Fin 2) ℝ) =
        deningerGammaSixCriticalHyperbolicBlock m by
          simpa [deningerGammaSixHyperbolicBalancingGaugeInv_inverse] using
            deningerGammaSixHyperbolicBalancing_similarity delta m]
    exact deningerGammaSixCriticalHyperbolicBlock_isSelfAdjoint m
  simpa [deningerGammaSixKrejcirikMetric, Matrix.star_eq_conjTranspose] using
    units_conjugate_metric_relation
      (u := deningerGammaSixHyperbolicBalancingUnit delta m)
      (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m) hself

/-- Balancing preserves the exact real spectrum of every Deninger Gamma-six block. -/
theorem deningerGammaSixCoefficientFaithful_spectrum_eq_critical
    (delta : ℝ) (m : ℕ) :
    spectrum ℝ (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m) =
      spectrum ℝ (deningerGammaSixCriticalHyperbolicBlock m) := by
  have h := spectrum.units_conjugate
    (R := ℝ) (A := Matrix (Fin 2) (Fin 2) ℝ)
    (u := deningerGammaSixHyperbolicBalancingUnit delta m)
    (a := deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m)
  have hconj :
      (deningerGammaSixHyperbolicBalancingUnit delta m :
          Matrix (Fin 2) (Fin 2) ℝ) *
        deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m *
          (((deningerGammaSixHyperbolicBalancingUnit delta m)⁻¹ :
            (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Matrix (Fin 2) (Fin 2) ℝ) =
        deningerGammaSixCriticalHyperbolicBlock m := by
    simpa [deningerGammaSixHyperbolicBalancingGaugeInv_inverse] using
      deningerGammaSixHyperbolicBalancing_similarity delta m
  rw [hconj] at h
  exact h.symm

/-- Equation (8) on the real axis for every Deninger Gamma-six block. -/
theorem deningerGammaSixCoefficientFaithful_pseudospectrum_sandwich
    (delta : ℝ) (m : ℕ) (ε : PseudospectralScale) :
    normResolventPseudospectrum ℝ
          (ε.divConditionNumber
            (deningerGammaSixHyperbolicBalancingUnit delta m))
          (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m) ⊆
        normResolventPseudospectrum ℝ ε
          (deningerGammaSixCriticalHyperbolicBlock m) ∧
      normResolventPseudospectrum ℝ ε
          (deningerGammaSixCriticalHyperbolicBlock m) ⊆
        normResolventPseudospectrum ℝ
          (ε.mulConditionNumber
            (deningerGammaSixHyperbolicBalancingUnit delta m))
          (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m) := by
  have h := normResolventPseudospectrum_similarity_sandwich
    (𝕜 := ℝ) ε (deningerGammaSixHyperbolicBalancingUnit delta m)
      (deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m)
  have hconj :
      (deningerGammaSixHyperbolicBalancingUnit delta m :
          Matrix (Fin 2) (Fin 2) ℝ) *
        deningerGammaSixCoefficientFaithfulHyperbolicBlock delta m *
          (((deningerGammaSixHyperbolicBalancingUnit delta m)⁻¹ :
            (Matrix (Fin 2) (Fin 2) ℝ)ˣ) : Matrix (Fin 2) (Fin 2) ℝ) =
        deningerGammaSixCriticalHyperbolicBlock m := by
    simpa [deningerGammaSixHyperbolicBalancingGaugeInv_inverse] using
      deningerGammaSixHyperbolicBalancing_similarity delta m
  rw [hconj] at h
  exact h

/-- Positive exponential Gram underlying the concrete rank-two, unit-scale Hermite similarity. -/
def hermiteRankTwoExponentialMetric : Matrix (Fin 2) (Fin 2) ℝ :=
  rankOneSchurExponentialPath
    (finiteGaussianDistanceGram (hermiteEvenRealGramCoordinates 2) 1)
    (fun j => (hermiteEvenStepFourDegree j : ℝ)) (2 * 1)

/-- Step-four degree observable underlying the concrete rank-two Hermite similarity. -/
def hermiteRankTwoDegreeObservable : Matrix (Fin 2) (Fin 2) ℝ :=
  rankOneLabelDiagonal (fun j => (hermiteEvenStepFourDegree j : ℝ))

/-- Proposition 2 metric relation for the concrete rank-two Hermite Gaussian similarity. -/
theorem hermiteRankTwoGaussianSimilarity_metric_relation :
    hermiteRankTwoExponentialMetric⁻¹ *
        hermiteEvenStepFourGaussianSimilarity 2 1 =
      (hermiteEvenStepFourGaussianSimilarity 2 1).transpose *
        hermiteRankTwoExponentialMetric⁻¹ := by
  have hbase :
      (finiteGaussianDistanceGram (hermiteEvenRealGramCoordinates 2) 1).PosDef :=
    finiteGaussianDistanceGram_one_posDef_of_injective
      (hermiteEvenRealGramCoordinates 2)
      (hermiteEvenRealGramCoordinates_injective 2)
  have hmetric : hermiteRankTwoExponentialMetric.PosDef := by
    exact rankOneSchurExponentialPath_posDef _ _ hbase _ (by norm_num)
  simpa [hermiteRankTwoExponentialMetric, hermiteRankTwoDegreeObservable,
    hermiteEvenStepFourGaussianSimilarity] using
    matrixSqrtSimilarity_metric_relation hermiteRankTwoExponentialMetric hmetric
      hermiteRankTwoDegreeObservable
      (rankOneLabelDiagonal_transpose _)

/-- The same rank-two Hermite operator is nonnormal in its displayed Euclidean coordinates. -/
theorem hermiteRankTwoGaussianSimilarity_isNonnormal :
    matrixSelfCommutator (hermiteEvenStepFourGaussianSimilarity 2 1) ≠ 0 := by
  exact (hermiteEvenStepFourGaussianSimilarity_selfCommutator_ne_zero_iff
    2 1 (by norm_num)).2 (by norm_num)

end

end RHTower
