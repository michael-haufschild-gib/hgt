import GaloisForLFunctions.HilbertMetric.GaussianMetricRankOneFracture
import GaloisForLFunctions.RHTower.HermiteEvenSlaterPluckerConnector

/-!
# Gaussian metric curvature of the step-four Hermite block

The real Gram coordinates of the first `m` Fourier-fixed Hermite modes form an injective finite
Euclidean family.  Appending their actual step-four degrees as one metric feature therefore
discharges the abstract hypotheses of the HilbertMetric rank-one Gaussian law.

The resulting Gaussian log-volume is concave at every nonnegative scale.  Its curvature vanishes
exactly for the empty and one-mode blocks and is strictly negative exactly from rank two onward.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

/-- Gaussian metric Gram obtained by appending the actual step-four Hermite degree as one
additional feature. -/
def hermiteEvenStepFourGaussianMetricGram (m : ℕ) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  gaussianMetricRankOneExtensionGram
    (hermiteEvenRealGramCoordinates m)
    (fun j => (hermiteEvenStepFourDegree j : ℝ)) t

/-- Square-root similarity matrix whose self-commutator measures curvature of the actual Hermite
metric extension. -/
def hermiteEvenStepFourGaussianSimilarity (m : ℕ) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  matrixSqrtSimilarity
    (rankOneSchurExponentialPath
      (finiteGaussianDistanceGram (hermiteEvenRealGramCoordinates m) 1)
      (fun j => (hermiteEvenStepFourDegree j : ℝ)) (2 * t))
    (rankOneLabelDiagonal (fun j => (hermiteEvenStepFourDegree j : ℝ)))

/-- The actual square Hermite Gram coordinate family is injective. -/
theorem hermiteEvenRealGramCoordinates_injective (m : ℕ) :
    Function.Injective (hermiteEvenRealGramCoordinates m) := by
  intro i j hij
  by_contra hne
  have hvalue := congrFun hij i
  simp [hermiteEvenRealGramCoordinates_apply, Ne.symm hne] at hvalue

/-- The actual step-four degree labels are constant exactly below rank two. -/
theorem hermiteEvenStepFourDegree_constant_iff (m : ℕ) :
    (∀ i j : Fin m,
      (hermiteEvenStepFourDegree i : ℝ) =
        (hermiteEvenStepFourDegree j : ℝ)) ↔ m ≤ 1 := by
  constructor
  · intro hconstant
    by_contra hm
    have hm2 : 2 ≤ m := by omega
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, by omega⟩
    have h := hconstant i j
    norm_num [i, j, hermiteEvenStepFourDegree] at h
  · intro hm i j
    have hij : i = j := Fin.ext (by omega)
    exact congrArg (fun k : Fin m => (hermiteEvenStepFourDegree k : ℝ)) hij

/-- **Hermite Gaussian metric flatness classification.**  At every nonnegative scale, the
log-volume curvature vanishes exactly for the empty and ground-mode blocks. -/
theorem hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_eq_zero_iff
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t = 0 ↔
        m ≤ 1 := by
  change deriv (deriv (fun s => Real.log
    (gaussianMetricRankOneExtensionGram
      (hermiteEvenRealGramCoordinates m)
      (fun j => (hermiteEvenStepFourDegree j : ℝ)) s).det)) t = 0 ↔ m ≤ 1
  rw [gaussianMetricRankOneExtension_logDet_secondDerivative_eq_zero_iff_constant
      (hermiteEvenRealGramCoordinates m)
      (fun j => (hermiteEvenStepFourDegree j : ℝ))
      (hermiteEvenRealGramCoordinates_injective m) t ht]
  exact hermiteEvenStepFourDegree_constant_iff m

/-- **Hermite Gaussian normality classification.**  The square-root similarity behind the
actual Hermite Gaussian metric is normal exactly for the empty and ground-mode blocks.  Thus the
rank-two curvature transition is already visible as a self-commutator transition. -/
theorem hermiteEvenStepFourGaussianSimilarity_selfCommutator_eq_zero_iff
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    matrixSelfCommutator (hermiteEvenStepFourGaussianSimilarity m t) = 0 ↔
      m ≤ 1 := by
  have hbase :
      (finiteGaussianDistanceGram (hermiteEvenRealGramCoordinates m) 1).PosDef :=
    finiteGaussianDistanceGram_one_posDef_of_injective
      (hermiteEvenRealGramCoordinates m)
      (hermiteEvenRealGramCoordinates_injective m)
  have h2t : 0 ≤ 2 * t := mul_nonneg (by norm_num) ht
  change matrixSelfCommutator
      (matrixSqrtSimilarity
        (rankOneSchurExponentialPath
          (finiteGaussianDistanceGram (hermiteEvenRealGramCoordinates m) 1)
          (fun j => (hermiteEvenStepFourDegree j : ℝ)) (2 * t))
        (rankOneLabelDiagonal fun j => (hermiteEvenStepFourDegree j : ℝ))) = 0 ↔
    m ≤ 1
  rw [rankOneSchurExponential_selfCommutator_eq_zero_iff_block
    _ _ hbase _ h2t, ← hermiteEvenStepFourDegree_constant_iff m]
  constructor
  · intro hblock i j
    by_contra hij
    have hzero := hblock i j hij
    simp [finiteGaussianDistanceGram] at hzero
  · intro hconstant i j hij
    exact (hij (hconstant i j)).elim

/-- **Hermite Gaussian commutation classification.**  The positive exponential Gram underlying
the curvature similarity commutes with the actual step-four degree observable exactly below rank
two.  This identifies flatness with a genuine reducing-block condition, not only a determinant
identity. -/
theorem hermiteEvenStepFourGaussianExponential_commutes_labelDiagonal_iff
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    rankOneLabelDiagonal (fun j : Fin m => (hermiteEvenStepFourDegree j : ℝ)) *
        rankOneSchurExponentialPath
          (finiteGaussianDistanceGram (hermiteEvenRealGramCoordinates m) 1)
          (fun j => (hermiteEvenStepFourDegree j : ℝ)) (2 * t) =
      rankOneSchurExponentialPath
          (finiteGaussianDistanceGram (hermiteEvenRealGramCoordinates m) 1)
          (fun j => (hermiteEvenStepFourDegree j : ℝ)) (2 * t) *
        rankOneLabelDiagonal (fun j : Fin m => (hermiteEvenStepFourDegree j : ℝ)) ↔
      m ≤ 1 := by
  have hbase :
      (finiteGaussianDistanceGram (hermiteEvenRealGramCoordinates m) 1).PosDef :=
    finiteGaussianDistanceGram_one_posDef_of_injective
      (hermiteEvenRealGramCoordinates m)
      (hermiteEvenRealGramCoordinates_injective m)
  have h2t : 0 ≤ 2 * t := mul_nonneg (by norm_num) ht
  rw [← rankOneSchurExponential_selfCommutator_eq_zero_iff_commutes
    _ _ hbase _ h2t]
  exact hermiteEvenStepFourGaussianSimilarity_selfCommutator_eq_zero_iff m t ht

/-- The Hermite Gaussian similarity is nonnormal exactly from rank two onward. -/
theorem hermiteEvenStepFourGaussianSimilarity_selfCommutator_ne_zero_iff
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    matrixSelfCommutator (hermiteEvenStepFourGaussianSimilarity m t) ≠ 0 ↔
      2 ≤ m := by
  rw [ne_eq,
    hermiteEvenStepFourGaussianSimilarity_selfCommutator_eq_zero_iff m t ht]
  omega

/-- Flat Gaussian log-volume curvature is exactly normality of the associated Hermite
square-root similarity. -/
theorem hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_eq_zero_iff_normal
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t = 0 ↔
        matrixSelfCommutator (hermiteEvenStepFourGaussianSimilarity m t) = 0 := by
  rw [hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_eq_zero_iff m t ht,
    hermiteEvenStepFourGaussianSimilarity_selfCommutator_eq_zero_iff m t ht]

/-- **Hermite curvature/Fano commutator identity.**  The actual Gaussian log-volume curvature is
four times the signed one-matrix column-energy defect of its square-root similarity. -/
theorem hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_eq_fanoDefect
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t =
        4 * (matrixHilbertSchmidtEnergy
            (hermiteEvenStepFourGaussianSimilarity m t *
              hermiteEvenStepFourGaussianSimilarity m t) -
          Matrix.trace
            ((hermiteEvenStepFourGaussianSimilarity m t).transpose *
              hermiteEvenStepFourGaussianSimilarity m t *
              ((hermiteEvenStepFourGaussianSimilarity m t).transpose *
                hermiteEvenStepFourGaussianSimilarity m t))) := by
  have hcurvature := gaussianMetricRankOneExtension_logDet_secondDerivative_eq
    (hermiteEvenRealGramCoordinates m)
    (fun j => (hermiteEvenStepFourDegree j : ℝ))
    (hermiteEvenRealGramCoordinates_injective m) t ht
  change deriv (deriv (fun s => Real.log
    (gaussianMetricRankOneExtensionGram
      (hermiteEvenRealGramCoordinates m)
      (fun j => (hermiteEvenStepFourDegree j : ℝ)) s).det)) t = _
  rw [hcurvature]
  change -2 * matrixHilbertSchmidtEnergy
    (matrixSelfCommutator (hermiteEvenStepFourGaussianSimilarity m t)) = _
  rw [selfCommutator_energy_eq_two_mul_defect
    (hermiteEvenStepFourGaussianSimilarity m t)]
  ring

/-- **Hermite Gaussian metric strict phase law.**  At every nonnegative scale, the actual
step-four degree extension has strictly negative log-volume curvature exactly from rank two
onward. -/
theorem hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t < 0 ↔
        2 ≤ m := by
  constructor
  · intro hneg
    by_contra hm
    have hm1 : m ≤ 1 := by omega
    have hzero :=
      (hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_eq_zero_iff
        m t ht).2 hm1
    linarith
  · intro hm
    change deriv (deriv (fun s => Real.log
      (gaussianMetricRankOneExtensionGram
        (hermiteEvenRealGramCoordinates m)
        (fun j => (hermiteEvenStepFourDegree j : ℝ)) s).det)) t < 0
    apply gaussianMetricRankOneExtension_logDet_secondDerivative_lt_zero
      (hermiteEvenRealGramCoordinates m)
      (fun j => (hermiteEvenStepFourDegree j : ℝ))
      (hermiteEvenRealGramCoordinates_injective m) t ht
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, by omega⟩
    refine ⟨i, j, ?_⟩
    norm_num [i, j, hermiteEvenStepFourDegree]

/-- Strict Hermite Gaussian log-volume curvature is equivalent to nonnormality of the exact
square-root similarity. -/
theorem hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff_nonnormal
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t < 0 ↔
        matrixSelfCommutator (hermiteEvenStepFourGaussianSimilarity m t) ≠ 0 := by
  rw [hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff m t ht,
    hermiteEvenStepFourGaussianSimilarity_selfCommutator_ne_zero_iff m t ht]

/-- **Hermite Gaussian Fano phase law.**  The similarity-square energy is strictly below its
column-energy square exactly from rank two onward. -/
theorem hermiteEvenStepFourGaussianSimilarity_fanoDefect_pos_iff
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    matrixHilbertSchmidtEnergy
          (hermiteEvenStepFourGaussianSimilarity m t *
            hermiteEvenStepFourGaussianSimilarity m t) <
        Matrix.trace
          ((hermiteEvenStepFourGaussianSimilarity m t).transpose *
            hermiteEvenStepFourGaussianSimilarity m t *
            ((hermiteEvenStepFourGaussianSimilarity m t).transpose *
              hermiteEvenStepFourGaussianSimilarity m t)) ↔
      2 ≤ m := by
  rw [← hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff m t ht,
    hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_eq_fanoDefect m t ht]
  constructor <;> intro h <;> linarith

/-- The Gaussian log-volume of the actual step-four Hermite metric extension is globally concave
on the complete physical scale ray. -/
theorem hermiteEvenStepFourGaussianMetric_logDet_concaveOn (m : ℕ) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun t => Real.log (hermiteEvenStepFourGaussianMetricGram m t).det) := by
  simpa only [hermiteEvenStepFourGaussianMetricGram] using
    gaussianMetricRankOneExtension_logDet_concaveOn
      (hermiteEvenRealGramCoordinates m)
      (fun j => (hermiteEvenStepFourDegree j : ℝ))
      (hermiteEvenRealGramCoordinates_injective m)

end

end RHTower
