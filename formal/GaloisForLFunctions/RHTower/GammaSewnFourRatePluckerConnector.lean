import GaloisForLFunctions.RHTower.GammaSewnFourRateSchurFisherCurvature
import GaloisForLFunctions.HilbertMetric.GradedPartition

/-!
# Gamma-sewn four-rate Pluecker connector

The six raw boundary-pair weights of the four-rate Gamma cell are not merely analogous to
Pluecker coordinates.  They are exactly the Cauchy--Binet expansion of a concrete weighted
two-row rational feature Gram determinant, hence exactly the degree-zero canonical feature
volume from `HilbertMetric.GradedPartition`.  Choosing a direct factorization of the simplified
Pluecker coordinates makes this identity unconditional, including at denominator-zero inputs.

This is a static boundary-partition connector.  It does not identify the Gamma Schur curvature
with the exponential-degree Slater variance: Gamma second jets also carry the source-specific
Fisher self-curvature isolated in `GammaSewnFourRateSchurFisherCurvature`.
-/

open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Weighted two-row rational feature whose pair minors are the simplified Gamma boundary
Pluecker coordinates. -/
def gammaSewnFourRateBoundaryPluckerFeature
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    Fin 2 → Fin 4 → ℝ :=
  fun i j =>
    gammaSewnMobiusApertureBoundaryAmplitude (cell j).1 *
      if i = 0 then 1 / (rate j ^ 2 - a ^ 2)
      else -2 * a * rate j / (rate j ^ 2 - a ^ 2)

/-- The six Gamma boundary weights are exactly the determinant of their weighted Cauchy feature
Gram matrix. -/
theorem gammaSewnFourRateBoundaryPairPartition_eq_gramDet
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    (∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s) =
      (standardFeatureGram
        (gammaSewnFourRateBoundaryPluckerFeature a rate cell)).det := by
  unfold gammaSewnFourRateBoundaryPairRawWeight twoBoundaryCauchyPairPluckerSq
  simp only [Fin.sum_univ_succ, fourRatePairLeft, fourRatePairRight,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  unfold standardFeatureGram
  rw [Matrix.det_fin_two]
  simp [Matrix.of_apply, Fin.sum_univ_succ,
    gammaSewnFourRateBoundaryPluckerFeature, twoBoundaryCauchyPairPlucker]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The same boundary partition is exactly HilbertMetric's degree-zero canonical Pluecker
feature volume. -/
theorem gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    (∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s) =
      canonicalFeatureVolume
        (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
        (fun _ => 1) (fun _ => 0) 1 := by
  rw [gammaSewnFourRateBoundaryPairPartition_eq_gramDet]
  have h :=
    det_scaledFeatureGram_eq_canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => 0)
      (fun _ => by norm_num) 1
  have hrows :
      scaledFeatureRows
          (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
          (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => 0) 1 =
        gammaSewnFourRateBoundaryPluckerFeature a rate cell := by
    funext i k
    simp [scaledFeatureRows]
  rw [hrows] at h
  simpa using h

/-- Under the source's nondegeneracy conditions, the weighted Cauchy feature Gram determinant is
strictly positive. -/
theorem gammaSewnFourRateBoundaryFeature_gramDet_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) :
    0 < (standardFeatureGram
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)).det := by
  rw [← gammaSewnFourRateBoundaryPairPartition_eq_gramDet]
  exact gammaSewnFourRateBoundaryPairPartition_pos ha hrate hboundary

/-- The Gamma boundary packet therefore gives a strictly positive canonical Pluecker volume. -/
theorem gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) :
    0 < canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ => 1) (fun _ => 0) 1 := by
  rw [← gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume]
  exact gammaSewnFourRateBoundaryPairPartition_pos ha hrate hboundary

/-- Canonical Pluecker normalization of one Gamma boundary-pair weight. -/
def gammaSewnFourRateCanonicalPluckerProbability
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  gammaSewnFourRateBoundaryPairRawWeight a rate cell s /
    canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ => 1) (fun _ => 0) 1

/-- The source probability packet is unconditionally the canonical Pluecker normalization. -/
theorem gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) :
    gammaSewnFourRateBoundaryPairProbability a rate cell s =
      gammaSewnFourRateCanonicalPluckerProbability a rate cell s := by
  unfold gammaSewnFourRateBoundaryPairProbability
    gammaSewnFourRateCanonicalPluckerProbability
  rw [gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume]

/-- Source nondegeneracy discharges the partition hypothesis in the four-rate curvature law and
states it directly over the canonical Pluecker probability packet. -/
theorem gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPlucker
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
      -2 * complementaryFisherMean
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) -
      2 * normalizedFinitePairDispersion
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateSelectedHeight cell) := by
  have h := gammaSewnFourRateSchurBoundaryLogCurvature_eq
    (gammaSewnFourRateBoundaryPairPartition_pos
      (cell := cell) ha hrate hboundary).ne'
  have hprob :
      gammaSewnFourRateBoundaryPairProbability a rate cell =
        gammaSewnFourRateCanonicalPluckerProbability a rate cell := by
    funext s
    exact gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized
      a rate cell s
  rw [hprob] at h
  exact h

/-- Source nondegeneracy likewise discharges the partition hypothesis for the corrected Fisher
channel, whose averaging packet is the canonical Pluecker normalization. -/
theorem gammaSewnFourRateSchurCorrectedFisher_eq_canonicalPlucker
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) :
    gammaSewnFourRateSchurCorrectedFisher a rate cell =
      complementaryFisherMean
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) := by
  have h := gammaSewnFourRateSchurCorrectedFisher_eq
    (gammaSewnFourRateBoundaryPairPartition_pos
      (cell := cell) ha hrate hboundary).ne'
  have hprob :
      gammaSewnFourRateBoundaryPairProbability a rate cell =
        gammaSewnFourRateCanonicalPluckerProbability a rate cell := by
    funext s
    exact gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized
      a rate cell s
  rw [hprob] at h
  exact h

end

end RHTower
