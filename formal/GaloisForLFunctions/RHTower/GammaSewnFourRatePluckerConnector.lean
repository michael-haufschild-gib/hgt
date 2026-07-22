import GaloisForLFunctions.RHTower.GammaSewnFourRateSchurFisherCurvature
import GaloisForLFunctions.HilbertMetric.GradedPartition
import GaloisForLFunctions.HilbertMetric.GramCurvaturePersistence

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

/-- A scalar jet represented as a one-dimensional matrix jet. -/
def boundaryPairPartitionScalarJetMatrix (z : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => z

/-- One-dimensional Gram log-curvature is exactly scalar logarithmic curvature.  The identity is
unconditional because both matrix and scalar inverses use the same zero convention. -/
theorem gramLogCurvatureJet_boundaryPairPartitionScalarJetMatrix
    (z z₁ z₂ : ℝ) :
    gramLogCurvatureJet
        (boundaryPairPartitionScalarJetMatrix z)
        (boundaryPairPartitionScalarJetMatrix z₁)
        (boundaryPairPartitionScalarJetMatrix z₂) =
      z₂ / z - (z₁ / z) ^ 2 := by
  simp [gramLogCurvatureJet, boundaryPairPartitionScalarJetMatrix,
    Matrix.trace, Matrix.mul_apply]
  ring

/-- The scalar boundary-partition 2-jet is literally a one-dimensional HilbertMetric Gram
log-curvature jet. -/
theorem boundaryPairPartitionLogCurvatureFromJets_eq_gramLogCurvatureJet
    {β : Type*} [Fintype β]
    (rawWeight selectedHeight selectedFisher : β → ℝ) :
    boundaryPairPartitionLogCurvatureFromJets
        rawWeight selectedHeight selectedFisher =
      gramLogCurvatureJet
        (boundaryPairPartitionScalarJetMatrix
          (boundaryPairPartitionJetZero rawWeight))
        (boundaryPairPartitionScalarJetMatrix
          (boundaryPairPartitionJetOne rawWeight selectedHeight))
        (boundaryPairPartitionScalarJetMatrix
          (boundaryPairPartitionJetTwo rawWeight selectedHeight selectedFisher)) := by
  rw [gramLogCurvatureJet_boundaryPairPartitionScalarJetMatrix]
  rfl

/-- The generic four-rate Schur boundary jet is the total numerator Fisher curvature minus its
one-dimensional denominator Gram log-curvature. -/
theorem fourRateSchurBoundaryLogCurvatureFromJets_eq_gramLogCurvatureJet
    {β : Type*} [Fintype β]
    (rawWeight selectedHeight selectedFisher : β → ℝ) (totalFisher : ℝ) :
    fourRateSchurBoundaryLogCurvatureFromJets
        rawWeight selectedHeight selectedFisher totalFisher =
      -2 * totalFisher -
        gramLogCurvatureJet
          (boundaryPairPartitionScalarJetMatrix
            (boundaryPairPartitionJetZero rawWeight))
          (boundaryPairPartitionScalarJetMatrix
            (boundaryPairPartitionJetOne rawWeight selectedHeight))
          (boundaryPairPartitionScalarJetMatrix
            (boundaryPairPartitionJetTwo rawWeight selectedHeight selectedFisher)) := by
  unfold fourRateSchurBoundaryLogCurvatureFromJets
  rw [boundaryPairPartitionLogCurvatureFromJets_eq_gramLogCurvatureJet]

/-- The actual Gamma-sewn four-rate curvature is therefore an exact HilbertMetric determinant-jet
curvature connector, with the source Fisher numerator retained explicitly. -/
theorem gammaSewnFourRateSchurBoundaryLogCurvature_eq_gramLogCurvatureJet
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
      -2 * gammaSewnFourRateTotalFisher cell -
        gramLogCurvatureJet
          (boundaryPairPartitionScalarJetMatrix
            (boundaryPairPartitionJetZero
              (gammaSewnFourRateBoundaryPairRawWeight a rate cell)))
          (boundaryPairPartitionScalarJetMatrix
            (boundaryPairPartitionJetOne
              (gammaSewnFourRateBoundaryPairRawWeight a rate cell)
              (gammaSewnFourRateSelectedHeight cell)))
          (boundaryPairPartitionScalarJetMatrix
            (boundaryPairPartitionJetTwo
              (gammaSewnFourRateBoundaryPairRawWeight a rate cell)
              (gammaSewnFourRateSelectedHeight cell)
              (gammaSewnFourRateSelectedFisher cell))) := by
  unfold gammaSewnFourRateSchurBoundaryLogCurvature
  rw [fourRateSchurBoundaryLogCurvatureFromJets_eq_gramLogCurvatureJet]

/-- The six Gamma boundary weights are exactly the determinant of their weighted rational
Pluecker-feature Gram matrix. -/
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

/-- Under the source's nondegeneracy conditions, the weighted rational Pluecker-feature Gram
determinant is strictly positive. -/
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

/-- Nonvanishing of the canonical Pluecker volume is the exact geometric normalization condition
needed by the four-rate curvature law. -/
theorem gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPlucker_of_volume_ne_zero
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hvolume : canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ => 1) (fun _ => 0) 1 ≠ 0) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
      -2 * complementaryFisherMean
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) -
      2 * normalizedFinitePairDispersion
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateSelectedHeight cell) := by
  have hpartition :
      (∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s) ≠ 0 := by
    rw [gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume]
    exact hvolume
  have h := gammaSewnFourRateSchurBoundaryLogCurvature_eq hpartition
  have hprob :
      gammaSewnFourRateBoundaryPairProbability a rate cell =
        gammaSewnFourRateCanonicalPluckerProbability a rate cell := by
    funext s
    exact gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized
      a rate cell s
  rw [hprob] at h
  exact h

/-- Source nondegeneracy discharges canonical-volume nonvanishing in the four-rate curvature law. -/
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
  exact gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPlucker_of_volume_ne_zero
    (gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
      (cell := cell) ha hrate hboundary).ne'

/-- Nonvanishing canonical Pluecker volume likewise suffices for the corrected Fisher channel. -/
theorem gammaSewnFourRateSchurCorrectedFisher_eq_canonicalPlucker_of_volume_ne_zero
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hvolume : canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ => 1) (fun _ => 0) 1 ≠ 0) :
    gammaSewnFourRateSchurCorrectedFisher a rate cell =
      complementaryFisherMean
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) := by
  have hpartition :
      (∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s) ≠ 0 := by
    rw [gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume]
    exact hvolume
  have h := gammaSewnFourRateSchurCorrectedFisher_eq hpartition
  have hprob :
      gammaSewnFourRateBoundaryPairProbability a rate cell =
        gammaSewnFourRateCanonicalPluckerProbability a rate cell := by
    funext s
    exact gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized
      a rate cell s
  rw [hprob] at h
  exact h

/-- Source nondegeneracy discharges canonical-volume nonvanishing for corrected Fisher. -/
theorem gammaSewnFourRateSchurCorrectedFisher_eq_canonicalPlucker
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) :
    gammaSewnFourRateSchurCorrectedFisher a rate cell =
      complementaryFisherMean
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) := by
  exact gammaSewnFourRateSchurCorrectedFisher_eq_canonicalPlucker_of_volume_ne_zero
    (gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
      (cell := cell) ha hrate hboundary).ne'

end

end RHTower
