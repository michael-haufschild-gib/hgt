import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz
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

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Weighted two-row rational feature whose pair minors are the simplified Gamma boundary
Pluecker coordinates. -/
def gammaSewnFourRateBoundaryPluckerFeature
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    Fin 2 → Fin 4 → ℝ :=
  fun i j =>
    gammaSewnMobiusApertureBoundaryAmplitude (cell j).1 *
      if i = 0 then 1 / (rate j ^ (2 : ℕ) - a ^ (2 : ℕ))
      else -2 * a * rate j / (rate j ^ (2 : ℕ) - a ^ (2 : ℕ))

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
      z₂ / z - (z₁ / z) ^ (2 : ℕ) := by
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
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    0 < (standardFeatureGram
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)).det := by
  rw [← gammaSewnFourRateBoundaryPairPartition_eq_gramDet]
  exact gammaSewnFourRateBoundaryPairPartition_pos ha hrate hboundary

/-- The Gamma boundary packet therefore gives a strictly positive canonical Pluecker volume. -/
theorem gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
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
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
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
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    gammaSewnFourRateSchurCorrectedFisher a rate cell =
      complementaryFisherMean
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) := by
  exact gammaSewnFourRateSchurCorrectedFisher_eq_canonicalPlucker_of_volume_ne_zero
    (gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
      (cell := cell) ha hrate hboundary).ne'

/-! ## Actual four-prime logarithmic metric -/

/-- Actual prime-log rate packet, with distinctness carried by the embedding rather than exposed
as a theorem hypothesis. -/
def gammaSewnFourPrimeLogRate (prime : Fin 4 ↪ Nat.Primes) : Fin 4 → ℝ :=
  fun i => primeLogSupport (prime i)

/-- Gamma cells over an arbitrary valuation-depth profile on four distinct actual primes. -/
def gammaSewnFourPrimeCell
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    Fin 4 → Nat.Primes × ℕ :=
  fun i => (prime i, depth i)

/-- Canonical physical aperture below every rate in an actual four-prime packet.  The reciprocal
sum makes the choice symmetric in the packet and removes any minimum-selection data. -/
def gammaSewnFourPrimeLogHarmonicAperture (prime : Fin 4 ↪ Nat.Primes) : ℝ :=
  (1 + ∑ i, (gammaSewnFourPrimeLogRate prime i)⁻¹)⁻¹

/-- Every actual prime-log rate is positive. -/
theorem gammaSewnFourPrimeLogRate_pos
    (prime : Fin 4 ↪ Nat.Primes) (i : Fin 4) :
    0 < gammaSewnFourPrimeLogRate prime i :=
  primeLogSupport_pos (prime i)

/-- Distinct actual primes have distinct logarithmic rates. -/
theorem gammaSewnFourPrimeLogRate_injective (prime : Fin 4 ↪ Nat.Primes) :
    Function.Injective (gammaSewnFourPrimeLogRate prime) :=
  primeLogSupport_injective.comp prime.injective

/-- The canonical reciprocal-sum aperture is strictly positive. -/
theorem gammaSewnFourPrimeLogHarmonicAperture_pos
    (prime : Fin 4 ↪ Nat.Primes) :
    0 < gammaSewnFourPrimeLogHarmonicAperture prime := by
  unfold gammaSewnFourPrimeLogHarmonicAperture
  apply inv_pos.mpr
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ =>
      (inv_pos.mpr (gammaSewnFourPrimeLogRate_pos prime i)).le)

/-- The canonical aperture lies strictly below every actual prime-log rate. -/
theorem gammaSewnFourPrimeLogHarmonicAperture_lt_rate
    (prime : Fin 4 ↪ Nat.Primes) (i : Fin 4) :
    gammaSewnFourPrimeLogHarmonicAperture prime <
      gammaSewnFourPrimeLogRate prime i := by
  have hrate : 0 < gammaSewnFourPrimeLogRate prime i :=
    gammaSewnFourPrimeLogRate_pos prime i
  have hle : (gammaSewnFourPrimeLogRate prime i)⁻¹ ≤
      ∑ j, (gammaSewnFourPrimeLogRate prime j)⁻¹ := by
    exact Finset.single_le_sum
      (fun j _ => (inv_pos.mpr (gammaSewnFourPrimeLogRate_pos prime j)).le)
      (Finset.mem_univ i)
  have hden : 0 < 1 + ∑ j, (gammaSewnFourPrimeLogRate prime j)⁻¹ := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun j _ =>
        (inv_pos.mpr (gammaSewnFourPrimeLogRate_pos prime j)).le)
  have hlt : (gammaSewnFourPrimeLogRate prime i)⁻¹ <
      1 + ∑ j, (gammaSewnFourPrimeLogRate prime j)⁻¹ := by
    linarith
  unfold gammaSewnFourPrimeLogHarmonicAperture
  rw [← inv_inv (gammaSewnFourPrimeLogRate prime i)]
  exact (inv_lt_inv₀ hden (inv_pos.mpr hrate)).2 hlt

/-- No actual prime-log rate meets the canonical aperture boundary. -/
theorem gammaSewnFourPrimeLogHarmonicAperture_boundary_ne
    (prime : Fin 4 ↪ Nat.Primes) (i : Fin 4) :
    gammaSewnFourPrimeLogRate prime i ^ (2 : ℕ) -
        gammaSewnFourPrimeLogHarmonicAperture prime ^ (2 : ℕ) ≠ 0 := by
  apply sub_ne_zero.mpr
  exact ne_of_gt ((sq_lt_sq₀
    (gammaSewnFourPrimeLogHarmonicAperture_pos prime).le
    (gammaSewnFourPrimeLogRate_pos prime i).le).2
      (gammaSewnFourPrimeLogHarmonicAperture_lt_rate prime i))

/-- Euclidean realization of the actual four-prime rational Pluecker feature. -/
def gammaSewnFourPrimeLogBoundaryHilbertFeature
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    Fin 2 → EuclideanSpace ℝ (Fin 4) :=
  fun i => WithLp.toLp 2
    (gammaSewnFourRateBoundaryPluckerFeature
      (gammaSewnFourPrimeLogHarmonicAperture prime)
      (gammaSewnFourPrimeLogRate prime)
      (gammaSewnFourPrimeCell prime depth) i)

/-- The actual four-prime feature matrix is literally the Gram of its Euclidean realization. -/
theorem gammaSewnFourPrimeLogBoundaryStandardGram_eq_gram
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    standardFeatureGram
        (gammaSewnFourRateBoundaryPluckerFeature
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth)) =
      Matrix.gram ℝ (gammaSewnFourPrimeLogBoundaryHilbertFeature prime depth) := by
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply]
  simp only [gammaSewnFourPrimeLogBoundaryHilbertFeature,
    RCLike.inner_apply, conj_trivial]
  simp [standardFeatureGram, mul_comm]

/-- **Unconditional actual-prime Hilbert metric.**  Every four-prime embedding and every valuation
depth profile gives a strictly positive-definite Gamma boundary Gram at the canonical physical
aperture; no rate-injectivity or boundary-avoidance proposition remains. -/
theorem gammaSewnFourPrimeLogBoundaryStandardGram_posDef
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    (standardFeatureGram
      (gammaSewnFourRateBoundaryPluckerFeature
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth))).PosDef := by
  have hdet := (gammaSewnFourRateBoundaryFeature_gramDet_pos
    (cell := gammaSewnFourPrimeCell prime depth)
    (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
    (gammaSewnFourPrimeLogRate_injective prime)
    (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)).ne'
  rw [gammaSewnFourPrimeLogBoundaryStandardGram_eq_gram prime depth] at hdet ⊢
  exact (Matrix.posSemidef_gram ℝ
    (gammaSewnFourPrimeLogBoundaryHilbertFeature prime depth)).posDef_iff_det_ne_zero.mpr hdet

/-- The same actual four-prime packet has strictly positive canonical Pluecker volume. -/
theorem gammaSewnFourPrimeLogBoundaryCanonicalFeatureVolume_pos
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    0 < canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth))
      (fun _ => 1) (fun _ => 0) 1 := by
  exact gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
    (cell := gammaSewnFourPrimeCell prime depth)
    (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
    (gammaSewnFourPrimeLogRate_injective prime)
    (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)

/-- **Exact actual-prime Pluecker curvature decomposition.**  At the canonical physical aperture,
the four-prime Schur curvature is the sum of the complementary Fisher expectation and the height
dispersion, with no nonvanishing, rate-injectivity, or boundary-avoidance premise. -/
theorem gammaSewnFourPrimeLogSchurBoundaryLogCurvature_eq_canonicalPlucker
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    gammaSewnFourRateSchurBoundaryLogCurvature
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth) =
      -2 * complementaryFisherMean
        (gammaSewnFourRateCanonicalPluckerProbability
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth))
        (gammaSewnFourRateComplementaryFisher
          (gammaSewnFourPrimeCell prime depth)) -
      2 * normalizedFinitePairDispersion
        (gammaSewnFourRateCanonicalPluckerProbability
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth))
        (gammaSewnFourRateSelectedHeight
          (gammaSewnFourPrimeCell prime depth)) := by
  exact gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPlucker
    (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
    (gammaSewnFourPrimeLogRate_injective prime)
    (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)

/-- **Unconditional actual-prime curvature law.**  Every four-prime packet is strictly
log-concave at its canonical physical aperture, for every valuation-depth profile. -/
theorem gammaSewnFourPrimeLogSchurBoundaryLogCurvature_neg
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    gammaSewnFourRateSchurBoundaryLogCurvature
      (gammaSewnFourPrimeLogHarmonicAperture prime)
      (gammaSewnFourPrimeLogRate prime)
      (gammaSewnFourPrimeCell prime depth) < 0 := by
  exact gammaSewnFourRateSchurBoundaryLogCurvature_neg
    (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
    (gammaSewnFourPrimeLogRate_injective prime)
    (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)

/-- At the canonical actual-prime aperture, the corrected Schur channel is exactly the canonical
Pluecker expectation of the complementary prime Fisher clock, with no normalization premise. -/
theorem gammaSewnFourPrimeLogSchurCorrectedFisher_eq_canonicalPlucker
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    gammaSewnFourRateSchurCorrectedFisher
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth) =
      complementaryFisherMean
        (gammaSewnFourRateCanonicalPluckerProbability
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth))
        (gammaSewnFourRateComplementaryFisher
          (gammaSewnFourPrimeCell prime depth)) := by
  exact gammaSewnFourRateSchurCorrectedFisher_eq_canonicalPlucker
    (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
    (gammaSewnFourPrimeLogRate_injective prime)
    (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)

end

end RHTower
