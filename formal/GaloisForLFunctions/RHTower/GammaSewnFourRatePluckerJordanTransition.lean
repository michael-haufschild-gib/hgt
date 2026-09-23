import GaloisForLFunctions.RHTower.GammaSewnFourRateHeightLocalizedDomination
import GaloisForLFunctions.RHTower.GammaSewnFourRatePluckerConnector
import GaloisForLFunctions.RHTower.GammaSewnFourRateSynchronizedEulerFisher

/-!
# Canonical Pluecker--Jordan transition for the four-rate Gamma seam

The four-rate boundary minors carry two descriptions which were previously disconnected.
`GammaSewnFourRatePluckerConnector` identifies their probability packet with the canonical
Pluecker normalization of a Gram feature.  Independently, the synchronized Euler--Fisher
calculation splits the complementary Fisher channel into a negative height finite part and a
positive sewing mass in the universal ratio `-1 : 3`.

Joining those descriptions makes the sewing mass a canonical Pluecker statistic.  The Rees-depth
transition can then be read directly from Schur log-curvature: the curvature crosses `-8/3` times
the Pluecker sewing mass exactly when the valuation half-depth crosses the source ratio
`sqrt(F / D)`.

This is an unconditional finite-source law.  It does not transport the boundary probability to
the physical depth-dependent Euler amplitude and makes no RH claim.
-/

open scoped BigOperators
open GaloisForLFunctions.HilbertMetric

namespace RHTower

noncomputable section

/-- Positive sewing channel averaged with the canonical Pluecker probability of the four-rate
boundary feature. -/
def gammaSewnFourRateCanonicalPluckerSewingMass
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  complementaryFisherMean
    (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
    (gammaSewnFourRateComplementarySewingBoundaryFisher cell)

/-- The source probability and canonical Pluecker probability give the same sewing mass. -/
theorem gammaSewnFourRateCanonicalPluckerSewingMass_eq_boundarySewingMass
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaSewnFourRateCanonicalPluckerSewingMass a rate cell =
      gammaSewnFourRateBoundaryComplementarySewingMass a rate cell := by
  unfold gammaSewnFourRateCanonicalPluckerSewingMass
    gammaSewnFourRateBoundaryComplementarySewingMass complementaryFisherMean
  apply Finset.sum_congr rfl
  intro s _hs
  rw [gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized]

/-- **Canonical Pluecker--Jordan ratio.**  The positive synchronized sewing mass is exactly
`3/2` of the cumulant-corrected Schur--Fisher channel.  Thus the projective signed decomposition
`height : sewing : residual = -1 : 3 : 2` is intrinsic to the canonical Pluecker packet. -/
theorem gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition :
      ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    gammaSewnFourRateCanonicalPluckerSewingMass a rate cell =
      (3 / 2 : ℝ) * gammaSewnFourRateSchurCorrectedFisher a rate cell := by
  rw [gammaSewnFourRateCanonicalPluckerSewingMass_eq_boundarySewingMass,
    gammaSewnFourRateBoundaryComplementarySewingMass_eq_three_halves_fisher,
    gammaSewnFourRateSchurCorrectedFisher_eq hpartition]

/-- Canonical-volume nonvanishing discharges the raw partition premise in the Pluecker--Jordan
ratio. -/
theorem gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher_of_volume_ne_zero
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hvolume : canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ => 1) (fun _ => 0) 1 ≠ 0) :
    gammaSewnFourRateCanonicalPluckerSewingMass a rate cell =
      (3 / 2 : ℝ) * gammaSewnFourRateSchurCorrectedFisher a rate cell := by
  apply gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher
  rw [gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume]
  exact hvolume

/-- Source nondegeneracy makes the canonical Pluecker--Jordan ratio unconditional at the
normalization interface. -/
theorem gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher_of_nondegenerate
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    gammaSewnFourRateCanonicalPluckerSewingMass a rate cell =
      (3 / 2 : ℝ) * gammaSewnFourRateSchurCorrectedFisher a rate cell := by
  exact
    gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher_of_volume_ne_zero
      (gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
        (cell := cell) ha hrate hboundary).ne'

/-- **Universal canonical Pluecker--Jordan curvature law.**  Once the Hilbert-feature volume is
nonzero, Schur curvature is the sum of `-4/3` times canonical sewing mass and the selected-height
dispersion penalty.  This removes the intermediate corrected-Fisher and raw-partition interfaces. -/
theorem gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPluckerJordan_of_volume_ne_zero
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hvolume : canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ => 1) (fun _ => 0) 1 ≠ 0) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
      -(4 / 3 : ℝ) * gammaSewnFourRateCanonicalPluckerSewingMass a rate cell -
      2 * normalizedFinitePairDispersion
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateSelectedHeight cell) := by
  have hpartition :
      (∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s) ≠ 0 := by
    rw [gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume]
    exact hvolume
  have hcurvature := gammaSewnFourRateSchurBoundaryLogCurvature_eq hpartition
  have hcorrected := gammaSewnFourRateSchurCorrectedFisher_eq hpartition
  have hprob :
      gammaSewnFourRateBoundaryPairProbability a rate cell =
        gammaSewnFourRateCanonicalPluckerProbability a rate cell := by
    funext s
    exact gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized
      a rate cell s
  rw [hprob] at hcurvature hcorrected
  have hsewing :=
    gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher_of_volume_ne_zero
      hvolume
  nlinarith

/-- Source nondegeneracy supplies the Hilbert-feature volume premise in the universal canonical
Pluecker--Jordan curvature law. -/
theorem gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPluckerJordan
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
      -(4 / 3 : ℝ) * gammaSewnFourRateCanonicalPluckerSewingMass a rate cell -
      2 * normalizedFinitePairDispersion
        (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
        (gammaSewnFourRateSelectedHeight cell) := by
  exact gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPluckerJordan_of_volume_ne_zero
    (gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
      (cell := cell) ha hrate hboundary).ne'

/-- **Canonical Pluecker--Jordan curvature transition.**  For a nondegenerate four-prime packet
at common valuation depth `e`, Schur log-curvature crosses `-8/3` times the canonical Pluecker
sewing mass exactly at the source-computable Rees scale `sqrt(F / D)`. -/
theorem gammaSewnFourRatePluckerJordan_curvature_transition_iff
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes} (e : ℕ)
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0)
    (hprime : Function.Injective prime) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate
          (gammaSewnFourRateCommonDepthCell prime e) <
        -(8 / 3 : ℝ) *
          gammaSewnFourRateCanonicalPluckerSewingMass a rate
            (gammaSewnFourRateCommonDepthCell prime e) ↔
      Real.sqrt
          (gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime /
            gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime) <
        (e : ℝ) + 1 / 2 := by
  have hcurvature :=
    gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPluckerJordan
      (cell := gammaSewnFourRateCommonDepthCell prime e) ha hrate hboundary
  have hsewing :=
    gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher_of_nondegenerate
      (cell := gammaSewnFourRateCommonDepthCell prime e) ha hrate hboundary
  have hprob :
      gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateCommonDepthCell prime e) =
        gammaSewnFourRateCanonicalPluckerProbability a rate
          (gammaSewnFourRateCommonDepthCell prime e) := by
    funext s
    exact gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized
      a rate (gammaSewnFourRateCommonDepthCell prime e) s
  have htransition :=
    gammaSewnFourRateCommonDepth_correctedFisher_lt_dispersion_iff
      e ha hrate hboundary hprime
  rw [hprob] at htransition
  constructor
  · intro hcross
    apply htransition.mp
    nlinarith
  · intro hscale
    have hdom := htransition.mpr hscale
    nlinarith

/-! ## Unconditional actual-prime Pluecker--Jordan package -/

/-- For four distinct actual primes at the canonical physical aperture, the canonical Pluecker
sewing mass is exactly `3/2` of corrected Fisher charge for every valuation-depth profile. -/
theorem gammaSewnFourPrimeLogCanonicalPluckerSewingMass_eq_three_halves_correctedFisher
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    gammaSewnFourRateCanonicalPluckerSewingMass
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth) =
      (3 / 2 : ℝ) * gammaSewnFourRateSchurCorrectedFisher
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth) := by
  exact
    gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher_of_nondegenerate
      (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
      (gammaSewnFourPrimeLogRate_injective prime)
      (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)

/-- Exact Pluecker--Jordan curvature decomposition for four distinct actual primes, with source
nondegeneracy, rate injectivity, and boundary avoidance discharged by the prime embedding and the
canonical physical aperture. -/
theorem gammaSewnFourPrimeLogSchurBoundaryLogCurvature_eq_canonicalPluckerJordan
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    gammaSewnFourRateSchurBoundaryLogCurvature
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth) =
      -(4 / 3 : ℝ) * gammaSewnFourRateCanonicalPluckerSewingMass
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth) -
      2 * normalizedFinitePairDispersion
        (gammaSewnFourRateCanonicalPluckerProbability
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth))
        (gammaSewnFourRateSelectedHeight
          (gammaSewnFourPrimeCell prime depth)) := by
  exact gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPluckerJordan
    (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
    (gammaSewnFourPrimeLogRate_injective prime)
    (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)

/-- **Actual-prime Pluecker--Jordan transition.**  For four distinct primes, curvature crosses
`-8/3` times canonical sewing mass exactly when common valuation half-depth crosses the explicit
prime-log Rees scale.  No auxiliary nondegeneracy proposition remains. -/
theorem gammaSewnFourPrimeLogPluckerJordan_curvature_transition_iff
    (prime : Fin 4 ↪ Nat.Primes) (e : ℕ) :
    gammaSewnFourRateSchurBoundaryLogCurvature
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourRateCommonDepthCell prime e) <
        -(8 / 3 : ℝ) * gammaSewnFourRateCanonicalPluckerSewingMass
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourRateCommonDepthCell prime e) ↔
      Real.sqrt
          (gammaSewnFourRateBoundaryComplementaryFisherMass
              (gammaSewnFourPrimeLogHarmonicAperture prime)
              (gammaSewnFourPrimeLogRate prime) prime /
            gammaSewnFourRateBoundaryPrimeLogDispersion
              (gammaSewnFourPrimeLogHarmonicAperture prime)
              (gammaSewnFourPrimeLogRate prime) prime) <
        (e : ℝ) + 1 / 2 := by
  exact gammaSewnFourRatePluckerJordan_curvature_transition_iff e
    (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
    (gammaSewnFourPrimeLogRate_injective prime)
    (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)
    prime.injective

/-- Every four-prime packet eventually enters the strict Pluecker--Jordan curvature regime at a
common valuation depth.  This packages the Archimedean depth witness with all actual-prime source
conditions discharged. -/
theorem exists_gammaSewnFourPrimeLogPluckerJordan_curvature_crossing
    (prime : Fin 4 ↪ Nat.Primes) :
    ∃ e : ℕ,
      gammaSewnFourRateSchurBoundaryLogCurvature
            (gammaSewnFourPrimeLogHarmonicAperture prime)
            (gammaSewnFourPrimeLogRate prime)
            (gammaSewnFourRateCommonDepthCell prime e) <
          -(8 / 3 : ℝ) * gammaSewnFourRateCanonicalPluckerSewingMass
            (gammaSewnFourPrimeLogHarmonicAperture prime)
            (gammaSewnFourPrimeLogRate prime)
            (gammaSewnFourRateCommonDepthCell prime e) := by
  obtain ⟨e, he⟩ := exists_nat_gt
    (Real.sqrt
      (gammaSewnFourRateBoundaryComplementaryFisherMass
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime) prime /
        gammaSewnFourRateBoundaryPrimeLogDispersion
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime) prime))
  refine ⟨e, (gammaSewnFourPrimeLogPluckerJordan_curvature_transition_iff prime e).2 ?_⟩
  exact he.trans (by norm_num)

/-- There is one common valuation depth where the smaller literal-Euler height dispersion already
dominates corrected Fisher charge and, consequently, Schur curvature lies strictly beyond the
canonical Pluecker--Jordan threshold.  This joins the Euler calibration and curvature-transition
branches with no source proposition left exposed. -/
theorem exists_gammaSewnFourPrimeLogEulerDominatedPluckerJordan_curvature_crossing
    (prime : Fin 4 ↪ Nat.Primes) :
    ∃ e : ℕ,
      gammaSewnFourRateSchurCorrectedFisher
            (gammaSewnFourPrimeLogHarmonicAperture prime)
            (gammaSewnFourPrimeLogRate prime)
            (gammaSewnFourRateCommonDepthCell prime e) <
          normalizedFinitePairDispersion
            (gammaSewnFourRateBoundaryPairProbability
              (gammaSewnFourPrimeLogHarmonicAperture prime)
              (gammaSewnFourPrimeLogRate prime)
              (gammaSewnFourRateCommonDepthCell prime e))
            (gammaSewnFourRateSelectedEulerHeight prime e) ∧
        gammaSewnFourRateSchurBoundaryLogCurvature
              (gammaSewnFourPrimeLogHarmonicAperture prime)
              (gammaSewnFourPrimeLogRate prime)
              (gammaSewnFourRateCommonDepthCell prime e) <
            -(8 / 3 : ℝ) * gammaSewnFourRateCanonicalPluckerSewingMass
              (gammaSewnFourPrimeLogHarmonicAperture prime)
              (gammaSewnFourPrimeLogRate prime)
              (gammaSewnFourRateCommonDepthCell prime e) := by
  obtain ⟨e, heuler⟩ :=
    exists_gammaSewnFourRateCommonDepth_correctedFisher_lt_eulerDispersion
      (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
      (gammaSewnFourPrimeLogRate_injective prime)
      (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)
      prime.injective
  refine ⟨e, heuler, ?_⟩
  apply (gammaSewnFourPrimeLogPluckerJordan_curvature_transition_iff prime e).2
  have heulerScale :=
    (gammaSewnFourRateCommonDepth_correctedFisher_lt_eulerDispersion_iff e
      (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
      (gammaSewnFourPrimeLogRate_injective prime)
      (gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime)
      prime.injective).1 heuler
  have he_nonneg : 0 ≤ (e : ℝ) := by positivity
  nlinarith

end

end RHTower
