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

/-- **Canonical Pluecker--Jordan curvature transition.**  For a nondegenerate four-prime packet
at common valuation depth `e`, Schur log-curvature crosses `-8/3` times the canonical Pluecker
sewing mass exactly at the source-computable Rees scale `sqrt(F / D)`. -/
theorem gammaSewnFourRatePluckerJordan_curvature_transition_iff
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes} (e : ℕ)
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0)
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
  let cell := gammaSewnFourRateCommonDepthCell prime e
  have hpartition :
      0 < ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s :=
    gammaSewnFourRateBoundaryPairPartition_pos
      (cell := cell) ha hrate hboundary
  have hcurvature := gammaSewnFourRateSchurBoundaryLogCurvature_eq hpartition.ne'
  have hcorrected := gammaSewnFourRateSchurCorrectedFisher_eq hpartition.ne'
  have hsewing :=
    gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher
      hpartition.ne'
  have htransition :=
    gammaSewnFourRateCommonDepth_correctedFisher_lt_dispersion_iff
      e ha hrate hboundary hprime
  constructor
  · intro hcross
    apply htransition.mp
    nlinarith
  · intro hscale
    have hdom := htransition.mpr hscale
    nlinarith

end

end RHTower
