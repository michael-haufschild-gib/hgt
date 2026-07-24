import GaloisForLFunctions.RHTower.ThetaBlackHoleQuarterCompletionStrictHankelUniversalityLaw
import GaloisForLFunctions.RHTower.ThetaCuspCassiniLikelihoodRatioReciprocalMarkovNoGoUniversalityLaw

/-!
# Theta-cusp likelihood representation-selective quarter-completion universality

The fixed theta-cusp likelihood carrier supports an exact nonlinear Cassini response, but its raw
reciprocal-square-gap pushforward cannot represent the whole response by a compact Markov
transform. Matching its source coordinate with the Gamma-quarter completion exposes the positive
survivor: the same likelihood moment hierarchy is strictly Hankel and completes to a concrete
strict prime-archimedean ray whose adjoining-cone closure is exactly RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- One-carrier certificate joining exact nonlinear Cassini readout, raw reciprocal-Markov
failure, strict source moments, and the canonical quarter-completed RH classifier. -/
structure ThetaCuspLikelihoodRepresentationSelectiveQuarterCompletionCertificate
    (x : ℝ) : Prop where
  positiveDensity :
    0 < thetaCuspCassiniLikelihoodBaseDensity x
  sourceStrictHankel :
    ∀ q : ℕ,
      (HTGeometry.momentHankelMatrix
        (thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate x)) q).PosDef
  nonlinearCassini :
    ∀ t : ℝ, 0 < t → t < 1 →
      thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2) =
          ((thetaCuspCassiniLikelihoodFlux t /
            (t * thetaCuspCassiniLikelihoodPartition t) : ℝ) : ℂ) ∧
        0 < (thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2)).re ∧
        (thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2)).im = 0
  reciprocalMarkovNoGo :
    ¬ ThetaCuspCassiniReciprocalLikelihoodBoundaryIdentity
  quarterCompletion :
    ∀ (scaleLog : ℂ) (m : ℕ),
      thetaBlackHoleQuarterCompletedMoment
          (thetaCuspLikelihoodCoordinate x) m =
        (4 : ℝ) ^ (m + 2) *
            HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m +
          thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate x) m
  completedStrictHankel :
    ∀ n : ℕ,
      (HTGeometry.momentHankelMatrix
        (thetaBlackHoleQuarterCompletedMoment
          (thetaCuspLikelihoodCoordinate x)) n).PosDef
  rhClassifier :
    RiemannHypothesis ↔
      PrimeArchStrictHankelRayAdjoiningCone
        (thetaBlackHoleQuarterCompletedMoment
          (thetaCuspLikelihoodCoordinate x))

/-- **Theta-cusp representation-selective quarter-completion law.** At every positive source
point, the fixed likelihood carrier has an exact nonlinear Cassini readout but no raw reciprocal
Markov representation; its strict moment hierarchy survives canonical Gamma-quarter completion
to a concrete exact RH adjoining-cone classifier. -/
theorem thetaCuspLikelihood_representationSelectiveQuarterCompletionUniversality
    (x : ℝ) (hx : 0 < x) :
    ThetaCuspLikelihoodRepresentationSelectiveQuarterCompletionCertificate x := by
  have hsource :=
    thetaCuspCassiniLikelihoodBaseDensity_pos_and_spectralHankel (x := x) hx
  have hratio :=
    thetaCuspCassiniLikelihoodRatio_reciprocalMarkovNoGo_universality
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx.le
  refine ⟨hsource.1, hsource.2, hratio.1, hratio.2, ?_, ?_, ?_⟩
  · intro scaleLog m
    exact thetaBlackHoleQuarterCompletedMoment_eq scaleLog
      (thetaCuspLikelihoodCoordinate x) m
  · exact thetaBlackHoleQuarterCompletedMoment_hankel_posDef hB
  · exact
      riemannHypothesis_iff_primeArch_adjoin_thetaBlackHoleQuarterCompletedRay hB

end

end RHTower
