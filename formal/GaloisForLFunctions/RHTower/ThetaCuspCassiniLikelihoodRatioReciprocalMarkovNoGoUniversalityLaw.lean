import GaloisForLFunctions.RHTower.ThetaCuspCassiniHyperbolicSourceLaw
import GaloisForLFunctions.RHTower.ThetaCuspCassiniMarkovBoundaryTransport
import GaloisForLFunctions.RHTower.ThetaCuspModularColdCurvatureUniversalityLaw

/-!
# Theta-cusp Cassini likelihood-ratio / reciprocal-Markov no-go universality law

The explicit aperture-independent theta likelihood carrier has two sharply different
representations.  Its hyperbolic flux-to-partition ratio is exactly the genuine Cassini response
at every positive aperture.  Its raw reciprocal-square-gap pushforward, despite finite compact
positive support, cannot represent the entire boundary response as a compact Markov transform
because analytic transport exposes an incompatible total mass.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Theta-cusp Cassini likelihood-ratio / reciprocal-Markov no-go universality law.**  The
source-built likelihood carrier gives the exact positive-real Cassini response through a nonlinear
ratio at every aperture `0 < t < 1`, while the raw reciprocal pushforward of the same carrier
cannot give a global linear Markov representation. -/
theorem thetaCuspCassiniLikelihoodRatio_reciprocalMarkovNoGo_universality :
    (∀ t : ℝ, 0 < t → t < 1 →
      thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2) =
          ((thetaCuspCassiniLikelihoodFlux t /
            (t * thetaCuspCassiniLikelihoodPartition t) : ℝ) : ℂ) ∧
        0 < (thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2)).re ∧
        (thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2)).im = 0) ∧
      ¬ ThetaCuspCassiniReciprocalLikelihoodBoundaryIdentity := by
  refine ⟨?_, not_thetaCuspCassiniReciprocalLikelihoodBoundaryIdentity⟩
  intro t ht0 ht1
  exact ⟨
    thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_likelihoodCarrierRatio ht0 ht1,
    thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_re_pos ht0 ht1,
    thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_im_eq_zero ht0 ht1⟩

/-- **Theta-cusp Cassini likelihood-carrier full-phase atlas universality law.**  The same fixed
likelihood carrier has positive density and strict Hankel blocks at every source point, gives the
exact positive-real Cassini response, fails the raw reciprocal Markov identity, and places every
modular cold-curvature coefficient strictly inside its order-two fluctuation cone. -/
theorem thetaCuspCassiniLikelihoodCarrier_fullPhaseAtlas_universality :
    ((∀ t : ℝ, 0 < t → t < 1 →
      thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2) =
          ((thetaCuspCassiniLikelihoodFlux t /
            (t * thetaCuspCassiniLikelihoodPartition t) : ℝ) : ℂ) ∧
        0 < (thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2)).re ∧
        (thetaCuspCassiniInwardCoordinateResponse (1 - t ^ 2)).im = 0) ∧
      ¬ ThetaCuspCassiniReciprocalLikelihoodBoundaryIdentity) ∧
    (∀ x : ℝ, 0 < x →
      0 < thetaCuspCassiniLikelihoodBaseDensity x ∧
        ∀ q : ℕ,
          (HTGeometry.momentHankelMatrix
            (thetaCuspHigherLikelihoodSpectralMoment
              (thetaCuspLikelihoodCoordinate x)) q).PosDef) ∧
    ∀ j : ℕ,
      0 < thetaCuspModularColdCurvatureFactor j ∧
      0 < thetaCuspModularColdSignedSlopeCoefficient j ∧
      thetaCuspModularColdSignedSlopeCoefficient j ^ 2 *
            (1 + thetaCuspHigherLikelihoodSpectralMoment
              (thetaCuspLikelihoodCoordinate 0) 0) ^ 2 <
        (2 * Real.pi) ^ 2 * thetaCuspModularColdCurvatureFactor j ^ 2 *
          thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate 0) 0 *
          thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate 0) 2 := by
  refine ⟨thetaCuspCassiniLikelihoodRatio_reciprocalMarkovNoGo_universality,
    ?_, ?_⟩
  · intro x hx
    exact thetaCuspCassiniLikelihoodBaseDensity_pos_and_spectralHankel hx
  · intro j
    exact ⟨thetaCuspModularColdCurvatureFactor_pos j,
      thetaCuspModularColdSignedSlopeCoefficient_pos j,
      thetaCuspModularColdSignedSlope_strictFluctuation j⟩

end

end RHTower
