import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodRepresentationSelectiveQuarterCompletionUniversalityLaw
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSourceDomainOrientation
import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity

/-!
# Theta likelihood exact-source-domain oriented quarter-completion universality

The likelihood coordinate is positive on an exact source domain beginning at a negative boundary.
Global positivity of the full theta source removes the stronger `x > 0` premise from the existing
representation-selective quarter-completion law.  On this enlarged exact domain, every prime
boundary and self-swap mass-shell phase also has strict negative current.
-/

open Complex

namespace RHTower

noncomputable section

/-- The likelihood density/source identity needs only positivity of the likelihood coordinate,
not positivity of the source point. -/
theorem thetaCuspCassiniLikelihoodBaseDensity_eq_two_mul_fullSource_of_coordinate_pos
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspCassiniLikelihoodBaseDensity x =
      2 * thetaCuspFullSource x := by
  rw [thetaCuspCassiniLikelihoodBaseDensity,
    thetaCuspCassiniLikelihoodFactor,
    thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos hB]
  ring

/-- The likelihood density and all its Hankel matrices are strict on the exact coordinate-positive
source domain, including its negative-source part. -/
theorem thetaCuspCassiniLikelihoodBaseDensity_pos_and_spectralHankel_of_boundaryPoint_lt
    {x : ℝ} (hx : thetaCuspLikelihoodBoundaryPoint < x) :
    0 < thetaCuspCassiniLikelihoodBaseDensity x ∧
      ∀ q : ℕ,
        (HTGeometry.momentHankelMatrix
          (thetaCuspHigherLikelihoodSpectralMoment
            (thetaCuspLikelihoodCoordinate x)) q).PosDef := by
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    (thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt x).2 hx
  constructor
  · rw [
      thetaCuspCassiniLikelihoodBaseDensity_eq_two_mul_fullSource_of_coordinate_pos hB]
    exact mul_pos (by norm_num) (thetaCuspFullSource_pos_all x)
  · exact (thetaCuspHigherLikelihoodSpectralMasterLaw hB).2

/-- The full representation-selective quarter-completion certificate extends from `x > 0` to the
exact positive-likelihood source domain. -/
theorem thetaCuspLikelihood_representationSelectiveQuarterCompletion_of_boundaryPoint_lt
    (x : ℝ) (hx : thetaCuspLikelihoodBoundaryPoint < x) :
    ThetaCuspLikelihoodRepresentationSelectiveQuarterCompletionCertificate x := by
  have hsource :=
    thetaCuspCassiniLikelihoodBaseDensity_pos_and_spectralHankel_of_boundaryPoint_lt hx
  have hratio :=
    thetaCuspCassiniLikelihoodRatio_reciprocalMarkovNoGo_universality
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    (thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt x).2 hx
  refine ⟨hsource.1, hsource.2, hratio.1, hratio.2, ?_, ?_, ?_⟩
  · intro scaleLog m
    exact thetaBlackHoleQuarterCompletedMoment_eq scaleLog
      (thetaCuspLikelihoodCoordinate x) m
  · exact thetaBlackHoleQuarterCompletedMoment_hankel_posDef hB
  · exact
      riemannHypothesis_iff_primeArch_adjoin_thetaBlackHoleQuarterCompletedRay hB

/-- Exact-domain certificate joining representation selection, quarter completion, RH
classification, and strict prime-face orientation. -/
structure ThetaLikelihoodExactSourceDomainOrientedQuarterCompletionCertificate
    (x : ℝ) : Prop extends
      ThetaCuspLikelihoodRepresentationSelectiveQuarterCompletionCertificate x where
  exactSourceDomain :
    thetaCuspLikelihoodBoundaryPoint < x ↔
      0 < thetaCuspLikelihoodCoordinate x
  boundaryFaceOrientation :
    ∀ {k : ℕ}, k.Prime → ∀ {z : ℂ}, 0 < z.im →
      (thetaCuspSourceBoundaryFaceMassShellPhaseDerivative k x z *
        (starRingEnd ℂ)
          (thetaCuspSourceBoundaryFaceMassShellPhase k x z)).im < 0
  selfSwapOrientation :
    ∀ {k : ℕ}, k.Prime → ∀ {z : ℂ}, 0 < z.im →
      (thetaCuspSourceSwapMassShellPhaseDerivative k x x z *
        (starRingEnd ℂ)
          (thetaCuspSourceSwapMassShellPhase k x x z)).im < 0

/-- **Theta likelihood exact-source-domain oriented quarter-completion universality law.** -/
theorem thetaLikelihood_exactSourceDomain_orientedQuarterCompletionUniversality
    (x : ℝ) (hx : thetaCuspLikelihoodBoundaryPoint < x) :
    ThetaLikelihoodExactSourceDomainOrientedQuarterCompletionCertificate x := by
  refine
    ⟨thetaCuspLikelihood_representationSelectiveQuarterCompletion_of_boundaryPoint_lt x hx,
      (thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt x).symm,
      ?_, ?_⟩
  · intro k hk z hz
    exact
      thetaCuspSourceBoundaryFacePrimeMassShellPhase_current_lt_zero_of_boundaryPoint_lt
        hk hx hz
  · intro k hk z hz
    exact
      thetaCuspSourceSwapPrimeMassShellPhase_current_lt_zero_of_boundaryPoint_lt
        hk hx hx hz

end

end RHTower
