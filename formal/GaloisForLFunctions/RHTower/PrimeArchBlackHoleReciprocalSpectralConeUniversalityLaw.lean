import GaloisForLFunctions.HTGeometry.BlackHoleReciprocalSpectralConeLaw
import GaloisForLFunctions.RHTower.PrimeArchFiniteStateDimension

/-!
# Prime--archimedean / black-hole / reciprocal spectral-cone universality

The normalized black-hole far-zone jet and reciprocal continuum clock generate an unconditional
strict Hankel cone.  The normalized prime--archimedean moment ray is strict in every degree exactly
under RH.  Adjoining that ray therefore turns the two-source physical cone into an exact
three-source cone criterion for RH: every nonzero nonnegative mixture is positive definite at
every finite depth if and only if RH holds.
-/

namespace RHTower

noncomputable section

/-- Nonnegative linear mixture of the black-hole Gamma clock, reciprocal continuum clock, and
normalized prime--archimedean source clock. -/
def primeArchBlackHoleReciprocalMixedClock
    (scaleLog : ℂ) (alpha beta gamma : ℝ) (n : ℕ) : ℝ :=
  alpha * HTGeometry.normalizedBlackHoleFarZoneJet scaleLog n +
    beta * HTGeometry.reciprocalTailClock n + gamma * normalizedPrimeArchMoment n

/-- Hankel formation is exactly linear on the three-ray cone. -/
theorem momentHankelMatrix_primeArchBlackHoleReciprocalMixedClock
    (scaleLog : ℂ) (alpha beta gamma : ℝ) (n : ℕ) :
    HTGeometry.momentHankelMatrix
        (primeArchBlackHoleReciprocalMixedClock scaleLog alpha beta gamma) n =
      alpha • HTGeometry.momentHankelMatrix
          (HTGeometry.normalizedBlackHoleFarZoneJet scaleLog) n +
        beta • HTGeometry.momentHankelMatrix HTGeometry.reciprocalTailClock n +
          gamma • HTGeometry.momentHankelMatrix normalizedPrimeArchMoment n := by
  ext i j
  simp [HTGeometry.momentHankelMatrix, primeArchBlackHoleReciprocalMixedClock]

/-- Under RH every nonzero nonnegative three-ray mixture is strictly Hankel positive at every
finite depth. -/
theorem primeArchBlackHoleReciprocalMixedClock_hankel_posDef_of_riemannHypothesis
    (hRH : RiemannHypothesis) (scaleLog : ℂ) {alpha beta gamma : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hnonzero : 0 < alpha + beta + gamma) (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (primeArchBlackHoleReciprocalMixedClock scaleLog alpha beta gamma) n).PosDef := by
  have hblack := HTGeometry.normalizedBlackHoleFarZoneJet_hankel_posDef scaleLog n
  have hreciprocal :
      (HTGeometry.momentHankelMatrix HTGeometry.reciprocalTailClock n).PosDef :=
    HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
      HTGeometry.reciprocalTailClock HTGeometry.reciprocalTailClock_eq_moment
      HTGeometry.reciprocalTailMeasure_integrable_moments
      HTGeometry.reciprocalTailMeasure_infiniteSupport n
  have hprime :
      (HTGeometry.momentHankelMatrix normalizedPrimeArchMoment n).PosDef := by
    change (primeArchSourceMomentHankelMatrix n).PosDef
    rw [primeArchSourceMomentHankelMatrix_eq_xiCentralMomentHankelMatrix]
    exact (xiCentralMomentHankelPosDef_iff_riemannHypothesis.mpr hRH) n
  rw [momentHankelMatrix_primeArchBlackHoleReciprocalMixedClock]
  by_cases halphaPos : 0 < alpha
  · exact ((hblack.smul halphaPos).add_posSemidef
      (hreciprocal.posSemidef.smul hbeta)).add_posSemidef
        (hprime.posSemidef.smul hgamma)
  · have halphaZero : alpha = 0 := le_antisymm (le_of_not_gt halphaPos) halpha
    by_cases hbetaPos : 0 < beta
    · simp only [halphaZero, zero_smul, zero_add]
      exact (hreciprocal.smul hbetaPos).add_posSemidef
        (hprime.posSemidef.smul hgamma)
    · have hbetaZero : beta = 0 := le_antisymm (le_of_not_gt hbetaPos) hbeta
      have hgammaPos : 0 < gamma := by linarith
      simp [halphaZero, hbetaZero]
      exact hprime.smul hgammaPos

/-- **Three-ray spectral-cone criterion for RH.**  RH is equivalent to strict positive
definiteness, at every finite depth, of every nonzero nonnegative mixture of the black-hole,
reciprocal-continuum, and normalized prime--archimedean moment rays. -/
theorem riemannHypothesis_iff_primeArchBlackHoleReciprocal_spectralCone_posDef :
    RiemannHypothesis ↔
      ∀ (scaleLog : ℂ) (alpha beta gamma : ℝ),
        0 ≤ alpha → 0 ≤ beta → 0 ≤ gamma → 0 < alpha + beta + gamma →
          ∀ n : ℕ,
            (HTGeometry.momentHankelMatrix
              (primeArchBlackHoleReciprocalMixedClock
                scaleLog alpha beta gamma) n).PosDef := by
  constructor
  · intro hRH scaleLog alpha beta gamma halpha hbeta hgamma hnonzero n
    exact primeArchBlackHoleReciprocalMixedClock_hankel_posDef_of_riemannHypothesis
      hRH scaleLog halpha hbeta hgamma hnonzero n
  · intro hcone
    apply primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mp
    intro n
    have hpure := hcone (0 : ℂ) 0 0 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) n
    rw [primeArchSourceMomentHankelMatrix_eq_momentHankelMatrix]
    have hpure' :
        (HTGeometry.momentHankelMatrix normalizedPrimeArchMoment n).PosDef := by
      rw [momentHankelMatrix_primeArchBlackHoleReciprocalMixedClock] at hpure
      simpa using hpure
    exact hpure'.det_pos

/-- Under RH no nonzero three-ray mixture lies in any fixed finite spectral-width local closure. -/
theorem primeArchBlackHoleReciprocalMixedClock_not_fixedSpectralWidthLocalClosure
    (hRH : RiemannHypothesis) (scaleLog : ℂ) {alpha beta gamma : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hnonzero : 0 < alpha + beta + gamma) (d : ℕ) :
    ¬ HTGeometry.FixedSpectralWidthLocalClosure d
      (primeArchBlackHoleReciprocalMixedClock scaleLog alpha beta gamma) := by
  apply HTGeometry.not_fixedSpectralWidthLocalClosure_of_det_ne_zero
  exact (primeArchBlackHoleReciprocalMixedClock_hankel_posDef_of_riemannHypothesis
    hRH scaleLog halpha hbeta hgamma hnonzero (d + 1)).det_pos.ne'

/-- Under RH no nonzero three-ray mixture lies in any fixed-dimensional linear state-space local
closure. -/
theorem primeArchBlackHoleReciprocalMixedClock_not_fixedStateSpaceDimensionLocalClosure
    (hRH : RiemannHypothesis) (scaleLog : ℂ) {alpha beta gamma : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hnonzero : 0 < alpha + beta + gamma) (d : ℕ) :
    ¬ HTGeometry.FixedStateSpaceDimensionLocalClosure d
      (primeArchBlackHoleReciprocalMixedClock scaleLog alpha beta gamma) := by
  apply HTGeometry.not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  exact (primeArchBlackHoleReciprocalMixedClock_hankel_posDef_of_riemannHypothesis
    hRH scaleLog halpha hbeta hgamma hnonzero (d + 1)).det_pos.ne'

end

end RHTower
