import GaloisForLFunctions.HTGeometry.BlackHoleDressedLogSpectralClock
import GaloisForLFunctions.HTGeometry.ReciprocalTailHankelStrict

/-!
# A strict spectral cone joining black-hole and continuum clocks

The normalized Schwarzschild far-zone jet is a strict Gamma--zeta moment clock, while the
reciprocal observation tail is the strict continuum moment clock on `[0,1]`.  Strict Hankel
geometry survives every nonzero nonnegative mixture, including both boundary rays.  Thus no
cancellation inside this physical two-source cone can restore a finite spectral palette or a
finite-dimensional hidden-state model.
-/

namespace HTGeometry

noncomputable section

/-- Nonnegative mixture of the normalized black-hole Gamma clock and the reciprocal continuum
clock. -/
def blackHoleReciprocalMixedClock
    (scaleLog : ℂ) (alpha beta : ℝ) (n : ℕ) : ℝ :=
  alpha * normalizedBlackHoleFarZoneJet scaleLog n + beta * reciprocalTailClock n

/-- Hankel formation is exactly linear on the black-hole/reciprocal spectral cone. -/
theorem momentHankelMatrix_blackHoleReciprocalMixedClock
    (scaleLog : ℂ) (alpha beta : ℝ) (n : ℕ) :
    momentHankelMatrix (blackHoleReciprocalMixedClock scaleLog alpha beta) n =
      alpha • momentHankelMatrix (normalizedBlackHoleFarZoneJet scaleLog) n +
        beta • momentHankelMatrix reciprocalTailClock n := by
  ext i j
  simp [momentHankelMatrix, blackHoleReciprocalMixedClock]

/-- **Black-hole/continuum strict spectral-cone law.**  Every nonzero nonnegative mixture has a
positive-definite Hankel block at every finite depth. -/
theorem blackHoleReciprocalMixedClock_hankel_posDef
    (scaleLog : ℂ) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hnonzero : 0 < alpha + beta)
    (n : ℕ) :
    (momentHankelMatrix (blackHoleReciprocalMixedClock scaleLog alpha beta) n).PosDef := by
  have hblack := normalizedBlackHoleFarZoneJet_hankel_posDef scaleLog n
  have hreciprocal : (momentHankelMatrix reciprocalTailClock n).PosDef :=
    momentHankelMatrix_posDef_of_infiniteSupport reciprocalTailClock
      reciprocalTailClock_eq_moment reciprocalTailMeasure_integrable_moments
      reciprocalTailMeasure_infiniteSupport n
  rw [momentHankelMatrix_blackHoleReciprocalMixedClock]
  by_cases halphaPos : 0 < alpha
  · exact (hblack.smul halphaPos).add_posSemidef
      (hreciprocal.posSemidef.smul hbeta)
  · have halphaZero : alpha = 0 := le_antisymm (le_of_not_gt halphaPos) halpha
    have hbetaPos : 0 < beta := by linarith
    simp [halphaZero]
    exact hreciprocal.smul hbetaPos

/-- Every finite determinant on the nonzero physical spectral cone is strictly positive. -/
theorem det_blackHoleReciprocalMixedClock_hankel_pos
    (scaleLog : ℂ) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hnonzero : 0 < alpha + beta)
    (n : ℕ) :
    0 < (momentHankelMatrix
      (blackHoleReciprocalMixedClock scaleLog alpha beta) n).det :=
  (blackHoleReciprocalMixedClock_hankel_posDef
    scaleLog halpha hbeta hnonzero n).det_pos

/-- No fixed finite spectral palette lies in the local closure of any nonzero clock in the cone. -/
theorem blackHoleReciprocalMixedClock_not_fixedSpectralWidthLocalClosure
    (scaleLog : ℂ) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hnonzero : 0 < alpha + beta)
    (d : ℕ) :
    ¬ FixedSpectralWidthLocalClosure d
      (blackHoleReciprocalMixedClock scaleLog alpha beta) := by
  apply not_fixedSpectralWidthLocalClosure_of_det_ne_zero
  exact ne_of_gt
    (det_blackHoleReciprocalMixedClock_hankel_pos
      scaleLog halpha hbeta hnonzero (d + 1))

/-- No fixed-dimensional linear state space lies in the local closure of any nonzero clock in
the cone. -/
theorem blackHoleReciprocalMixedClock_not_fixedStateSpaceDimensionLocalClosure
    (scaleLog : ℂ) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hnonzero : 0 < alpha + beta)
    (d : ℕ) :
    ¬ FixedStateSpaceDimensionLocalClosure d
      (blackHoleReciprocalMixedClock scaleLog alpha beta) := by
  apply not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  exact ne_of_gt
    (det_blackHoleReciprocalMixedClock_hankel_pos
      scaleLog halpha hbeta hnonzero (d + 1))

end

end HTGeometry
