import GaloisForLFunctions.RHTower.XiShiftedHalfDensityAdmissionBoundaryPort
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionConnection

/-!
# Canonical admission mismatch from the source-native monic half-density landing

The adaptive half-density producer supplies a canonical monic tangent whose `n-1` coefficient is
the positive landing energy.  Actual inverse-Hankel admission velocity is another tangent of degree
strictly below `n`.  Coupling with `X P_n` sees only their `n-1` coefficient difference.

This file isolates that difference as one scalar, rewrites the existing canonical source connection
as positive landing energy plus the scalar mismatch, and expresses raw canonical odd-current drift
as `-2 h_n` times one exact dissipation reserve.  No fixed reporter is introduced: both velocities
are formed from the current moment-adapted admission.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Unique `X P_n`-visible difference between actual inverse-Hankel admission velocity and the
source-native monic half-density landing. -/
def xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch (y : ℝ) (n : ℕ) : ℝ :=
  (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) -
    xiShiftedAdaptiveMonicHalfDensityLanding
      (fun k => (xiShiftedReciprocalMoment y k).re) n).coeff (n - 1)

/-- Actual velocity minus source-native monic landing remains inside the lower tangent flag. -/
theorem natDegree_xiShiftedCanonicalAdmissionVelocity_sub_monicHalfDensityLanding_lt
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) -
      xiShiftedAdaptiveMonicHalfDensityLanding
        (fun k => (xiShiftedReciprocalMoment y k).re) n).natDegree < n := by
  let h := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
    (max_lt
      (natDegree_finitePolynomialVelocity_xiShiftedCanonicalAdmission_lt hn y)
      (natDegree_xiShiftedAdaptiveMonicHalfDensityLanding_lt h hn (by omega)))

/-- The entire odd-current coupling of velocity mismatch is norm times its one visible scalar. -/
theorem momentInner_xiShiftedCanonicalAdmissionVelocity_sub_monicHalfDensityLanding_eq_mismatch
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HTGeometry.momentInner (fun k => (xiShiftedReciprocalMoment y k).re)
        (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n) -
          xiShiftedAdaptiveMonicHalfDensityLanding
            (fun k => (xiShiftedReciprocalMoment y k).re) n)
        (X * HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) n) =
      HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
        xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch y n := by
  let h := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  exact momentInner_velocity_X_monicOrtho_eq_norm_mul_coeff_below
    h hn (by omega)
      (natDegree_xiShiftedCanonicalAdmissionVelocity_sub_monicHalfDensityLanding_lt hn hH)

/-- The visible mismatch is actual subleading velocity minus the positive monic landing energy. -/
theorem xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch_eq_velocityCoeff_sub_energy
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch y n =
      (finitePolynomialVelocity
        (xiShiftedCanonicalAdmissionVelocity y n)).coeff (n - 1) -
      xiShiftedAdaptiveMonicHalfDensityLandingEnergy
        (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  let h := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch, Polynomial.coeff_sub,
    coeff_xiShiftedAdaptiveMonicHalfDensityLanding_prev_eq_energy_below
      h hn (by omega)]

/-- Canonical inverse-Hankel source connection is positive monic landing energy plus exactly one
visible velocity-mismatch scalar. -/
theorem xiShiftedCanonicalAdmissionSourceConnection_eq_landingEnergy_add_visibleMismatch
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionSourceConnection y n =
      2 * HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
        (xiShiftedAdaptiveMonicHalfDensityLandingEnergy
            (fun k => (xiShiftedReciprocalMoment y k).re) n +
          xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch y n) := by
  rw [xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch_eq_velocityCoeff_sub_energy hn hH]
  unfold xiShiftedCanonicalAdmissionSourceConnection
  ring

/-- Exact reserve whose sign is equivalent to raw canonical odd-current dissipation. -/
def xiShiftedCanonicalAdmissionHalfDensityDissipationReserve (y : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.adaptiveOrthoJacobiEnergy
      (fun k => (xiShiftedReciprocalMoment y k).re) n -
    xiShiftedAdaptiveMonicHalfDensityLandingEnergy
      (fun k => (xiShiftedReciprocalMoment y k).re) n -
    xiShiftedCanonicalAdmissionVisibleHalfDensityMismatch y n

/-- **Exact scalar frontier.**  Raw current canonical odd-current drift is `-2 h_n` times the
half-density dissipation reserve.  Every projection term has disappeared; only one visible
admission-velocity mismatch remains. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_neg_two_norm_mul_halfDensityReserve
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n)
        (X * HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment v k).re) n))
      (-2 * HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n *
        xiShiftedCanonicalAdmissionHalfDensityDissipationReserve y n) y := by
  have h := hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_jacobiEnergy
    hy hn hH
  rw [xiShiftedCanonicalAdmissionSourceConnection_eq_landingEnergy_add_visibleMismatch
    hn hH] at h
  apply h.congr_deriv
  unfold xiShiftedCanonicalAdmissionHalfDensityDissipationReserve
  ring

end

end RHTower
