import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicAcceleration

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Strict fourth-Turan upper envelope for the fourth ordinary source-flux jet at modular
center. -/
def thetaCuspReflectedSourceDecayFluxFourthJetTuranCeilingAtZero
    (t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct 0 t *
    ((2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) - 320) -
      4 * thetaCuspReflectedLogJetOne 0 t * thetaCuspReflectedLogJetThree 0 t -
      3 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) +
      6 * thetaCuspReflectedLogJetOne 0 t ^ (2 : ℕ) * thetaCuspReflectedLogJetTwo 0 t -
      thetaCuspReflectedLogJetOne 0 t ^ (4 : ℕ))

theorem thetaCuspReflectedSourceDecayFluxFourthJet_lt_turanCeiling_zero
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceDecayFluxFourthJet 0 t <
      thetaCuspReflectedSourceDecayFluxFourthJetTuranCeilingAtZero t := by
  have hP : 0 < thetaCuspReflectedSourceProduct 0 t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hq := thetaCuspReflectedLogJetFour_zero_add_threeHundredTwenty_lt_two_sq ht
  unfold thetaCuspReflectedSourceDecayFluxFourthJet
    thetaCuspReflectedSourceDecayFluxFourthJetTuranCeilingAtZero
  apply mul_lt_mul_of_pos_left _ hP
  linarith

/-- Fourth-Turan ceiling for raw C5 acceleration, with every lower source jet retained exactly. -/
def thetaCuspReflectedSourceFifthRootCurvatureAccelerationTuranCeilingAtZero
    (t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop 0 t
  let D := thetaCuspReflectedSourceDecayFlux 0 t
  let J := thetaCuspReflectedSourceDecayFluxCurvature 0 t
  let K := thetaCuspReflectedSourceDecayFluxThirdJet 0 t
  let L := thetaCuspReflectedSourceDecayFluxFourthJetTuranCeilingAtZero t
  22 * D ^ (2 : ℕ) + 40 * A * J - 39 * t * D * J + 11 * t * A * K +
    t ^ (2 : ℕ) * (2 * D * K + 5 * A * L - 3 * J ^ (2 : ℕ))

theorem thetaCuspReflectedSourceFifthRootCurvatureAcceleration_lt_turanCeiling_zero
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceFifthRootCurvatureAcceleration 0 t <
      thetaCuspReflectedSourceFifthRootCurvatureAccelerationTuranCeilingAtZero t := by
  have hL := thetaCuspReflectedSourceDecayFluxFourthJet_lt_turanCeiling_zero ht
  have hA := thetaCuspReflectedSourceFirstDrop_pos 0 ht
  have hweight : 0 < 5 * t ^ (2 : ℕ) * thetaCuspReflectedSourceFirstDrop 0 t := by
    positivity
  have hmul := mul_lt_mul_of_pos_left hL hweight
  unfold thetaCuspReflectedSourceFifthRootCurvatureAcceleration
    thetaCuspReflectedSourceFifthRootCurvatureAccelerationTuranCeilingAtZero
  dsimp only
  linarith

/-- Fourth-Turan ceiling for the division-free intrinsic second derivative. -/
def thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero
    (t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop 0 t
  let D := thetaCuspReflectedSourceDecayFlux 0 t
  let J := thetaCuspReflectedSourceDecayFluxCurvature 0 t
  let N := thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t
  let Acc := thetaCuspReflectedSourceFifthRootCurvatureAccelerationTuranCeilingAtZero t
  Acc * A ^ (2 : ℕ) - 2 * N * (D ^ (2 : ℕ) + A * J)

theorem
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator_lt_turanCeiling_zero
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator 0 t <
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero t := by
  have hacc :=
    thetaCuspReflectedSourceFifthRootCurvatureAcceleration_lt_turanCeiling_zero ht
  have hA := thetaCuspReflectedSourceFirstDrop_pos 0 ht
  have hmul := mul_lt_mul_of_pos_right hacc (sq_pos_of_pos hA)
  unfold thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero
  dsimp only
  linarith

/-- At any intrinsic C5 local minimum, strict fourth-Turan curvature must leave a strictly
positive lower-jet compensation after its entire fourth-jet contribution is removed. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_pos_of_isLocalMin
    {t : ℝ} (ht : 0 < t)
    (hmin : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t) :
    0 <
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero t := by
  have hnonneg :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator_nonneg_of_isLocalMin
      0 ht hmin
  have hlt :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator_lt_turanCeiling_zero ht
  linarith

/-- Every modular-center C5 failure forces one negative intrinsic minimum where the exact
likelihood tax overspends its reserve and the lower three source jets strictly overcompensate the
entire fourth-Turan ceiling. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicFourthTuranCompensation
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 ∧
      IsLocalMin
        (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t ∧
      0 <
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero t ∧
      thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t + 320 <
        2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) ∧
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  obtain ⟨t, ht, hneg, hmin, _hrel, _hvel, hfour, hover⟩ :=
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicBalance_localMin
      hfail
  exact ⟨t, ht, hneg, hmin,
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_pos_of_isLocalMin
      ht hmin,
    hfour, hover⟩

/-- Exact fourth-Turan reduction. Global modular-center C5 is equivalent to ruling out the
strictly positive lower-jet compensation forced by fourth-Turan at every negative intrinsic
minimum. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_negativeIntrinsicMin_turanCeiling_nonpos :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        IsLocalMin
          (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t →
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 →
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero t ≤ 0 := by
  constructor
  · intro h t ht _hmin hneg
    have hNneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 :=
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_neg_iff 0 ht).mp hneg
    exact (not_lt_of_ge (h t ht) hNneg).elim
  · intro h t ht
    by_contra hnot
    obtain ⟨s, hs, hsneg, hsmin, hsceil, _hsfour, _hsover⟩ :=
      thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicFourthTuranCompensation
        ⟨t, ht, lt_of_not_ge hnot⟩
    exact (not_lt_of_ge (h s hs hsmin hsneg)) hsceil

end

end RHTower
