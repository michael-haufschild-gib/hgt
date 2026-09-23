import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicFourthTuran

open Real Set Filter Topology

namespace RHTower

noncomputable section

def thetaCuspReflectedActionRadiusAtZero (t : ℝ) : ℝ :=
  Real.exp (thetaCuspReflectedLogAction 0 t) - 1

def thetaCuspReflectedActionNormalizedVelocityAtZero (t : ℝ) : ℝ :=
  t * thetaCuspReflectedLogJetOne 0 t /
    thetaCuspReflectedActionRadiusAtZero t

def thetaCuspReflectedActionNormalizedFluxCurvatureAtZero (t : ℝ) : ℝ :=
  t ^ (2 : ℕ) *
      (thetaCuspReflectedLogJetTwo 0 t -
        thetaCuspReflectedLogJetOne 0 t ^ (2 : ℕ)) /
    thetaCuspReflectedActionRadiusAtZero t

def thetaCuspReflectedActionNormalizedFluxThirdJetAtZero (t : ℝ) : ℝ :=
  t ^ (3 : ℕ) *
      (thetaCuspReflectedLogJetThree 0 t -
        3 * thetaCuspReflectedLogJetOne 0 t *
          thetaCuspReflectedLogJetTwo 0 t +
        thetaCuspReflectedLogJetOne 0 t ^ (3 : ℕ)) /
    thetaCuspReflectedActionRadiusAtZero t

def thetaCuspReflectedActionNormalizedRiccatiMarginAtZero (t : ℝ) : ℝ :=
  t ^ (3 : ℕ) * thetaCuspReflectedLogRiccatiMargin 0 t /
    thetaCuspReflectedActionRadiusAtZero t

def thetaCuspReflectedActionNormalizedTuranFourthFluxAtZero (t : ℝ) : ℝ :=
  t ^ (4 : ℕ) *
      (thetaCuspReflectedSourceDecayFluxFourthJetTuranCeilingAtZero t /
        thetaCuspReflectedSourceProduct 0 t) /
    thetaCuspReflectedActionRadiusAtZero t

def thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderCoreAtZero
    (t : ℝ) : ℝ :=
  let s := thetaCuspReflectedActionNormalizedVelocityAtZero t
  let b := thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t
  let c := thetaCuspReflectedActionNormalizedFluxThirdJetAtZero t
  let d := thetaCuspReflectedActionNormalizedTuranFourthFluxAtZero t
  22 * s ^ (2 : ℕ) + 40 * b - 39 * s * b + 11 * c + 2 * s * c + 5 * d -
    3 * b ^ (2 : ℕ) - 2 * (24 - 9 * s + 5 * b - 4 * s ^ (2 : ℕ)) * (s ^ (2 : ℕ) + b)

def thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero
    (t : ℝ) : ℝ :=
  let r := thetaCuspReflectedActionRadiusAtZero t
  let s := thetaCuspReflectedActionNormalizedVelocityAtZero t
  let b := thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t
  let rho := thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t
  99 * s - 123 * s ^ (2 : ℕ) + 24 * s ^ (4 : ℕ) - 51 * b + 36 * s * b +
    16 * s ^ (2 : ℕ) * b - 65 * b ^ (2 : ℕ) + 100 * s * r * rho -
    8000 * t ^ (4 : ℕ) / r - 25 * r * (b + 2 * s ^ (2 : ℕ) * r) ^ (2 : ℕ)

private theorem intrinsicSecondOrderCore_eq_riccatiBudget_div_five
    {t r s b c d rho : ℝ}
    (hstationary : -9 * s + b + s ^ (2 : ℕ) + 5 * c - 13 * s * b + 8 * s ^ (3 : ℕ) = 0)
    (hfourth :
      d = -320 * t ^ (4 : ℕ) / r - b ^ (2 : ℕ) * r - 4 * s ^ (2 : ℕ) * b * r ^ (2 : ℕ) -
        4 * s ^ (4 : ℕ) * r ^ (3 : ℕ) + 4 * s * r * rho) :
    5 * (22 * s ^ (2 : ℕ) + 40 * b - 39 * s * b + 11 * c + 2 * s * c + 5 * d -
        3 * b ^ (2 : ℕ) - 2 * (24 - 9 * s + 5 * b - 4 * s ^ (2 : ℕ)) * (s ^ (2 : ℕ) + b)) =
      99 * s - 123 * s ^ (2 : ℕ) + 24 * s ^ (4 : ℕ) - 51 * b + 36 * s * b +
        16 * s ^ (2 : ℕ) * b - 65 * b ^ (2 : ℕ) + 100 * s * r * rho -
        8000 * t ^ (4 : ℕ) / r - 25 * r * (b + 2 * s ^ (2 : ℕ) * r) ^ (2 : ℕ) := by
  calc
    _ = 99 * s - 123 * s ^ (2 : ℕ) + 24 * s ^ (4 : ℕ) - 51 * b + 36 * s * b +
          16 * s ^ (2 : ℕ) * b - 65 * b ^ (2 : ℕ) + 25 * d := by
      linear_combination (11 + 2 * s) * hstationary
    _ = _ := by
      rw [hfourth]
      ring

theorem thetaCuspReflectedActionRadiusAtZero_pos
    {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedActionRadiusAtZero t := by
  unfold thetaCuspReflectedActionRadiusAtZero
  rw [sub_pos, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := 0) ht)

private theorem thetaCuspReflectedActionNormalizedRiccatiMarginAtZero_eq
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t =
      -(thetaCuspReflectedActionNormalizedFluxThirdJetAtZero t +
        thetaCuspReflectedActionNormalizedVelocityAtZero t *
          thetaCuspReflectedActionRadiusAtZero t *
          thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t) := by
  have hr := (thetaCuspReflectedActionRadiusAtZero_pos ht).ne'
  unfold thetaCuspReflectedActionNormalizedRiccatiMarginAtZero
    thetaCuspReflectedActionNormalizedFluxThirdJetAtZero
    thetaCuspReflectedActionNormalizedVelocityAtZero
    thetaCuspReflectedActionNormalizedFluxCurvatureAtZero
    thetaCuspReflectedLogRiccatiMargin
  field_simp [hr]
  ring

private theorem thetaCuspReflectedActionNormalizedTuranFourthFluxAtZero_eq
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionNormalizedTuranFourthFluxAtZero t =
      (let r := thetaCuspReflectedActionRadiusAtZero t;
      let s := thetaCuspReflectedActionNormalizedVelocityAtZero t;
      let b := thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t;
      let rho := thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t;
      -320 * t ^ (4 : ℕ) / r - b ^ (2 : ℕ) * r - 4 * s ^ (2 : ℕ) * b * r ^ (2 : ℕ) -
        4 * s ^ (4 : ℕ) * r ^ (3 : ℕ) + 4 * s * r * rho) := by
  have hr := (thetaCuspReflectedActionRadiusAtZero_pos ht).ne'
  have hP : thetaCuspReflectedSourceProduct 0 t ≠ 0 := by
    unfold thetaCuspReflectedSourceProduct
    exact (mul_pos (thetaCuspFullSource_pos_all _)
      (thetaCuspFullSource_pos_all _)).ne'
  rw [thetaCuspReflectedActionNormalizedRiccatiMarginAtZero_eq ht]
  unfold thetaCuspReflectedActionNormalizedTuranFourthFluxAtZero
    thetaCuspReflectedSourceDecayFluxFourthJetTuranCeilingAtZero
    thetaCuspReflectedActionNormalizedFluxThirdJetAtZero
    thetaCuspReflectedActionNormalizedVelocityAtZero
    thetaCuspReflectedActionNormalizedFluxCurvatureAtZero
  dsimp only
  field_simp [hr, hP]
  ring

private theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicStationary_normalized
    {t : ℝ} (ht : 0 < t)
    (hstationary :
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t *
          thetaCuspReflectedSourceFirstDrop 0 t =
        2 * thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t *
          thetaCuspReflectedSourceDecayFlux 0 t) :
    (let s := thetaCuspReflectedActionNormalizedVelocityAtZero t;
    let b := thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t;
    let c := thetaCuspReflectedActionNormalizedFluxThirdJetAtZero t;
    -9 * s + b + s ^ (2 : ℕ) + 5 * c - 13 * s * b + 8 * s ^ (3 : ℕ) = 0) := by
  have hP : 0 < thetaCuspReflectedSourceProduct 0 t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hr : 0 < thetaCuspReflectedActionRadiusAtZero t :=
    thetaCuspReflectedActionRadiusAtZero_pos ht
  have hA : thetaCuspReflectedSourceFirstDrop 0 t =
      thetaCuspReflectedSourceProduct 0 t *
        thetaCuspReflectedActionRadiusAtZero t := by
    simpa only [thetaCuspReflectedActionRadiusAtZero] using
      thetaCuspReflectedSourceFirstDrop_eq_product_mul_exp_action_sub_one 0 t
  unfold thetaCuspReflectedSourceFifthRootCurvatureVelocity
    thetaCuspReflectedSourceFifthRootCurvatureNumerator
    thetaCuspReflectedSourceDecayFlux
    thetaCuspReflectedSourceDecayFluxCurvature
    thetaCuspReflectedSourceDecayFluxThirdJet at hstationary
  rw [hA] at hstationary
  unfold thetaCuspReflectedActionNormalizedVelocityAtZero
    thetaCuspReflectedActionNormalizedFluxCurvatureAtZero
    thetaCuspReflectedActionNormalizedFluxThirdJetAtZero
  dsimp only
  field_simp [hr.ne']
  field_simp [hP.ne'] at hstationary
  linear_combination t * hstationary

private theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_eq_core
    {t : ℝ} (ht : 0 < t) :
    t ^ (2 : ℕ) *
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero t =
      thetaCuspReflectedSourceFirstDrop 0 t ^ (4 : ℕ) *
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderCoreAtZero t := by
  have hP : 0 < thetaCuspReflectedSourceProduct 0 t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hr : 0 < thetaCuspReflectedActionRadiusAtZero t :=
    thetaCuspReflectedActionRadiusAtZero_pos ht
  have hA : thetaCuspReflectedSourceFirstDrop 0 t =
      thetaCuspReflectedSourceProduct 0 t *
        thetaCuspReflectedActionRadiusAtZero t := by
    simpa only [thetaCuspReflectedActionRadiusAtZero] using
      thetaCuspReflectedSourceFirstDrop_eq_product_mul_exp_action_sub_one 0 t
  unfold thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero
    thetaCuspReflectedSourceFifthRootCurvatureAccelerationTuranCeilingAtZero
    thetaCuspReflectedSourceFifthRootCurvatureNumerator
    thetaCuspReflectedSourceDecayFlux
    thetaCuspReflectedSourceDecayFluxCurvature
    thetaCuspReflectedSourceDecayFluxThirdJet
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderCoreAtZero
    thetaCuspReflectedActionNormalizedVelocityAtZero
    thetaCuspReflectedActionNormalizedFluxCurvatureAtZero
    thetaCuspReflectedActionNormalizedFluxThirdJetAtZero
    thetaCuspReflectedActionNormalizedTuranFourthFluxAtZero
  dsimp only
  rw [hA]
  field_simp [hP.ne', hr.ne']
  ring

theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_eq_riccatiBudget
    {t : ℝ} (ht : 0 < t)
    (hstationary :
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t *
          thetaCuspReflectedSourceFirstDrop 0 t =
        2 * thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t *
          thetaCuspReflectedSourceDecayFlux 0 t) :
    5 * t ^ (2 : ℕ) *
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero t =
      thetaCuspReflectedSourceFirstDrop 0 t ^ (4 : ℕ) *
        thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t := by
  have hcore :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_eq_core ht
  have hstat :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicStationary_normalized ht hstationary
  have hfourth :=
    thetaCuspReflectedActionNormalizedTuranFourthFluxAtZero_eq ht
  let r := thetaCuspReflectedActionRadiusAtZero t
  let s := thetaCuspReflectedActionNormalizedVelocityAtZero t
  let b := thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t
  let c := thetaCuspReflectedActionNormalizedFluxThirdJetAtZero t
  let d := thetaCuspReflectedActionNormalizedTuranFourthFluxAtZero t
  let rho := thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t
  have hbudget :
      5 * thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderCoreAtZero t =
        thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t := by
    simpa only [
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderCoreAtZero,
      thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero,
      r, s, b, c, d, rho] using
      (intrinsicSecondOrderCore_eq_riccatiBudget_div_five
        (r := r) (s := s) (b := b) (c := c) (d := d) (rho := rho)
        (t := t) hstat hfourth)
  calc
    _ = 5 * (thetaCuspReflectedSourceFirstDrop 0 t ^ (4 : ℕ) *
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderCoreAtZero t) := by
      linear_combination 5 * hcore
    _ = thetaCuspReflectedSourceFirstDrop 0 t ^ (4 : ℕ) *
        (5 * thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderCoreAtZero t) := by
      ring
    _ = _ := by rw [hbudget]

/-- At every intrinsic C5 local minimum, the scaled Riccati margin must pay the complete
fourth-Turan cost and the residual perfect-square cost. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero_pos_of_isLocalMin
    {t : ℝ} (ht : 0 < t)
    (hmin : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t) :
    0 < thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t := by
  have hstationary :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_isLocalMin_velocity
      0 ht hmin
  have heq :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_eq_riccatiBudget
      ht hstationary
  have hceil :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_pos_of_isLocalMin
      ht hmin
  have hleft : 0 < 5 * t ^ (2 : ℕ) *
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero t := by
    positivity
  have hA4 : 0 < thetaCuspReflectedSourceFirstDrop 0 t ^ (4 : ℕ) := by
    exact pow_pos (thetaCuspReflectedSourceFirstDrop_pos 0 ht) 4
  by_contra hnot
  have hbudgetNonpos :
      thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t ≤ 0 :=
    le_of_not_gt hnot
  have hrightNonpos : thetaCuspReflectedSourceFirstDrop 0 t ^ (4 : ℕ) *
      thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hA4.le hbudgetNonpos
  linarith

/-- Every modular-center C5 failure forces a negative intrinsic minimum with strict Riccati
overcompensation, strict fourth-Turan curvature, and likelihood-tax overspend. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicRiccatiCompensation
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 ∧
      IsLocalMin
        (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t ∧
      0 < thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t ∧
      thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t + 320 <
        2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) ∧
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  obtain ⟨t, ht, hneg, hmin, _hceil, hfour, hover⟩ :=
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicFourthTuranCompensation
      hfail
  exact ⟨t, ht, hneg, hmin,
    thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero_pos_of_isLocalMin
      ht hmin,
    hfour, hover⟩

/-- Exact Riccati-budget reduction. Global modular-center C5 is equivalent to ruling out the
strict Riccati overcompensation forced at every negative intrinsic minimum. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_negativeIntrinsicMin_riccatiBudget_nonpos :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        IsLocalMin
          (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t →
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 →
        thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t ≤ 0 := by
  constructor
  · intro h t ht _hmin hneg
    have hNneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 :=
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_neg_iff 0 ht).mp hneg
    exact (not_lt_of_ge (h t ht) hNneg).elim
  · intro h t ht
    by_contra hnot
    obtain ⟨s, hs, hsneg, hsmin, hsbudget, _hsfour, _hsover⟩ :=
      thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicRiccatiCompensation
        ⟨t, ht, lt_of_not_ge hnot⟩
    exact (not_lt_of_ge (h s hs hsmin hsneg)) hsbudget

end

end RHTower
