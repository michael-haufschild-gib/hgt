import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicRiccatiBudget

/-!
# Backward Riccati drift for the modular-center theta C5 wall

The local Riccati law has the wrong orientation for the remaining C5 upper envelope.  This file
instead differentiates the normalized Riccati margin.  In the action variables `(r,s,b,rho)`, its
logarithmic-scale derivative is

`rho*(3-s*(3*r+1)) + 4*s^(2 : ℕ)*r^(2 : ℕ)*(b+s^(2 : ℕ)*r) + (t^(4 : ℕ)/r)*(2*q2^(2 : ℕ)-q4)`.

The strict completed-theta fourth-Turan theorem makes the final summand strictly larger than
`320*t^(4 : ℕ)/r`.  Thus the evolution has a strict forward lower drift.  Hostile testing of the
backward idea identifies its exact integrating factor: the conjugated quantity is
`exp(2*q)*R`, and it is strictly increasing.  Therefore cofinal decay of normalized `rho` cannot
be used as a zero terminal condition: normalization hides an increasing Riccati charge.  Any
successful `C5-RB1` proof must upper-control that charge by additional nonlocal theta structure.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Strict fourth-Turan floor in the logarithmic-scale evolution of the normalized center
Riccati margin. -/
def thetaCuspReflectedActionNormalizedRiccatiBackwardDriftAtZero
    (t : ℝ) : ℝ :=
  let r := thetaCuspReflectedActionRadiusAtZero t
  let s := thetaCuspReflectedActionNormalizedVelocityAtZero t
  let b := thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t
  let rho := thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t
  rho * (3 - s * (3 * r + 1)) +
    4 * s ^ (2 : ℕ) * r ^ (2 : ℕ) * (b + s ^ (2 : ℕ) * r) + 320 * t ^ (4 : ℕ) / r

private theorem riccati_drift_algebra
    {t r s b rho q1 q2 q3 q4 : ℝ}
    (ht : t ≠ 0) (hr : r ≠ 0)
    (hs : s = t * q1 / r)
    (hb : b = t ^ (2 : ℕ) * (q2 - q1 ^ (2 : ℕ)) / r)
    (hrho : rho = t ^ (3 : ℕ) * (2 * q1 * q2 - q3) / r) :
    3 * rho + t ^ (4 : ℕ) *
          (2 * q2 ^ (2 : ℕ) + 2 * q1 * q3 - q4) / r -
        rho * s * (r + 1) =
      rho * (3 - s * (3 * r + 1)) +
        4 * s ^ (2 : ℕ) * r ^ (2 : ℕ) * (b + s ^ (2 : ℕ) * r) +
        t ^ (4 : ℕ) * (2 * q2 ^ (2 : ℕ) - q4) / r := by
  subst s
  subst b
  subst rho
  field_simp [hr]
  ring

private theorem hasDerivAt_thetaCuspReflectedActionRadiusAtZero
    (t : ℝ) :
    HasDerivAt thetaCuspReflectedActionRadiusAtZero
      ((thetaCuspReflectedActionRadiusAtZero t + 1) *
        thetaCuspReflectedLogJetOne 0 t) t := by
  have hq := hasDerivAt_thetaCuspReflectedLogAction 0 t
  have hexp := hq.exp
  have hsub := hexp.sub_const 1
  change HasDerivAt
    (fun y => Real.exp (thetaCuspReflectedLogAction 0 y) - 1)
    ((Real.exp (thetaCuspReflectedLogAction 0 t) - 1 + 1) *
      thetaCuspReflectedLogJetOne 0 t) t
  refine (hsub.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  ring

private theorem hasDerivAt_thetaCuspReflectedLogRiccatiMargin_zero
    (t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogRiccatiMargin 0)
      (2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) +
        2 * thetaCuspReflectedLogJetOne 0 t *
          thetaCuspReflectedLogJetThree 0 t -
        thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t) t := by
  have hq1 := hasDerivAt_thetaCuspReflectedLogJetOne 0 t
  have hq2 := hasDerivAt_thetaCuspReflectedLogJetTwo 0 t
  have hq3 := hasDerivAt_thetaCuspReflectedLogJetThree_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t
  unfold thetaCuspReflectedLogRiccatiMargin
  convert ((hq1.mul hq2).const_mul 2).sub hq3 using 1
  any_goals rfl
  · funext y
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  · ring

/-- Exact normalized Riccati evolution in the intrinsic action variables. -/
theorem hasDerivAt_thetaCuspReflectedActionNormalizedRiccatiMarginAtZero
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt thetaCuspReflectedActionNormalizedRiccatiMarginAtZero
      ((thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t *
            (3 - thetaCuspReflectedActionNormalizedVelocityAtZero t *
              (3 * thetaCuspReflectedActionRadiusAtZero t + 1)) +
          4 * thetaCuspReflectedActionNormalizedVelocityAtZero t ^ (2 : ℕ) *
            thetaCuspReflectedActionRadiusAtZero t ^ (2 : ℕ) *
            (thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t +
              thetaCuspReflectedActionNormalizedVelocityAtZero t ^ (2 : ℕ) *
                thetaCuspReflectedActionRadiusAtZero t) +
          t ^ (4 : ℕ) *
            (2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) -
              thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t) /
            thetaCuspReflectedActionRadiusAtZero t) / t) t := by
  have hrpos := thetaCuspReflectedActionRadiusAtZero_pos ht
  have hr := hrpos.ne'
  have hR := hasDerivAt_thetaCuspReflectedLogRiccatiMargin_zero t
  have hnum := ((hasDerivAt_id t).pow 3).mul hR
  have hrad := hasDerivAt_thetaCuspReflectedActionRadiusAtZero t
  have hraw := hnum.div hrad hr
  have hs : thetaCuspReflectedActionNormalizedVelocityAtZero t =
      t * thetaCuspReflectedLogJetOne 0 t /
        thetaCuspReflectedActionRadiusAtZero t := rfl
  have hb : thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t =
      t ^ (2 : ℕ) * (thetaCuspReflectedLogJetTwo 0 t -
        thetaCuspReflectedLogJetOne 0 t ^ (2 : ℕ)) /
        thetaCuspReflectedActionRadiusAtZero t := rfl
  have hrho : thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t =
      t ^ (3 : ℕ) * thetaCuspReflectedLogRiccatiMargin 0 t /
        thetaCuspReflectedActionRadiusAtZero t := rfl
  have hid :
      3 * thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t +
            t ^ (4 : ℕ) *
              (2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) +
                2 * thetaCuspReflectedLogJetOne 0 t *
                  thetaCuspReflectedLogJetThree 0 t -
                thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t) /
              thetaCuspReflectedActionRadiusAtZero t -
            thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t *
              thetaCuspReflectedActionNormalizedVelocityAtZero t *
              (thetaCuspReflectedActionRadiusAtZero t + 1) =
          thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t *
              (3 - thetaCuspReflectedActionNormalizedVelocityAtZero t *
                (3 * thetaCuspReflectedActionRadiusAtZero t + 1)) +
            4 * thetaCuspReflectedActionNormalizedVelocityAtZero t ^ (2 : ℕ) *
              thetaCuspReflectedActionRadiusAtZero t ^ (2 : ℕ) *
              (thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t +
                thetaCuspReflectedActionNormalizedVelocityAtZero t ^ (2 : ℕ) *
                  thetaCuspReflectedActionRadiusAtZero t) +
            t ^ (4 : ℕ) *
              (2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) -
                thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t) /
              thetaCuspReflectedActionRadiusAtZero t := by
    exact riccati_drift_algebra ht.ne' hr hs hb hrho
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [thetaCuspReflectedActionNormalizedRiccatiMarginAtZero,
      Pi.div_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  · apply (eq_div_iff ht.ne').2
    rw [← hid, hrho, hs]
    simp only [id_eq, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat,
      Nat.reduceSub, pow_two]
    field_simp [hr]

/-- Strict forward drift forced by the completed-theta fourth-Turan law. -/
theorem thetaCuspReflectedActionNormalizedRiccatiBackwardDriftAtZero_lt_logDeriv
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionNormalizedRiccatiBackwardDriftAtZero t <
      t * deriv thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t := by
  rw [(hasDerivAt_thetaCuspReflectedActionNormalizedRiccatiMarginAtZero ht).deriv]
  have hr := thetaCuspReflectedActionRadiusAtZero_pos ht
  have hT := thetaCuspReflectedLogJetFour_zero_add_threeHundredTwenty_lt_two_sq ht
  have hscaled :
      320 * t ^ (4 : ℕ) / thetaCuspReflectedActionRadiusAtZero t <
        t ^ (4 : ℕ) *
          (2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) -
            thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t) /
          thetaCuspReflectedActionRadiusAtZero t := by
    apply (div_lt_div_iff_of_pos_right hr).2
    nlinarith [pow_pos ht 4]
  unfold thetaCuspReflectedActionNormalizedRiccatiBackwardDriftAtZero
  dsimp only
  rw [mul_div_cancel₀ _ ht.ne']
  linarith

/-- Riccati charge exposed by the exact integrating factor of the normalized drift equation. -/
def thetaCuspReflectedActionRiccatiChargeAtZero (t : ℝ) : ℝ :=
  Real.exp (2 * thetaCuspReflectedLogAction 0 t) *
    thetaCuspReflectedLogRiccatiMargin 0 t

/-- Exact charge evolution.  The mixed third-jet channel cancels after conjugation. -/
theorem hasDerivAt_thetaCuspReflectedActionRiccatiChargeAtZero (t : ℝ) :
    HasDerivAt thetaCuspReflectedActionRiccatiChargeAtZero
      (Real.exp (2 * thetaCuspReflectedLogAction 0 t) *
        (2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) +
          4 * thetaCuspReflectedLogJetOne 0 t ^ (2 : ℕ) *
            thetaCuspReflectedLogJetTwo 0 t -
          thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t)) t := by
  have hq := hasDerivAt_thetaCuspReflectedLogAction 0 t
  have h2q := hq.const_mul 2
  have hexp := h2q.exp
  have hR := hasDerivAt_thetaCuspReflectedLogRiccatiMargin_zero t
  unfold thetaCuspReflectedActionRiccatiChargeAtZero
  convert hexp.mul hR using 1
  any_goals rfl
  unfold thetaCuspReflectedLogRiccatiMargin
  ring

/-- The integrating-factor Riccati charge is strictly increasing on the positive source ray. -/
theorem deriv_thetaCuspReflectedActionRiccatiChargeAtZero_pos
    {t : ℝ} (ht : 0 < t) :
    0 < deriv thetaCuspReflectedActionRiccatiChargeAtZero t := by
  rw [(hasDerivAt_thetaCuspReflectedActionRiccatiChargeAtZero t).deriv]
  have hT := thetaCuspReflectedLogJetFour_zero_add_threeHundredTwenty_lt_two_sq ht
  have hq1 := thetaCuspReflectedLogJetOne_pos 0 ht
  have hq2 : 0 < thetaCuspReflectedLogJetTwo 0 t := by
    unfold thetaCuspReflectedLogJetTwo
    rw [show 0 + t = t by ring, show 0 - t = -t by ring,
      thetaCuspLogCurvature_neg]
    nlinarith [thetaCuspLogCurvature_pos t]
  have hpositive :
      0 < 4 * thetaCuspReflectedLogJetOne 0 t ^ (2 : ℕ) *
        thetaCuspReflectedLogJetTwo 0 t := by positivity
  have hinside :
      0 < 2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) +
          4 * thetaCuspReflectedLogJetOne 0 t ^ (2 : ℕ) *
            thetaCuspReflectedLogJetTwo 0 t -
          thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t := by
    nlinarith
  exact mul_pos (Real.exp_pos _) hinside

theorem continuous_thetaCuspReflectedActionRiccatiChargeAtZero :
    Continuous thetaCuspReflectedActionRiccatiChargeAtZero := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_thetaCuspReflectedActionRiccatiChargeAtZero t).continuousAt

/-- The conjugated Riccati charge grows strictly from the modular seam. -/
theorem strictMonoOn_thetaCuspReflectedActionRiccatiChargeAtZero :
    StrictMonoOn thetaCuspReflectedActionRiccatiChargeAtZero (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact continuous_thetaCuspReflectedActionRiccatiChargeAtZero.continuousOn
  · intro t ht
    rw [interior_Ici] at ht
    exact deriv_thetaCuspReflectedActionRiccatiChargeAtZero_pos ht

theorem thetaCuspReflectedActionRiccatiChargeAtZero_zero :
    thetaCuspReflectedActionRiccatiChargeAtZero 0 = 0 := by
  have hq1 := thetaCuspReflectedLogJetOne_zero 0
  have hq3 := thetaCuspReflectedLogJetThree_zero 0
  unfold thetaCuspReflectedActionRiccatiChargeAtZero
    thetaCuspReflectedLogRiccatiMargin
  rw [hq1, hq3]
  ring

theorem thetaCuspReflectedActionRiccatiChargeAtZero_pos
    {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedActionRiccatiChargeAtZero t := by
  rw [← thetaCuspReflectedActionRiccatiChargeAtZero_zero]
  exact strictMonoOn_thetaCuspReflectedActionRiccatiChargeAtZero
    (by simp) (by simp [ht.le]) ht

/-- Exact integrating-factor identity.  The normalized margin may decay only because the inverse
factor `t^(3 : ℕ) / (r*(r+1)^(2 : ℕ))` collapses; the conjugated charge itself grows. -/
theorem thetaCuspReflectedActionRiccatiChargeAtZero_eq_integratingFactor
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionRiccatiChargeAtZero t =
      thetaCuspReflectedActionRadiusAtZero t *
          (thetaCuspReflectedActionRadiusAtZero t + 1) ^ (2 : ℕ) / t ^ (3 : ℕ) *
        thetaCuspReflectedActionNormalizedRiccatiMarginAtZero t := by
  have hr := (thetaCuspReflectedActionRadiusAtZero_pos ht).ne'
  have he : Real.exp (thetaCuspReflectedLogAction 0 t) - 1 ≠ 0 := by
    simpa only [thetaCuspReflectedActionRadiusAtZero] using hr
  unfold thetaCuspReflectedActionRiccatiChargeAtZero
    thetaCuspReflectedActionNormalizedRiccatiMarginAtZero
    thetaCuspReflectedActionRadiusAtZero
  rw [show Real.exp (2 * thetaCuspReflectedLogAction 0 t) =
      Real.exp (thetaCuspReflectedLogAction 0 t) ^ (2 : ℕ) by
    rw [show 2 * thetaCuspReflectedLogAction 0 t =
        thetaCuspReflectedLogAction 0 t +
          thetaCuspReflectedLogAction 0 t by ring,
      Real.exp_add, pow_two]]
  field_simp [he, ht.ne']
  ring

/-- Division-free gap between the exact C5 compensation barrier and the increasing Riccati
charge.  This is the charge-coordinate form of the surviving `C5-RB1` burden. -/
def thetaCuspReflectedActionRiccatiChargeEnvelopeGapAtZero (t : ℝ) : ℝ :=
  let r := thetaCuspReflectedActionRadiusAtZero t
  let s := thetaCuspReflectedActionNormalizedVelocityAtZero t
  let b := thetaCuspReflectedActionNormalizedFluxCurvatureAtZero t
  (r + 1) ^ (2 : ℕ) *
      (8000 * t ^ (4 : ℕ) / r + 25 * r * (b + 2 * s ^ (2 : ℕ) * r) ^ (2 : ℕ) -
        (99 * s - 123 * s ^ (2 : ℕ) + 24 * s ^ (4 : ℕ) - 51 * b + 36 * s * b +
          16 * s ^ (2 : ℕ) * b - 65 * b ^ (2 : ℕ))) -
    100 * s * t ^ (3 : ℕ) * thetaCuspReflectedActionRiccatiChargeAtZero t

/-- The conjugated charge is the literal source-product flux Wronskian.  This removes every
logarithmic jet from the quantity which now needs a nonlocal upper comparison. -/
theorem thetaCuspReflectedActionRiccatiChargeAtZero_eq_fluxWronskian
    (t : ℝ) :
    thetaCuspReflectedActionRiccatiChargeAtZero t =
      Real.exp (2 * thetaCuspReflectedLogAction 0 t) *
        (-(thetaCuspReflectedSourceProduct 0 t *
              thetaCuspReflectedSourceDecayFluxThirdJet 0 t +
            thetaCuspReflectedSourceDecayFlux 0 t *
              thetaCuspReflectedSourceDecayFluxCurvature 0 t) /
          thetaCuspReflectedSourceProduct 0 t ^ (2 : ℕ)) := by
  have hP : thetaCuspReflectedSourceProduct 0 t ≠ 0 := by
    unfold thetaCuspReflectedSourceProduct
    exact (mul_pos (thetaCuspFullSource_pos_all _)
      (thetaCuspFullSource_pos_all _)).ne'
  unfold thetaCuspReflectedActionRiccatiChargeAtZero
    thetaCuspReflectedLogRiccatiMargin
    thetaCuspReflectedSourceDecayFluxThirdJet
    thetaCuspReflectedSourceDecayFlux
    thetaCuspReflectedSourceDecayFluxCurvature
  field_simp [hP]
  ring

/-- Fully raw source form of the charge.  Its growth is the center source-product square times a
negative flux Wronskian, divided by the fourth power of the current source product. -/
theorem thetaCuspReflectedActionRiccatiChargeAtZero_eq_rawSourceFluxWronskian
    (t : ℝ) :
    thetaCuspReflectedActionRiccatiChargeAtZero t =
      thetaCuspReflectedSourceProduct 0 0 ^ (2 : ℕ) /
          thetaCuspReflectedSourceProduct 0 t ^ (4 : ℕ) *
        (-(thetaCuspReflectedSourceProduct 0 t *
              thetaCuspReflectedSourceDecayFluxThirdJet 0 t +
            thetaCuspReflectedSourceDecayFlux 0 t *
              thetaCuspReflectedSourceDecayFluxCurvature 0 t)) := by
  have hP : 0 < thetaCuspReflectedSourceProduct 0 t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _)
      (thetaCuspFullSource_pos_all _)
  have hPzero : 0 < thetaCuspReflectedSourceProduct 0 0 := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _)
      (thetaCuspFullSource_pos_all _)
  have hratio :
      Real.exp (-thetaCuspReflectedLogAction 0 t) =
        thetaCuspReflectedSourceProduct 0 t /
          thetaCuspReflectedSourceProduct 0 0 := by
    simpa only [thetaCuspReflectedSourceProduct, zero_add, zero_sub, neg_zero,
      pow_two] using exp_neg_thetaCuspReflectedLogAction 0 t
  have hscaled :
      Real.exp (-thetaCuspReflectedLogAction 0 t) *
          thetaCuspReflectedSourceProduct 0 0 =
        thetaCuspReflectedSourceProduct 0 t :=
    (eq_div_iff hPzero.ne').mp hratio
  have hprod :
      Real.exp (thetaCuspReflectedLogAction 0 t) *
          thetaCuspReflectedSourceProduct 0 t =
        thetaCuspReflectedSourceProduct 0 0 := by
    rw [← hscaled]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hexp :
      Real.exp (2 * thetaCuspReflectedLogAction 0 t) =
        thetaCuspReflectedSourceProduct 0 0 ^ (2 : ℕ) /
          thetaCuspReflectedSourceProduct 0 t ^ (2 : ℕ) := by
    apply (eq_div_iff (sq_pos_of_pos hP).ne').2
    rw [show Real.exp (2 * thetaCuspReflectedLogAction 0 t) =
        Real.exp (thetaCuspReflectedLogAction 0 t) ^ (2 : ℕ) by
      rw [show 2 * thetaCuspReflectedLogAction 0 t =
          thetaCuspReflectedLogAction 0 t +
            thetaCuspReflectedLogAction 0 t by ring,
        Real.exp_add, pow_two]]
    nlinarith [sq_nonneg
      (Real.exp (thetaCuspReflectedLogAction 0 t) *
        thetaCuspReflectedSourceProduct 0 t -
          thetaCuspReflectedSourceProduct 0 0)]
  rw [thetaCuspReflectedActionRiccatiChargeAtZero_eq_fluxWronskian,
    hexp]
  field_simp [hP.ne']

/-- Strict source-coordinate survivor of charge positivity: endpoint flux acceleration and
curvature form a negative Wronskian current on every positive radius. -/
theorem thetaCuspReflectedSourceRiccatiFluxWronskianAtZero_neg
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceProduct 0 t *
          thetaCuspReflectedSourceDecayFluxThirdJet 0 t +
        thetaCuspReflectedSourceDecayFlux 0 t *
          thetaCuspReflectedSourceDecayFluxCurvature 0 t < 0 := by
  have hP : 0 < thetaCuspReflectedSourceProduct 0 t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _)
      (thetaCuspFullSource_pos_all _)
  have hcharge := thetaCuspReflectedActionRiccatiChargeAtZero_pos ht
  have heq := thetaCuspReflectedActionRiccatiChargeAtZero_eq_fluxWronskian t
  have hscaled :
      thetaCuspReflectedActionRiccatiChargeAtZero t *
          thetaCuspReflectedSourceProduct 0 t ^ (2 : ℕ) =
        Real.exp (2 * thetaCuspReflectedLogAction 0 t) *
          (-(thetaCuspReflectedSourceProduct 0 t *
              thetaCuspReflectedSourceDecayFluxThirdJet 0 t +
            thetaCuspReflectedSourceDecayFlux 0 t *
              thetaCuspReflectedSourceDecayFluxCurvature 0 t)) := by
    rw [heq]
    field_simp [hP.ne']
  have hleft : 0 <
      thetaCuspReflectedActionRiccatiChargeAtZero t *
        thetaCuspReflectedSourceProduct 0 t ^ (2 : ℕ) := by
    positivity
  by_contra hnot
  have hcurrent : 0 ≤
      thetaCuspReflectedSourceProduct 0 t *
          thetaCuspReflectedSourceDecayFluxThirdJet 0 t +
        thetaCuspReflectedSourceDecayFlux 0 t *
          thetaCuspReflectedSourceDecayFluxCurvature 0 t :=
    le_of_not_gt hnot
  have hright :
      Real.exp (2 * thetaCuspReflectedLogAction 0 t) *
          (-(thetaCuspReflectedSourceProduct 0 t *
              thetaCuspReflectedSourceDecayFluxThirdJet 0 t +
            thetaCuspReflectedSourceDecayFlux 0 t *
              thetaCuspReflectedSourceDecayFluxCurvature 0 t)) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (neg_nonpos.mpr hcurrent)
  linarith

/-- Exact conversion from normalized Riccati compensation to the source-charge envelope. -/
theorem thetaCuspReflectedActionRiccatiChargeEnvelopeGapAtZero_eq
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionRiccatiChargeEnvelopeGapAtZero t =
      -(thetaCuspReflectedActionRadiusAtZero t + 1) ^ (2 : ℕ) *
        thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t := by
  have hr := (thetaCuspReflectedActionRadiusAtZero_pos ht).ne'
  unfold thetaCuspReflectedActionRiccatiChargeEnvelopeGapAtZero
    thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero
  dsimp only
  rw [thetaCuspReflectedActionRiccatiChargeAtZero_eq_integratingFactor ht]
  field_simp [hr, ht.ne']
  ring

/-- The remaining modular-center C5 condition is exactly upper control of the literal source
Riccati charge by its stationary compensation envelope. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero_nonpos_iff_chargeEnvelope
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t ≤ 0 ↔
      0 ≤ thetaCuspReflectedActionRiccatiChargeEnvelopeGapAtZero t := by
  rw [thetaCuspReflectedActionRiccatiChargeEnvelopeGapAtZero_eq ht]
  have hf : 0 < (thetaCuspReflectedActionRadiusAtZero t + 1) ^ (2 : ℕ) := by
    have hr := thetaCuspReflectedActionRadiusAtZero_pos ht
    positivity
  rw [show -(thetaCuspReflectedActionRadiusAtZero t + 1) ^ (2 : ℕ) *
      thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t =
        -((thetaCuspReflectedActionRadiusAtZero t + 1) ^ (2 : ℕ) *
          thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t) by ring,
    neg_nonneg]
  constructor
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hf.le h
  · intro h
    by_contra hnot
    have hpos : 0 <
        thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero t :=
      lt_of_not_ge hnot
    exact (not_lt_of_ge h) (mul_pos hf hpos)

/-- Exact RH-chain interface for the charge coordinate.  Global modular-center source C5 is
equivalent to nonnegativity of the literal source-charge envelope only at negative intrinsic
minima.  Off-center transport, higher-packet positivity, and source-to-Weil no-escape remain
separate downstream joins. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_negativeIntrinsicMin_chargeEnvelope :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        IsLocalMin
          (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t →
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 →
        0 ≤ thetaCuspReflectedActionRiccatiChargeEnvelopeGapAtZero t := by
  rw [
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_negativeIntrinsicMin_riccatiBudget_nonpos]
  constructor
  · intro h t ht hmin hneg
    exact
      (thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero_nonpos_iff_chargeEnvelope
        ht).mp (h t ht hmin hneg)
  · intro h t ht hmin hneg
    exact
      (thetaCuspReflectedSourceFifthRootCurvatureRiccatiCompensationBudgetAtZero_nonpos_iff_chargeEnvelope
        ht).mpr (h t ht hmin hneg)

end

end RHTower
