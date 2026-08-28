import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceCumulativeFluxBalance

open Set

namespace RHTower

noncomputable section

/-!
# Intrinsic-action velocity form of the completed-theta C5 wall

For reflected log action `q`, put `v = t q'` and use `q` itself as intrinsic time.  Since
`q' > 0` at positive displacement, the intrinsic velocity slope is

`w = dv/dq = (q' + t q'') / q'`.

The cumulative endpoint ratio and normalized flux elasticity become

`m = v / (2 (exp q - 1))`,

`e = (w - v - 2) / 2`.

Consequently the remaining C5 sign is exactly the first-order action-flow barrier

`0 <= 24r + 5vw - 14v - 5v^2 - 4v^2/r`,

where `r = exp q - 1 > 0`.  This removes the displacement second jet as an independent
coordinate.  Any fixed-action centre transport must control one velocity field and its intrinsic
derivative, rather than the earlier cumulative/local pair `(m,e)` separately.
-/

/-- Log action accumulated per logarithmic displacement. -/
def thetaCuspReflectedActionVelocity (u t : ℝ) : ℝ :=
  t * thetaCuspReflectedLogJetOne u t

/-- Intrinsic-action slope of the action velocity. -/
def thetaCuspReflectedActionVelocitySlope (u t : ℝ) : ℝ :=
  (thetaCuspReflectedLogJetOne u t +
      t * thetaCuspReflectedLogJetTwo u t) /
    thetaCuspReflectedLogJetOne u t

/-- C5 in intrinsic action-flow coordinates. -/
def thetaCuspReflectedActionVelocityC5Balance (u t : ℝ) : ℝ :=
  let r := Real.exp (thetaCuspReflectedLogAction u t) - 1
  let v := thetaCuspReflectedActionVelocity u t
  let w := thetaCuspReflectedActionVelocitySlope u t
  6 - v / r - v ^ 2 / r ^ 2 + 5 * v * (w - v - 2) / (4 * r)

/-- Division-free first-order action-flow barrier for C5. -/
def thetaCuspReflectedActionVelocityC5Barrier (u t : ℝ) : ℝ :=
  let r := Real.exp (thetaCuspReflectedLogAction u t) - 1
  let v := thetaCuspReflectedActionVelocity u t
  let w := thetaCuspReflectedActionVelocitySlope u t
  24 * r + 5 * v * w - 14 * v - 5 * v ^ 2 - 4 * v ^ 2 / r

/-- Universal C5 barrier at one positive intrinsic action radius. -/
def thetaCuspActionVelocityBarrier (r v w : ℝ) : ℝ :=
  24 * r + 5 * v * w - 14 * v - 5 * v ^ 2 - 4 * v ^ 2 / r

theorem thetaCuspReflectedActionVelocityC5Barrier_eq_universal (u t : ℝ) :
    thetaCuspReflectedActionVelocityC5Barrier u t =
      thetaCuspActionVelocityBarrier
        (Real.exp (thetaCuspReflectedLogAction u t) - 1)
        (thetaCuspReflectedActionVelocity u t)
        (thetaCuspReflectedActionVelocitySlope u t) := by
  rfl

/-- Exact centre derivative of the velocity barrier while its action radius is held fixed. -/
theorem hasDerivAt_thetaCuspActionVelocityBarrier_fixedRadius
    {V W : ℝ → ℝ} {x r : ℝ}
    (hr : r ≠ 0) (hV : HasDerivAt V (deriv V x) x)
    (hW : HasDerivAt W (deriv W x) x) :
    HasDerivAt (fun y => thetaCuspActionVelocityBarrier r (V y) (W y))
      (5 * (V x * deriv W x + W x * deriv V x) -
        (14 + 10 * V x + 8 * V x / r) * deriv V x) x := by
  have hraw :=
    (((((hasDerivAt_const x (24 * r)).add ((hV.mul hW).const_mul 5)).sub
      (hV.const_mul 14)).sub ((hV.pow 2).const_mul 5)).sub
      ((hV.pow 2).const_mul 4 |>.div_const r))
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold thetaCuspActionVelocityBarrier
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · field_simp [hr]
    ring

/-- Negative centre transport and nonnegative transport-current growth force the barrier
derivative to be nonnegative. -/
theorem thetaCuspActionVelocityBarrier_fixedRadius_derivative_nonneg
    {r v w h k : ℝ} (hr : 0 < r) (hv : 0 ≤ v) (hh : h ≤ 0)
    (hcurrent : 0 ≤ v * k + w * h) :
    0 ≤ 5 * (v * k + w * h) - (14 + 10 * v + 8 * v / r) * h := by
  have hvdiv : 0 ≤ v / r := div_nonneg hv hr.le
  have hcoef : 0 ≤ 14 + 10 * v + 8 * v / r := by positivity
  have htransport : 0 ≤ -(14 + 10 * v + 8 * v / r) * h := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef hh]
  nlinarith

/-- Displacement derivative of the action velocity. -/
theorem hasDerivAt_thetaCuspReflectedActionVelocity (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedActionVelocity u)
      (thetaCuspReflectedLogJetOne u t +
        t * thetaCuspReflectedLogJetTwo u t) t := by
  change HasDerivAt (fun s : ℝ => s * thetaCuspReflectedLogJetOne u s)
    (thetaCuspReflectedLogJetOne u t +
      t * thetaCuspReflectedLogJetTwo u t) t
  have hraw :=
    (hasDerivAt_id t).mul (hasDerivAt_thetaCuspReflectedLogJetOne u t)
  have hfun : id * thetaCuspReflectedLogJetOne u =
      fun s : ℝ => s * thetaCuspReflectedLogJetOne u s := by
    funext s
    rfl
  rw [hfun] at hraw
  simpa only [one_mul, id_eq] using hraw

/-- The named slope is literally `dv/dq`. -/
theorem thetaCuspReflectedActionVelocitySlope_eq_deriv_div (u t : ℝ) :
    thetaCuspReflectedActionVelocitySlope u t =
      deriv (thetaCuspReflectedActionVelocity u) t /
        deriv (thetaCuspReflectedLogAction u) t := by
  rw [(hasDerivAt_thetaCuspReflectedActionVelocity u t).deriv,
    (hasDerivAt_thetaCuspReflectedLogAction u t).deriv]
  rfl

/-- Endpoint mass is action velocity divided by twice the exponential action drop. -/
theorem thetaCuspReflectedSourceCumulativeEndpointFluxRatio_eq_actionVelocity
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t =
      thetaCuspReflectedActionVelocity u t /
        (2 * (Real.exp (thetaCuspReflectedLogAction u t) - 1)) := by
  have hP : 0 < thetaCuspReflectedSourceProduct u t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hr : 0 < Real.exp (thetaCuspReflectedLogAction u t) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht)
  unfold thetaCuspReflectedSourceCumulativeEndpointFluxRatio
    thetaCuspReflectedSourceDecayFlux thetaCuspReflectedActionVelocity
  rw [thetaCuspReflectedSourceFirstDrop_eq_product_mul_exp_action_sub_one]
  field_simp [hP.ne', hr.ne']

/-- Flux elasticity is half the excess of intrinsic velocity slope over `v+2`. -/
theorem thetaCuspReflectedSourceNormalizedFluxElasticity_eq_actionVelocitySlope
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceNormalizedFluxElasticity u t =
      (thetaCuspReflectedActionVelocitySlope u t -
        thetaCuspReflectedActionVelocity u t - 2) / 2 := by
  have hP : 0 < thetaCuspReflectedSourceProduct u t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hq₁ := thetaCuspReflectedLogJetOne_pos u ht
  unfold thetaCuspReflectedSourceNormalizedFluxElasticity
    thetaCuspReflectedSourceDecayFluxCurvature
    thetaCuspReflectedSourceDecayFlux
    thetaCuspReflectedActionVelocitySlope thetaCuspReflectedActionVelocity
  field_simp [hP.ne', hq₁.ne']
  ring

/-- The cumulative C5 balance is exactly its intrinsic action-flow expression. -/
theorem thetaCuspReflectedSourceCumulativeFluxC5Balance_eq_actionVelocity
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceCumulativeFluxC5Balance u t =
      thetaCuspReflectedActionVelocityC5Balance u t := by
  rw [show thetaCuspReflectedSourceCumulativeFluxC5Balance u t =
      6 - 2 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t -
        4 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t ^ 2 +
        5 * thetaCuspReflectedSourceCumulativeEndpointFluxRatio u t *
          thetaCuspReflectedSourceNormalizedFluxElasticity u t by rfl,
    thetaCuspReflectedSourceCumulativeEndpointFluxRatio_eq_actionVelocity u ht,
    thetaCuspReflectedSourceNormalizedFluxElasticity_eq_actionVelocitySlope u ht]
  unfold thetaCuspReflectedActionVelocityC5Balance
  have hr : Real.exp (thetaCuspReflectedLogAction u t) - 1 ≠ 0 := by
    have hq := thetaCuspReflectedLogAction_pos (u := u) ht
    exact sub_ne_zero.mpr (ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hq))
  field_simp [hr]
  ring

/-- Exact first-order intrinsic-action normal form of the action C5 numerator. -/
theorem thetaCuspReflectedActionFifthRootCurvatureNumerator_eq_actionVelocityBarrier
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionFifthRootCurvatureNumerator u t =
      (Real.exp (thetaCuspReflectedLogAction u t) - 1) *
        thetaCuspReflectedActionVelocityC5Barrier u t := by
  have hq₁ := thetaCuspReflectedLogJetOne_pos u ht
  have hr : Real.exp (thetaCuspReflectedLogAction u t) - 1 ≠ 0 := by
    have hq := thetaCuspReflectedLogAction_pos (u := u) ht
    exact sub_ne_zero.mpr (ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hq))
  unfold thetaCuspReflectedActionFifthRootCurvatureNumerator
    thetaCuspReflectedActionVelocityC5Barrier
    thetaCuspReflectedActionVelocity thetaCuspReflectedActionVelocitySlope
  dsimp only
  field_simp [hq₁.ne', hr]
  ring

/-- C5 is equivalent to the first-order intrinsic action-flow barrier. -/
theorem thetaCuspReflectedActionFifthRootCurvatureNumerator_nonneg_iff_actionVelocityBarrier
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ thetaCuspReflectedActionFifthRootCurvatureNumerator u t ↔
      0 ≤ thetaCuspReflectedActionVelocityC5Barrier u t := by
  rw [thetaCuspReflectedActionFifthRootCurvatureNumerator_eq_actionVelocityBarrier u ht]
  have hr : 0 < Real.exp (thetaCuspReflectedLogAction u t) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := u) ht)
  exact mul_nonneg_iff_of_pos_left hr

end

end RHTower
