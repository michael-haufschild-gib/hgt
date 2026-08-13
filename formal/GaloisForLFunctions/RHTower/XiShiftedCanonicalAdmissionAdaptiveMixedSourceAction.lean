import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveArithmeticSurplus

/-!
# Adaptive mixed/completed arithmetic source action

The literal adaptive mixed `P^sharp` source contains one intrinsic positive action after current
admission drift is removed.  If `F_n` is cumulative Jacobi flux, define

`J_n = source_n / h_n - alpha_n F_n - 2 n alpha_n^2`.

In every positive shifted-Xi chamber this source-first object is exactly cumulative Jacobi
dissipation.  Consequently

`F_n' = -J_n`,

and projective arithmetic surplus is its exact nonlinear capitalization

`Pi_n = (2n+1) J_n - F_n^2`.

After forced trace-multiplicity normalization `U_n = F_n/(2n+1)`, the literal source law becomes

`U_n' = -U_n^2 - Pi_n/(2n+1)^2`.

Degree renewal and mass transport also form one exact plaquette: the adjacent degree edge is
`F_(n+1)-F_n = alpha_n+alpha_(n+1)`, while its mass derivative is `J_n-J_(n+1)`.
Thus the producer is an admission-sensitive nonlinear arithmetic action formed before reflection
aggregation, not an orientation map or fixed linear reporter.
-/

open Matrix Polynomial
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Literal adaptive mixed/completed source after removing its endogenous current-alpha drift.
Admission, source formation, and norm normalization all occur before this subtraction. -/
noncomputable def xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
    (w : ℝ) (n : ℕ) : ℝ :=
  let s := xiShiftedRealMomentSequence w
  let alpha := HTGeometry.monicOrthoAlpha s n
  let F := xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n
  let h := HTGeometry.monicOrthoNormSq s n
  let source := xiShiftedAdaptiveMixedCompletedArithmeticSource w
    (HTGeometry.monicMomentAdmissionPolynomial s n)
  source / h - alpha * F - 2 * (n : ℝ) * alpha ^ 2

/-- Projective surplus is exactly degree weight times literal source action minus squared flux.
This identity is division-free in the projective variables. -/
theorem xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_degreeWeight_mul_sourceAction_sub_flux_sq
    (w : ℝ) (n : ℕ) :
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n =
      (2 * n + 1 : ℝ) *
          xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w n -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n ^ 2 := by
  rfl

/-- **Exact arithmetic source law.**  In a positive block, the drift-removed literal completed
`P^sharp` source is precisely cumulative Jacobi dissipation. -/
theorem xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w n =
      xiShiftedCanonicalAdmissionCumulativeJacobiDissipation (w ^ 2) n := by
  have hsurplus :=
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_cauchyGap hw hn hH
  rw [xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_degreeWeight_mul_sourceAction_sub_flux_sq]
    at hsurplus
  have hc : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  nlinarith

/-- The actual adaptive mixed/completed source action is strictly positive in every positive
admission block. -/
theorem xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w n := by
  rw [xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
    hw hn hH]
  exact xiShiftedCanonicalAdmissionCumulativeJacobiDissipation_pos hn hH

/-- **Source-action flow.**  Cumulative Jacobi flux is consumed at exactly the rate of the
drift-removed literal adaptive completed source. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_sourceAction
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    HasDerivAt
      (fun y => xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n)
      (-xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w n) (w ^ 2) := by
  rw [xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
    hw hn hH]
  exact hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
    (sq_pos_of_pos (lt_trans (by norm_num) hw)) hn hH

/-- Source action splits exactly into Riccati transport plus strict literal projective surplus
after forced trace-multiplicity normalization. -/
theorem xiShiftedCanonicalAdmissionSourceAction_div_degreeWeight_eq_renormalizedFlux_sq_add_surplus
    (w : ℝ) (n : ℕ) :
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w n /
        (2 * n + 1 : ℝ) =
      xiShiftedCanonicalAdmissionRenormalizedJacobiFlux (w ^ 2) n ^ 2 +
        xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n /
          (2 * n + 1 : ℝ) ^ 2 := by
  have hc : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  rw [xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_degreeWeight_mul_sourceAction_sub_flux_sq]
  unfold xiShiftedCanonicalAdmissionRenormalizedJacobiFlux
  field_simp [hc]
  ring

/-- Literal projective arithmetic surplus is the exact nonlinear Riccati defect of current flux. -/
theorem xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_neg_degreeWeight_mul_deriv_sub_flux_sq
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n =
      -(2 * n + 1 : ℝ) *
          deriv (fun y => xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n) (w ^ 2) -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n ^ 2 := by
  rw [xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_cauchyGap hw hn hH,
    (hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
      (sq_pos_of_pos (lt_trans (by norm_num) hw)) hn hH).deriv]
  ring

/-- **Normalized nonlinear arithmetic source law.**  The completed source surplus is the exact
strict correction to universal Riccati contraction. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_eq_neg_sq_sub_literalSurplus
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    HasDerivAt
      (fun y => xiShiftedCanonicalAdmissionRenormalizedJacobiFlux y n)
      (-xiShiftedCanonicalAdmissionRenormalizedJacobiFlux (w ^ 2) n ^ 2 -
        xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n /
          (2 * n + 1 : ℝ) ^ 2) (w ^ 2) := by
  let c : ℝ := (2 * n + 1 : ℝ)
  have hc : c ≠ 0 := by positivity
  have hflux :=
    (hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
      (sq_pos_of_pos (lt_trans (by norm_num) hw)) hn hH).div_const c
  apply hflux.congr_deriv
  have hsource :=
    xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_neg_degreeWeight_mul_deriv_sub_flux_sq
      hw hn hH
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux
      (sq_pos_of_pos (lt_trans (by norm_num) hw)) hn hH).deriv] at hsource
  dsimp only [xiShiftedCanonicalAdmissionRenormalizedJacobiFlux, c] at hflux ⊢
  field_simp [hc]
  nlinarith

/-- Adjacent admission changes cumulative flux by exactly the two endpoint diagonals. -/
theorem xiShiftedCanonicalAdmissionCumulativeJacobiFlux_succ_sub_eq_adjacentAlpha
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) (n + 1) -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n =
      HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) n +
        HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) (n + 1) := by
  have hHn : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  change xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) (n + 1) -
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n =
    HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n +
      HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 1)
  rw [xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace (by omega) hH,
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hHn,
    Finset.sum_range_succ]
  ring

/-- **Degree--mass source plaquette.**  Mass derivative of adjacent degree edge is exactly the
difference of current and newborn literal source actions. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_degreeEdge_eq_sourceActionDifference
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    HasDerivAt
      (fun y => xiShiftedCanonicalAdmissionCumulativeJacobiFlux y (n + 1) -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n)
      (xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w n -
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 1))
      (w ^ 2) := by
  have hHn : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hnext :=
    hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_sourceAction
      hw (by omega) hH
  have hcurrent :=
    hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_sourceAction
      hw hn hHn
  exact (hnext.sub hcurrent).congr_deriv (by ring)

/-- Literal strict projective surplus per forced squared trace multiplicity, expressed in mass
coordinates. -/
noncomputable def xiShiftedCanonicalAdmissionNormalizedProjectiveSurplusDensity
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus (Real.sqrt y) n /
    (2 * n + 1 : ℝ) ^ 2

/-- Total normalized literal source action in mass coordinates. -/
noncomputable def xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n /
    (2 * n + 1 : ℝ)

/-- Square-mass specialization of normalized literal projective surplus. -/
theorem xiShiftedCanonicalAdmissionNormalizedProjectiveSurplusDensity_sq
    {w : ℝ} (hw : 0 < w) (n : ℕ) :
    xiShiftedCanonicalAdmissionNormalizedProjectiveSurplusDensity (w ^ 2) n =
      xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus w n /
        (2 * n + 1 : ℝ) ^ 2 := by
  rw [xiShiftedCanonicalAdmissionNormalizedProjectiveSurplusDensity,
    Real.sqrt_sq_eq_abs, abs_of_pos hw]

/-- Total normalized source action is Riccati transport plus strict literal surplus. -/
theorem xiShiftedCanonicalAdmissionMassNormalizedSourceAction_eq_flux_sq_add_surplus
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction y n =
      xiShiftedCanonicalAdmissionRenormalizedJacobiFlux y n ^ 2 +
        xiShiftedCanonicalAdmissionNormalizedProjectiveSurplusDensity y n := by
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have h :=
    xiShiftedCanonicalAdmissionSourceAction_div_degreeWeight_eq_renormalizedFlux_sq_add_surplus
      (Real.sqrt y) n
  rw [hsq] at h
  simpa only [xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction,
    xiShiftedCanonicalAdmissionNormalizedProjectiveSurplusDensity] using h

/-- Native mass-coordinate form of the exact adaptive mixed/completed source action law. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_eq_neg_massSourceAction
    {y : ℝ} (hy : 1 / 4 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionRenormalizedJacobiFlux v n)
      (-xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction y n) y := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy.le
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrt0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hw : 1 / 2 < Real.sqrt y := by nlinarith
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
        (n + 2)).PosDef
    simpa only [hsq] using hH
  have h :=
    (hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_sourceAction
      hw hn hHsqrt).div_const (2 * n + 1 : ℝ)
  rw [hsq] at h
  have hderiv :
      -xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n /
          (2 * n + 1 : ℝ) =
        -(xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n /
          (2 * n + 1 : ℝ)) := by ring
  rw [hderiv] at h
  simpa only [xiShiftedCanonicalAdmissionRenormalizedJacobiFlux,
    xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction] using h

/-- Native mass-coordinate source action is strictly positive in every positive physical block. -/
theorem xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction_pos
    {y : ℝ} (hy : 1 / 4 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction y n := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy.le
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrt0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hw : 1 / 2 < Real.sqrt y := by nlinarith
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
        (n + 2)).PosDef
    simpa only [hsq] using hH
  exact div_pos
    (xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_pos hw hn hHsqrt)
    (by positivity)

/-- Native mass-coordinate projective surplus density is strictly positive. -/
theorem xiShiftedCanonicalAdmissionNormalizedProjectiveSurplusDensity_pos
    {y : ℝ} (hy : 1 / 4 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionNormalizedProjectiveSurplusDensity y n := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy.le
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrt0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hw : 1 / 2 < Real.sqrt y := by nlinarith
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
        (n + 2)).PosDef
    simpa only [hsq] using hH
  apply div_pos
    (xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_pos hw hn hHsqrt)
  positivity

end
end XiShiftedCanonicalAdmission
end RHTower
