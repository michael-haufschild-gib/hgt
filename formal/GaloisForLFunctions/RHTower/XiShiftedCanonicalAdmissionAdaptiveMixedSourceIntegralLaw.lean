import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceAction
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussRiccatiSource
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact integral law for adaptive mixed arithmetic source action

At physical mass `y`, the literal drift-removed adaptive mixed/completed `P^sharp` source is
formed at source coordinate `sqrt y`.  Inside any actual positive admission chamber it is
strictly positive and is exactly the derivative of negative cumulative Jacobi flux.

Positivity of this derivative supplies interval integrability without a separate continuity or
integrability premise.  The fundamental theorem of calculus then gives the exact path law

`integral_a^b J_n(sqrt y) dy = F_n(a) - F_n(b)`.

Thus literal arithmetic source action is the exact integral metric of adaptive flux.  On a complete
terminal chamber, Riccati positivity at the right endpoint makes every finite source expenditure
strictly smaller than current flux capital.  Exact weight-two dilation and fixed-degree recession
further show cumulative flux tends to zero.  Hence full right-tail source action is integrable and
equals current flux exactly.  No fixed reporter or reflection aggregate occurs.
-/

open Matrix Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators Interval

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Native mass-normalized literal source action is cumulative Jacobi dissipation divided by
forced trace multiplicity. -/
theorem massNormalizedSourceAction_eq_dissipation_div_degreeWeight
    {y : ℝ} (hy : 1 / 4 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction y n =
      xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y n /
        (2 * n + 1 : ℝ) := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy.le
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrt : 1 / 2 < Real.sqrt y := by
    have hsqrt0 := Real.sqrt_nonneg y
    nlinarith
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
        (n + 2)).PosDef
    simpa only [hsq] using hH
  rw [xiShiftedCanonicalAdmissionMassNormalizedAdaptiveMixedCompletedSourceAction,
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
      hsqrt hn hHsqrt, hsq]

/-- Cumulative flux is consumed by literal source action expressed directly in physical mass. -/
theorem hasDerivAt_flux_eq_neg_literalMassSourceAction
    {y : ℝ} (hy : 1 / 4 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionCumulativeJacobiFlux v n)
      (-xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n) y := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy.le
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrt : 1 / 2 < Real.sqrt y := by
    have hsqrt0 := Real.sqrt_nonneg y
    nlinarith
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
        (n + 2)).PosDef
    simpa only [hsq] using hH
  have h := hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_sourceAction
    hsqrt hn hHsqrt
  simpa only [hsq] using h

/-- Literal mass-coordinate adaptive mixed/completed source action is strictly positive. -/
theorem literalMassSourceAction_pos
    {y : ℝ} (hy : 1 / 4 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    0 < xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy.le
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrt : 1 / 2 < Real.sqrt y := by
    have hsqrt0 := Real.sqrt_nonneg y
    nlinarith
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
        (n + 2)).PosDef
    simpa only [hsq] using hH
  exact xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_pos hsqrt hn hHsqrt

/-- **Exact integral source law.**  Positivity automatically supplies integrability, and total
literal source action across a positive chamber equals endpoint cumulative-flux loss. -/
theorem integral_literalMassSourceAction_eq_flux_drop_of_posDef
    {a b : ℝ} (hab : a ≤ b) (ha : 1 / 4 < a) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (∫ y in a..b,
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n) =
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux a n -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux b n := by
  let F : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n
  let J : ℝ → ℝ := fun y =>
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n
  have hd : ∀ y ∈ Icc a b, HasDerivAt (fun v => -F v) (J y) y := by
    intro y hy
    have hyquarter : 1 / 4 < y := lt_of_lt_of_le ha hy.1
    have hflow := hasDerivAt_flux_eq_neg_literalMassSourceAction
      hyquarter hn (hH y hy)
    exact hflow.neg.congr_deriv (by simp only [neg_neg, J])
  have hcont : ContinuousOn (fun v => -F v) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  have hdIoo : ∀ y ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun v => -F v) (J y) y := by
    simp only [min_eq_left hab, max_eq_right hab]
    intro y hy
    exact hd y ⟨hy.1.le, hy.2.le⟩
  have hJnonneg : ∀ y ∈ Ioo (min a b) (max a b), 0 ≤ J y := by
    simp only [min_eq_left hab, max_eq_right hab]
    intro y hy
    exact (literalMassSourceAction_pos
      (lt_of_lt_of_le ha hy.1.le) hn (hH y ⟨hy.1.le, hy.2.le⟩)).le
  have hJint : IntervalIntegrable J volume a b :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont hdIoo hJnonneg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hd y (by simpa [uIcc_of_le hab] using hy)) hJint
  dsimp only [F, J] at hftc ⊢
  linarith

/-- **Integral Lipschitz equality.**  Absolute adaptive-flux motion is exactly literal source
path length; in particular, the corresponding integral Lipschitz inequality is sharp. -/
theorem abs_flux_drop_eq_literalMassSourceAction_integral
    {a b : ℝ} (hab : a ≤ b) (ha : 1 / 4 < a) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    |xiShiftedCanonicalAdmissionCumulativeJacobiFlux b n -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux a n| =
      ∫ y in a..b,
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n := by
  have heq := integral_literalMassSourceAction_eq_flux_drop_of_posDef hab ha hn hH
  have hnonneg : 0 ≤ ∫ y in a..b,
      xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n := by
    apply intervalIntegral.integral_nonneg hab
    intro y hy
    exact (literalMassSourceAction_pos
      (lt_of_lt_of_le ha hy.1) hn (hH y hy)).le
  rw [heq] at hnonneg ⊢
  rw [abs_of_nonpos]
  · ring
  · linarith

/-- **Terminal source-capital budget.**  On a complete terminal chamber, every finite future
source expenditure is strictly smaller than current positive cumulative flux. -/
theorem integral_literalMassSourceAction_lt_currentFlux_of_terminalChamber
    {A a b : ℝ} (hA : 1 / 4 ≤ A) (hAa : A < a) (hab : a ≤ b)
    {n : ℕ} (hn : 0 < n)
    (hchamber : ∀ y, A < y →
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    (∫ y in a..b,
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n) <
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux a n := by
  have ha : 1 / 4 < a := lt_of_le_of_lt hA hAa
  have hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
    intro y hy
    exact hchamber y (lt_of_lt_of_le hAa hy.1)
  have heq := integral_literalMassSourceAction_eq_flux_drop_of_posDef hab ha hn hH
  have hUb := xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_pos_of_terminalChamber
    (le_trans (by norm_num) hA) (lt_of_lt_of_le hAa hab) hn hchamber
  have hc : 0 < (2 * n + 1 : ℝ) := by positivity
  have hFb : 0 < xiShiftedCanonicalAdmissionCumulativeJacobiFlux b n := by
    rw [xiShiftedCanonicalAdmissionRenormalizedJacobiFlux] at hUb
    have hmul := mul_pos hUb hc
    field_simp [hc.ne'] at hmul
    exact hmul
  linarith

/-- Dimensionless cumulative flux has exact reciprocal-mass weight two. -/
theorem dimensionlessCumulativeJacobiFlux_eq_square_mul_actual
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 4)).PosDef) :
    dimensionlessCumulativeJacobiFlux w n =
      w ^ 2 * xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n := by
  have hsum := normalizedAlpha_sum_eq_square_mul_actualAlpha_sum hw n hN hA
  have hNn : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hAn : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 3)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have halpha := normalizedAlpha_eq_square_mul_actualAlpha hw n hNn hAn
  have hAtrace : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  rw [dimensionlessCumulativeJacobiFlux,
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hAtrace,
    hsum, halpha]
  ring

/-- Fixed-degree actual cumulative flux vanishes along square mass. -/
theorem tendsto_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_squareParam_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ => xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ 2) n)
      atTop (nhds 0) := by
  have hdim := tendsto_dimensionlessCumulativeJacobiFlux n
  have hinv : Tendsto (fun w : ℝ => (w ^ 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega : 2 ≠ 0))
  have hprod := hdim.mul hinv
  rw [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 4),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 4),
    eventually_gt_atTop (1 : ℝ)] with w hN0 hA hw
  have hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef := by
    simpa only [xiShiftedFarRightNormalizedHankelMatrix] using hN0
  have hscale := dimensionlessCumulativeJacobiFlux_eq_square_mul_actual hw hn hN hA
  rw [hscale]
  field_simp [ne_of_gt (lt_trans zero_lt_one hw)]

/-- Fixed-degree actual cumulative flux vanishes on the physical mass ray. -/
theorem tendsto_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n)
      atTop (nhds 0) := by
  have h :=
    (tendsto_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_squareParam_zero hn).comp
      Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simp only [Function.comp_apply, Real.sq_sqrt hy]

/-- **Exact full-tail source budget.**  If one fixed admission block remains positive on the
whole right ray from `a`, literal adaptive mixed/completed source is integrable there and its
entire remaining action equals current cumulative flux. -/
theorem integral_Ioi_literalMassSourceAction_eq_currentFlux
    {a : ℝ} (ha : 1 / 4 < a) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    IntegrableOn
        (fun y => xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
          (Real.sqrt y) n) (Ioi a) ∧
      (∫ y in Ioi a,
          xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n) =
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux a n := by
  let F : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n
  let J : ℝ → ℝ := fun y =>
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (Real.sqrt y) n
  have hd : ∀ y ∈ Ici a, HasDerivAt (fun v => -F v) (J y) y := by
    intro y hy
    have hyquarter : 1 / 4 < y := lt_of_lt_of_le ha hy
    have hflow := hasDerivAt_flux_eq_neg_literalMassSourceAction
      hyquarter hn (hH y hy)
    exact hflow.neg.congr_deriv (by simp only [neg_neg, J])
  have hJnonneg : ∀ y ∈ Ioi a, 0 ≤ J y := by
    intro y hy
    exact (literalMassSourceAction_pos
      (lt_trans ha hy) hn (hH y (show a ≤ y from hy.le))).le
  have hlim : Tendsto (fun y => -F y) atTop (nhds 0) := by
    simpa only [F, neg_zero] using
      (tendsto_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_zero hn).neg
  have hint : IntegrableOn J (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg' hd hJnonneg hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonneg' hd hJnonneg hlim
  refine ⟨hint, ?_⟩
  dsimp only [F, J] at heq ⊢
  linarith

end
end XiShiftedCanonicalAdmission
end RHTower
