import GaloisForLFunctions.HTGeometry.FixedActionC5JacobianGermAnalyticClosure
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5JacobianSeamOrientation
import Mathlib.Analysis.Calculus.Taylor

/-!
# Direct fixed-action C5 Jacobian germ closure for the theta cusp source

This module identifies the actual centre derivative of the direct fixed-action C5 Jacobian with
the universal division-free germ, proves its first nonzero derivative is the positive ninth jet,
and transports that strict sign to a punctured right neighbourhood of the collapsed seam.
-/

open scoped BigOperators ContDiff
open Set Filter Topology

namespace RHTower

noncomputable section

/-- Squared-radius regularization of the direct fixed-action C5 centre Jacobian derivative. -/
def thetaCuspC5FixedActionJacobianCenterRegularizedGerm (t : ℝ) : ℝ :=
  HTGeometry.c5FixedActionRegularizedCenterExpression
    (-iteratedDeriv 2 thetaCuspLogSource 0)
    (thetaCuspReflectedLogAction 0) t

theorem contDiff_thetaCuspReflectedLogAction_zero :
    ContDiff ℝ ∞ (thetaCuspReflectedLogAction 0) := by
  have hfun : thetaCuspReflectedLogAction 0 = fun t =>
      2 * thetaCuspLogSource 0 - 2 * thetaCuspLogSource t := by
    funext t
    unfold thetaCuspReflectedLogAction
    rw [zero_add, zero_sub, thetaCuspLogSource_neg]
    ring
  rw [hfun]
  exact contDiff_const.sub (contDiff_const.mul contDiff_thetaCuspLogSource)

private theorem iteratedDeriv_succ_thetaCuspReflectedLogAction_zero
    (n : ℕ) :
    iteratedDeriv (n + 1) (thetaCuspReflectedLogAction 0) 0 =
      -2 * iteratedDeriv (n + 1) thetaCuspLogSource 0 := by
  have hfun : thetaCuspReflectedLogAction 0 = fun t =>
      2 * thetaCuspLogSource 0 - 2 * thetaCuspLogSource t := by
    funext t
    unfold thetaCuspReflectedLogAction
    rw [zero_add, zero_sub, thetaCuspLogSource_neg]
    ring
  rw [hfun]
  change iteratedDeriv (n + 1)
    ((fun _ : ℝ => 2 * thetaCuspLogSource 0) -
      (fun t => 2 * thetaCuspLogSource t)) 0 = _
  have hc : ContDiffAt ℝ (n + 1)
      (fun _ : ℝ => 2 * thetaCuspLogSource 0) 0 := contDiffAt_const
  have hsource : ContDiffAt ℝ (n + 1) thetaCuspLogSource 0 :=
    contDiff_thetaCuspLogSource.contDiffAt.of_le
      (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))
  have hs : ContDiffAt ℝ (n + 1)
      (fun t => 2 * thetaCuspLogSource t) 0 :=
    contDiffAt_const.mul hsource
  rw [iteratedDeriv_sub hc hs]
  rw [iteratedDeriv_const]
  rw [iteratedDeriv_const_mul 2 hsource]
  simp

theorem thetaCuspC5FixedActionJacobianCenterRegularizedGerm_jets :
    (∀ n < 9,
      iteratedDeriv n thetaCuspC5FixedActionJacobianCenterRegularizedGerm 0 = 0) ∧
    iteratedDeriv 9 thetaCuspC5FixedActionJacobianCenterRegularizedGerm 0 =
      20160 * thetaCuspC5FixedActionSeamLogValue := by
  let A := -iteratedDeriv 2 thetaCuspLogSource 0
  let B := -iteratedDeriv 4 thetaCuspLogSource 0
  let C := -iteratedDeriv 6 thetaCuspLogSource 0
  let D := -iteratedDeriv 8 thetaCuspLogSource 0
  let q : ℝ → ℝ := thetaCuspReflectedLogAction 0
  let e : ℝ → ℝ := fun t => Real.exp (q t)
  let jq : ℕ → ℝ := fun n => iteratedDeriv n q 0
  let je : ℕ → ℝ := fun n => iteratedDeriv n e 0
  have hq1 : jq 1 = 0 := by
    rw [show (1 : ℕ) = 0 + 1 by omega]
    simp only [jq, q, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    rw [iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 1 by norm_num)]
    ring
  have hq2 : jq 2 = 2 * A := by
    rw [show (2 : ℕ) = 1 + 1 by omega]
    simp only [jq, q, A, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    ring
  have hq3 : jq 3 = 0 := by
    rw [show (3 : ℕ) = 2 + 1 by omega]
    simp only [jq, q, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    rw [iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 by norm_num)]
    ring
  have hq4 : jq 4 = 2 * B := by
    rw [show (4 : ℕ) = 3 + 1 by omega]
    simp only [jq, q, B, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    ring
  have hq5 : jq 5 = 0 := by
    rw [show (5 : ℕ) = 4 + 1 by omega]
    simp only [jq, q, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    rw [iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 by norm_num)]
    ring
  have hq6 : jq 6 = 2 * C := by
    rw [show (6 : ℕ) = 5 + 1 by omega]
    simp only [jq, q, C, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    ring
  have hq7 : jq 7 = 0 := by
    rw [show (7 : ℕ) = 6 + 1 by omega]
    simp only [jq, q, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    rw [iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 7 by norm_num)]
    ring
  have hq8 : jq 8 = 2 * D := by
    rw [show (8 : ℕ) = 7 + 1 by omega]
    simp only [jq, q, D, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    ring
  have hq9 : jq 9 = 0 := by
    rw [show (9 : ℕ) = 8 + 1 by omega]
    simp only [jq, q, iteratedDeriv_succ_thetaCuspReflectedLogAction_zero]
    rw [iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 9 by norm_num)]
    ring
  have hq0 : q 0 = 0 := by
    simp only [q, thetaCuspReflectedLogAction, zero_add, zero_sub]
    ring_nf
  have he0 : je 0 = 1 := by
    simp [je, e, iteratedDeriv_zero, hq0]
  have hqc : ContDiff ℝ ∞ q := by
    simpa only [q] using contDiff_thetaCuspReflectedLogAction_zero
  have hec : ContDiff ℝ ∞ e := by simpa only [e] using hqc.exp
  have hderiv : deriv e = fun t => e t * iteratedDeriv 1 q t := by
    funext t
    have hqt : HasDerivAt q (deriv q t) t :=
      (hqc.differentiable (by simp)).differentiableAt.hasDerivAt
    have het := hqt.exp
    rw [het.deriv]
    simp [e, iteratedDeriv_succ, iteratedDeriv_zero]
  have herec (n : ℕ) : je (n + 1) =
      HTGeometry.realScalarJetConvolution je (fun k => jq (k + 1)) n := by
    simp only [je, jq]
    rw [iteratedDeriv_succ']
    rw [hderiv]
    have haqc : ContDiff ℝ ∞ (iteratedDeriv 1 q) := by
      rw [show iteratedDeriv 1 q = deriv q by
        rw [show (1 : ℕ) = 0 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_zero]]
      exact hqc.deriv'
    change iteratedDeriv n (e * iteratedDeriv 1 q) 0 = _
    rw [HTGeometry.iteratedDeriv_mul_eq_realScalarJetConvolution
      (hec.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (haqc.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    unfold HTGeometry.realScalarJetConvolution
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    change iteratedDeriv (n - i) (iteratedDeriv 1 q) 0 =
      iteratedDeriv ((n - i) + 1) q 0
    simpa [Nat.add_comm] using
      congrFun (HTGeometry.iteratedDeriv_iteratedDeriv_real q 1 (n - i)) 0
  have halg := HTGeometry.c5FixedActionRegularizedCenterJet_elimination
    A B C D jq je hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 hq9 he0 herec
  have han (n : ℕ) :=
    HTGeometry.iteratedDeriv_c5FixedActionRegularizedCenterExpression A q hqc n
  constructor
  · intro n hn
    change iteratedDeriv n
      (HTGeometry.c5FixedActionRegularizedCenterExpression A q) 0 = 0
    rw [han n]
    exact halg.1 n hn
  · change iteratedDeriv 9
      (HTGeometry.c5FixedActionRegularizedCenterExpression A q) 0 = _
    rw [han 9]
    simpa [thetaCuspC5FixedActionSeamLogValue, A, B, C, D] using halg.2

theorem thetaCuspC5FixedActionJacobianCenterRegularizedGerm_ninth_pos :
    0 < iteratedDeriv 9 thetaCuspC5FixedActionJacobianCenterRegularizedGerm 0 := by
  rw [thetaCuspC5FixedActionJacobianCenterRegularizedGerm_jets.2]
  exact mul_pos (by norm_num) thetaCuspC5FixedActionSeamLogValue_pos

/-- Fourth logarithmic source jet in curvature sign convention. -/
def thetaCuspLogCurvatureJetTwo (x : ℝ) : ℝ :=
  -iteratedDeriv 4 thetaCuspLogSource x

/-- Fourth displacement jet of reflected logarithmic action. -/
private def thetaCuspReflectedLogJetFour (u t : ℝ) : ℝ :=
  thetaCuspLogCurvatureJetTwo (u + t) +
    thetaCuspLogCurvatureJetTwo (u - t)

/-- Centre derivative of the centre-mixed third jet. -/
def thetaCuspReflectedLogCenterMixedJetFour (u t : ℝ) : ℝ :=
  thetaCuspLogCurvatureJetTwo (u + t) +
    thetaCuspLogCurvatureJetTwo (u - t)

theorem hasDerivAt_thetaCuspLogCurvatureJet
    (x : ℝ) :
    HasDerivAt thetaCuspLogCurvatureJet
      (thetaCuspLogCurvatureJetTwo x) x := by
  unfold thetaCuspLogCurvatureJet thetaCuspLogCurvatureJetTwo
  convert (hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x).neg using 1
  all_goals rfl

private theorem hasDerivAt_thetaCuspReflectedLogJetThree
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogJetThree u)
      (thetaCuspReflectedLogJetFour u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u + t)).comp t
    ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u - t)).comp t
    ((hasDerivAt_id t).const_sub u)
  convert hp.sub hm using 1
  all_goals first | rfl | simp [thetaCuspReflectedLogJetFour]

theorem hasDerivAt_thetaCuspReflectedLogCenterMixedJetThree
    (u t : ℝ) :
    HasDerivAt (fun x => thetaCuspReflectedLogCenterMixedJetThree x t)
      (thetaCuspReflectedLogCenterMixedJetFour u t) u := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u + t)).comp u
    ((hasDerivAt_id u).add_const t)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u - t)).comp u
    ((hasDerivAt_id u).sub_const t)
  convert hp.add hm using 1
  all_goals first | rfl | simp [thetaCuspReflectedLogCenterMixedJetFour]

private theorem thetaCuspReflectedLogCenterJetOne_zero_center (t : ℝ) :
    thetaCuspReflectedLogCenterJetOne 0 t = 0 := by
  have hs0 : thetaCuspLogDecaySlope 0 = 0 := by
    have h := thetaCuspLogDecaySlope_neg 0
    norm_num at h
    linarith
  unfold thetaCuspReflectedLogCenterJetOne
  rw [zero_add, zero_sub, thetaCuspLogDecaySlope_neg, hs0]
  ring

private theorem thetaCuspReflectedLogCenterMixedJetOne_zero_center (t : ℝ) :
    thetaCuspReflectedLogCenterMixedJetOne 0 t = 0 := by
  unfold thetaCuspReflectedLogCenterMixedJetOne
  rw [zero_add, zero_sub, thetaCuspLogCurvature_neg]
  ring

private theorem thetaCuspReflectedLogCenterMixedJetThree_zero_center (t : ℝ) :
    thetaCuspReflectedLogCenterMixedJetThree 0 t = 0 := by
  unfold thetaCuspReflectedLogCenterMixedJetThree
  rw [zero_add, zero_sub, thetaCuspLogCurvatureJet_neg]
  ring

private theorem thetaCuspReflectedLogCenterJetTwo_zero_eq (t : ℝ) :
    thetaCuspReflectedLogCenterJetTwo 0 t =
      thetaCuspReflectedLogJetTwo 0 t -
        2 * (-iteratedDeriv 2 thetaCuspLogSource 0) := by
  unfold thetaCuspReflectedLogCenterJetTwo thetaCuspReflectedLogJetTwo
    thetaCuspLogCurvature
  rw [zero_add, zero_sub]

private theorem thetaCuspReflectedLogCenterMixedJetTwo_zero_eq (t : ℝ) :
    thetaCuspReflectedLogCenterMixedJetTwo 0 t =
      thetaCuspReflectedLogJetThree 0 t := by
  unfold thetaCuspReflectedLogCenterMixedJetTwo thetaCuspReflectedLogJetThree
  rw [zero_add, zero_sub]

private theorem thetaCuspReflectedLogCenterMixedJetFour_zero_eq (t : ℝ) :
    thetaCuspReflectedLogCenterMixedJetFour 0 t =
      thetaCuspReflectedLogJetFour 0 t := by
  rfl

theorem hasDerivAt_thetaCuspReflectedActionC5FixedActionJacobian_center_zero
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => thetaCuspReflectedActionC5FixedActionJacobian u t)
      (let a := thetaCuspReflectedLogJetOne 0 t
       let b := thetaCuspReflectedLogJetTwo 0 t
       let c := thetaCuspReflectedLogJetThree 0 t
       let d := thetaCuspReflectedLogJetFour 0 t
       let h := b - 2 * (-iteratedDeriv 2 thetaCuspLogSource 0)
       let p1 := thetaCuspReflectedActionC5PartialJetOne 0 t
       let p2 := thetaCuspReflectedActionC5PartialJetTwo 0 t
       let pd := thetaCuspReflectedActionC5PartialDisplacement 0 t
       a * (p1 * c + p2 * d) - h * (pd + p1 * b + p2 * c)) 0 := by
  have hR : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedActionInverseRadius u t) 0 :=
    (hasDerivAt_thetaCuspReflectedActionInverseRadius_center 0 ht).differentiableAt
  have hqa : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedLogJetOne u t) 0 :=
    (hasDerivAt_thetaCuspReflectedLogJetOne_center 0 t).differentiableAt
  have hqb : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedLogJetTwo u t) 0 :=
    (hasDerivAt_thetaCuspReflectedLogJetTwo_center 0 t).differentiableAt
  have hq3 : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedLogJetThree u t) 0 := by
    have hp := (hasDerivAt_thetaCuspLogCurvatureJet (0 + t)).comp 0
      ((hasDerivAt_id 0).add_const t)
    have hm := (hasDerivAt_thetaCuspLogCurvatureJet (0 - t)).comp 0
      ((hasDerivAt_id 0).sub_const t)
    have hraw := hp.sub hm
    exact (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => rfl)).differentiableAt
  have hpA : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedActionC5PartialAction u t) 0 := by
    unfold thetaCuspReflectedActionC5PartialAction
    dsimp only
    fun_prop
  have hp1 : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedActionC5PartialJetOne u t) 0 := by
    unfold thetaCuspReflectedActionC5PartialJetOne
    dsimp only
    fun_prop
  have hp2 : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedActionC5PartialJetTwo u t) 0 := by
    unfold thetaCuspReflectedActionC5PartialJetTwo
    fun_prop
  have hpd : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedActionC5PartialDisplacement u t) 0 := by
    unfold thetaCuspReflectedActionC5PartialDisplacement
    dsimp only
    fun_prop
  have hcenter : HasDerivAt
      (fun u => thetaCuspReflectedActionC5CenterDerivative u t)
      (thetaCuspReflectedActionC5PartialAction 0 t *
          thetaCuspReflectedLogCenterJetTwo 0 t +
        thetaCuspReflectedActionC5PartialJetOne 0 t *
          thetaCuspReflectedLogCenterMixedJetTwo 0 t +
        thetaCuspReflectedActionC5PartialJetTwo 0 t *
          thetaCuspReflectedLogCenterMixedJetFour 0 t) 0 := by
    have h0 := thetaCuspReflectedLogCenterJetOne_zero_center t
    have h1 := thetaCuspReflectedLogCenterMixedJetOne_zero_center t
    have h3 := thetaCuspReflectedLogCenterMixedJetThree_zero_center t
    have hraw :=
      ((hpA.hasDerivAt.mul
          (hasDerivAt_thetaCuspReflectedLogCenterJetOne 0 t)).add
        (hp1.hasDerivAt.mul
          (hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne 0 t))).add
        (hp2.hasDerivAt.mul
          (hasDerivAt_thetaCuspReflectedLogCenterMixedJetThree 0 t))
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
    · rfl
    · rw [h0, h1, h3]
      ring
  have hcenter0 : thetaCuspReflectedActionC5CenterDerivative 0 t = 0 := by
    unfold thetaCuspReflectedActionC5CenterDerivative
    rw [thetaCuspReflectedLogCenterJetOne_zero_center,
      thetaCuspReflectedLogCenterMixedJetOne_zero_center,
      thetaCuspReflectedLogCenterMixedJetThree_zero_center]
    ring
  have hdisp : DifferentiableAt ℝ
      (fun u => thetaCuspReflectedActionC5DisplacementDerivative u t) 0 := by
    unfold thetaCuspReflectedActionC5DisplacementDerivative
    fun_prop
  have hqcenter := hasDerivAt_thetaCuspReflectedLogCenterJetOne 0 t
  have hqcenter0 := thetaCuspReflectedLogCenterJetOne_zero_center t
  have haction := hasDerivAt_thetaCuspReflectedLogJetOne_center 0 t
  have haction0 := thetaCuspReflectedLogCenterMixedJetOne_zero_center t
  have hraw := (hcenter.mul haction).sub (hdisp.hasDerivAt.mul hqcenter)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · rfl
  · rw [hcenter0, hqcenter0, haction0,
      thetaCuspReflectedLogCenterJetTwo_zero_eq,
      thetaCuspReflectedLogCenterMixedJetTwo_zero_eq,
      thetaCuspReflectedLogCenterMixedJetFour_zero_eq]
    unfold thetaCuspReflectedActionC5DisplacementDerivative
    dsimp only
    ring

private theorem iteratedDeriv_one_thetaCuspReflectedLogAction_zero
    (t : ℝ) :
    iteratedDeriv 1 (thetaCuspReflectedLogAction 0) t =
      thetaCuspReflectedLogJetOne 0 t := by
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
    (hasDerivAt_thetaCuspReflectedLogAction 0 t).deriv

private theorem iteratedDeriv_two_thetaCuspReflectedLogAction_zero
    (t : ℝ) :
    iteratedDeriv 2 (thetaCuspReflectedLogAction 0) t =
      thetaCuspReflectedLogJetTwo 0 t := by
  have hfun : iteratedDeriv 1 (thetaCuspReflectedLogAction 0) =
      thetaCuspReflectedLogJetOne 0 := by
    funext x
    exact iteratedDeriv_one_thetaCuspReflectedLogAction_zero x
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, hfun,
    (hasDerivAt_thetaCuspReflectedLogJetOne 0 t).deriv]

private theorem iteratedDeriv_three_thetaCuspReflectedLogAction_zero
    (t : ℝ) :
    iteratedDeriv 3 (thetaCuspReflectedLogAction 0) t =
      thetaCuspReflectedLogJetThree 0 t := by
  have hfun : iteratedDeriv 2 (thetaCuspReflectedLogAction 0) =
      thetaCuspReflectedLogJetTwo 0 := by
    funext x
    exact iteratedDeriv_two_thetaCuspReflectedLogAction_zero x
  rw [show (3 : ℕ) = 2 + 1 by omega, iteratedDeriv_succ, hfun,
    (hasDerivAt_thetaCuspReflectedLogJetTwo 0 t).deriv]

private theorem iteratedDeriv_four_thetaCuspReflectedLogAction_zero
    (t : ℝ) :
    iteratedDeriv 4 (thetaCuspReflectedLogAction 0) t =
      thetaCuspReflectedLogJetFour 0 t := by
  have hfun : iteratedDeriv 3 (thetaCuspReflectedLogAction 0) =
      thetaCuspReflectedLogJetThree 0 := by
    funext x
    exact iteratedDeriv_three_thetaCuspReflectedLogAction_zero x
  rw [show (4 : ℕ) = 3 + 1 by omega, iteratedDeriv_succ, hfun,
    (hasDerivAt_thetaCuspReflectedLogJetThree 0 t).deriv]

/-- The analytic germ is exactly the squared-radius regularization of the actual direct
fixed-action C5 Jacobian centre derivative away from the collapsed displacement seam. -/
theorem thetaCuspC5FixedActionJacobianCenterRegularizedGerm_eq
    {t : ℝ} (ht : 0 < t) :
    thetaCuspC5FixedActionJacobianCenterRegularizedGerm t =
      (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) ^ (2 : ℕ) *
        deriv (fun u => thetaCuspReflectedActionC5FixedActionJacobian u t) 0 := by
  rw [(hasDerivAt_thetaCuspReflectedActionC5FixedActionJacobian_center_zero ht).deriv]
  unfold thetaCuspC5FixedActionJacobianCenterRegularizedGerm
    HTGeometry.c5FixedActionRegularizedCenterExpression
  rw [iteratedDeriv_one_thetaCuspReflectedLogAction_zero,
    iteratedDeriv_two_thetaCuspReflectedLogAction_zero,
    iteratedDeriv_three_thetaCuspReflectedLogAction_zero,
    iteratedDeriv_four_thetaCuspReflectedLogAction_zero]
  dsimp only
  have hr : Real.exp (thetaCuspReflectedLogAction 0 t) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos (u := 0) ht))
  unfold thetaCuspReflectedActionC5PartialJetOne
    thetaCuspReflectedActionC5PartialJetTwo
    thetaCuspReflectedActionC5PartialDisplacement
    thetaCuspReflectedActionInverseRadius
  dsimp only
  field_simp [hr]
  ring

/-- Smoothness of the division-free direct fixed-action Jacobian germ. -/
theorem contDiff_thetaCuspC5FixedActionJacobianCenterRegularizedGerm :
    ContDiff ℝ ∞ thetaCuspC5FixedActionJacobianCenterRegularizedGerm := by
  unfold thetaCuspC5FixedActionJacobianCenterRegularizedGerm
  exact HTGeometry.contDiff_c5FixedActionRegularizedCenterExpression
    (-iteratedDeriv 2 thetaCuspLogSource 0)
    (thetaCuspReflectedLogAction 0)
    contDiff_thetaCuspReflectedLogAction_zero

private def c5IteratedTaylorShift
    (f : ℝ → ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    iteratedDeriv k f x * r ^ k / (k.factorial : ℝ)

private theorem taylorWithinEval_add_eq_c5IteratedTaylorShift
    {f : ℝ → ℝ} {x r : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hr : 0 < r) (j : ℕ) :
    taylorWithinEval f j (uIcc x (x + r)) x (x + r) =
      c5IteratedTaylorShift f j r x := by
  have hle : x ≤ x + r := by linarith
  rw [uIcc_of_le hle]
  induction j with
  | zero =>
      simp [c5IteratedTaylorShift, iteratedDeriv_zero]
  | succ j ih =>
      rw [taylorWithinEval_succ, ih]
      simp only [c5IteratedTaylorShift, Finset.sum_range_succ]
      have hderiv : iteratedDerivWithin (j + 1) f (Icc x (x + r)) x =
          iteratedDeriv (j + 1) f x := by
        exact iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by linarith))
          (hf.of_le (WithTop.coe_le_coe.mpr le_top))
          (left_mem_Icc.mpr hle)
      rw [hderiv, Nat.factorial_succ]
      push_cast
      ring

private theorem thetaCuspC5FixedActionJacobianCenterRegularizedGerm_taylor_eight_zero
    {t : ℝ} (ht : 0 < t) :
    taylorWithinEval thetaCuspC5FixedActionJacobianCenterRegularizedGerm 8
      (uIcc 0 t) 0 t = 0 := by
  have hTaylor := taylorWithinEval_add_eq_c5IteratedTaylorShift
    (f := thetaCuspC5FixedActionJacobianCenterRegularizedGerm)
    (x := 0) (r := t)
    contDiff_thetaCuspC5FixedActionJacobianCenterRegularizedGerm.contDiffAt ht 8
  simpa only [zero_add] using hTaylor.trans (by
    unfold c5IteratedTaylorShift
    apply Finset.sum_eq_zero
    intro k hk
    rw [thetaCuspC5FixedActionJacobianCenterRegularizedGerm_jets.1 k
      (Finset.mem_range.mp hk)]
    simp)

/-- The positive ninth centre germ forces a punctured right neighbourhood on which the
division-free direct fixed-action C5 Jacobian linearization is positive. -/
theorem eventually_thetaCuspC5FixedActionJacobianCenterRegularizedGerm_pos :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < thetaCuspC5FixedActionJacobianCenterRegularizedGerm t := by
  let f := thetaCuspC5FixedActionJacobianCenterRegularizedGerm
  have hf : ContDiff ℝ ∞ f := by
    simpa only [f] using
      contDiff_thetaCuspC5FixedActionJacobianCenterRegularizedGerm
  have hf9 : ContinuousAt (iteratedDeriv 9 f) 0 :=
    (HTGeometry.contDiff_top_iteratedDeriv_real f hf 9).continuous.continuousAt
  have hpos0 : 0 < iteratedDeriv 9 f 0 := by
    simpa only [f] using
      thetaCuspC5FixedActionJacobianCenterRegularizedGerm_ninth_pos
  have hevent : {x : ℝ | 0 < iteratedDeriv 9 f x} ∈ nhds 0 :=
    continuousAt_const.eventually_lt hf9 hpos0
  rcases Metric.mem_nhds_iff.mp hevent with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have hTaylor : taylorWithinEval f 8 (uIcc 0 t) 0 t = 0 := by
    simpa only [f] using
      thetaCuspC5FixedActionJacobianCenterRegularizedGerm_taylor_eight_zero ht
  obtain ⟨x, hx, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x := t) (x₀ := 0) (n := 8) (ne_of_lt ht)
    (hf.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [uIoo_of_le ht.le] at hx
  have hxball : x ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
    exact hx.2.trans htδ
  have hxpos : 0 < iteratedDeriv 9 f x := hball hxball
  rw [hTaylor, sub_zero, sub_zero] at hrem
  change 0 < f t
  rw [hrem]
  exact div_pos (mul_pos hxpos (pow_pos ht 9)) (by positivity)

/-- Direct-J acquires a definite positive centre orientation immediately to the right of the
collapsed displacement seam. -/
theorem eventually_deriv_thetaCuspReflectedActionC5FixedActionJacobian_center_pos :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < deriv (fun u => thetaCuspReflectedActionC5FixedActionJacobian u t) 0 := by
  rcases eventually_thetaCuspC5FixedActionJacobianCenterRegularizedGerm_pos with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have hG := hlocal t ht htδ
  rw [thetaCuspC5FixedActionJacobianCenterRegularizedGerm_eq ht] at hG
  exact pos_of_mul_pos_right hG (sq_nonneg _)

/-- The positive centre derivative is an actual positive direct-J chamber: for every sufficiently
small positive displacement, direct-J is positive throughout some punctured right neighbourhood
of the reflection centre. -/
theorem eventually_right_thetaCuspReflectedActionC5FixedActionJacobian_pos :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
        0 < thetaCuspReflectedActionC5FixedActionJacobian u t := by
  rcases eventually_deriv_thetaCuspReflectedActionC5FixedActionJacobian_center_pos with
    ⟨δ, hδ, hderiv⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have hcenter :=
    hasDerivAt_thetaCuspReflectedActionC5FixedActionJacobian_center_zero ht
  have hcenter' : HasDerivAt
      (fun u => thetaCuspReflectedActionC5FixedActionJacobian u t)
      (deriv (fun u => thetaCuspReflectedActionC5FixedActionJacobian u t) 0) 0 :=
    hcenter.congr_deriv hcenter.deriv.symm
  have hslope : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      0 < u⁻¹ * thetaCuspReflectedActionC5FixedActionJacobian u t := by
    have hlimit := hcenter'.tendsto_slope_zero_right
    have hevent := hlimit.eventually (eventually_gt_nhds (hderiv t ht htδ))
    simpa [smul_eq_mul, thetaCuspReflectedActionC5FixedActionJacobian_zero] using hevent
  have hu : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < u := self_mem_nhdsWithin
  filter_upwards [hslope, hu] with u hJu hu
  exact pos_of_mul_pos_right hJu (inv_nonneg.mpr hu.le)

end

end RHTower
