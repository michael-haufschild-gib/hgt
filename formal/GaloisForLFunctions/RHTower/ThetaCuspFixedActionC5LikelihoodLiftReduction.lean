import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodCenterFlow
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati
import GaloisForLFunctions.HTGeometry.ConvexIntegralTrapezoid

/-!
# Fixed-action C5 likelihood-lift reduction

This module attacks the decisive far-tail conjecture

  completed atom-plus-likelihood compensation is positive on the physical tail.

Its RH proof chain is:

  far-tail direct-J orientation -> local/compact assembly -> fixed-action seam ->
  reflection-odd rank-four/Ptolemy wall -> cofinal no-escape ->
  CLG/TTF or Weil polarization positivity -> RH.

The exact atom-plus-likelihood action is differentiated in the centre and identified with the
intrinsic completed-source transport.  More importantly, the complete third likelihood channel is
proved quantitatively favorable: it adds

  t^2 * (completed first jet * positive centre jet
    - negative third likelihood jet * positive centre-action jet)

to velocity-slope transport.  The support gap forces its mixed second-centre jet to exceed six
times the adverse master curvature, so literal compensation recovers more than thirty master
units after the C5 coefficient is applied.  Convex source geometry controls all five remaining
adverse likelihood quantities by the single positive master loss
`-thetaCuspReflectedLikelihoodCumulantJetTwo`.  The open tail burden is therefore one scalar
atom-versus-likelihood domination with a quantified highest-channel reserve, rather than an
independent seven-jet bound.  A sharper adaptive law shows curvature cools faster than
`exp (-thetaCuspSingleAtomReflectionScale 1 x)` and gives exact reflected-endpoint coupling.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Likelihood log partition is strictly convex on the physical source half-line. -/
theorem strictConvexOn_thetaCuspLikelihoodSourceLogPartition :
    StrictConvexOn ℝ (Set.Ici 0) thetaCuspLikelihoodSourceLogPartition := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) ?_ ?_
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartition
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  · intro x hx y hy hxy
    rw [interior_Ici] at hx hy
    rw [(hasDerivAt_thetaCuspLikelihoodSourceLogPartition
        (thetaCuspLikelihoodCoordinate_pos hx.le)).deriv,
      (hasDerivAt_thetaCuspLikelihoodSourceLogPartition
        (thetaCuspLikelihoodCoordinate_pos hy.le)).deriv]
    exact strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetOne
      (show x ∈ Set.Ici 0 by simpa only [Set.mem_Ici] using hx.le)
      (show y ∈ Set.Ici 0 by simpa only [Set.mem_Ici] using hy.le) hxy

/-- Source likelihood curvature cools at a strict rate set by the first-atom scale.  This is the
sharp support-gap coupling between the sole adverse master curvature and its favorable centre
transport. -/
theorem two_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
    {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspLikelihoodSourceLogPartitionJetTwo x <
      -thetaCuspLikelihoodSourceLogPartitionJetThree x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let m := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  let v := thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x)
  let k := thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x)
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have hm : 0 < m := by
    simpa only [m] using thetaCuspLikelihoodMean_pos
      (thetaCuspLikelihoodCoordinate_pos hx)
  have hv : 0 < v := by
    simpa only [v] using thetaCuspLikelihoodVariance_pos
      (thetaCuspLikelihoodCoordinate_pos hx)
  have hk : 2 * v < k := by
    simpa only [v, k] using
      two_mul_thetaCuspLikelihoodVariance_lt_thirdCumulant_coordinate hx
  have hk' : A ^ 2 * (2 * v) < A ^ 2 * k :=
    mul_lt_mul_of_pos_left hk (sq_pos_of_pos hA0)
  have hbracket :
      0 < A ^ 2 * (k - v) - 3 * A * v + A * m + m := by
    have hgap : 0 < A * v * (A - 3) := by positivity
    nlinarith
  unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
    thetaCuspLikelihoodSourceLogPartitionJetThree
  dsimp only [A, m, v, k] at hA0 hbracket ⊢
  nlinarith [mul_pos hA0 hbracket]

/-- Constant-rate corollary of adaptive support-gap cooling. -/
theorem six_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
    {x : ℝ} (hx : 0 ≤ x) :
    6 * thetaCuspLikelihoodSourceLogPartitionJetTwo x <
      -thetaCuspLikelihoodSourceLogPartitionJetThree x := by
  have hA := three_lt_thetaCuspSingleAtomReflectionScale
    (n := 1) (by norm_num) hx
  have hcurv := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos hx
  have hadaptive :=
    two_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree hx
  have hscale : 6 * thetaCuspLikelihoodSourceLogPartitionJetTwo x <
      2 * thetaCuspSingleAtomReflectionScale 1 x *
        thetaCuspLikelihoodSourceLogPartitionJetTwo x := by
    nlinarith
  exact lt_trans hscale hadaptive

/-- Adaptively renormalized likelihood curvature is strictly decreasing. -/
theorem strictAntiOn_expScale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo :
    StrictAntiOn (fun x : ℝ =>
      Real.exp (thetaCuspSingleAtomReflectionScale 1 x) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo x) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro x hx
    have hA := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
    have hexp := hA.exp
    have hh := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos hx)
    exact (hexp.mul hh).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hA := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
    have hexp := hA.exp
    have hh := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos hx.le)
    have hderiv := hexp.mul hh
    change deriv ((fun y : ℝ =>
      Real.exp (thetaCuspSingleAtomReflectionScale 1 y)) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo) x < 0
    rw [hderiv.deriv]
    have hcool :=
      two_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
        hx.le
    have hexppos := Real.exp_pos (thetaCuspSingleAtomReflectionScale 1 x)
    nlinarith

/-- Adaptive endpoint likelihood curvature separation across a reflected packet. -/
theorem expScaleWeighted_thetaCuspLikelihoodSourceLogPartitionJetTwo_plus_lt_minus
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    Real.exp (thetaCuspSingleAtomReflectionScale 1 (u + t)) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) <
      Real.exp (thetaCuspSingleAtomReflectionScale 1 (u - t)) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) := by
  exact strictAntiOn_expScale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo
    (show u - t ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
    (show u + t ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
    (by linarith)

/-- Adaptive curvature endpoint separation in displacement-normalized form. -/
theorem expScaleGap_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_plus_lt_minus
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    Real.exp (thetaCuspSingleAtomReflectionScale 1 (u + t) -
        thetaCuspSingleAtomReflectionScale 1 (u - t)) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) <
      thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) := by
  have hsep :=
    expScaleWeighted_thetaCuspLikelihoodSourceLogPartitionJetTwo_plus_lt_minus ht htu
  have heq :
      Real.exp (thetaCuspSingleAtomReflectionScale 1 (u + t)) =
        Real.exp (thetaCuspSingleAtomReflectionScale 1 (u - t)) *
          Real.exp (thetaCuspSingleAtomReflectionScale 1 (u + t) -
            thetaCuspSingleAtomReflectionScale 1 (u - t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hsep
  have hcommon :=
    Real.exp_pos (thetaCuspSingleAtomReflectionScale 1 (u - t))
  have hsep' :
      Real.exp (thetaCuspSingleAtomReflectionScale 1 (u - t)) *
          (Real.exp (thetaCuspSingleAtomReflectionScale 1 (u + t) -
              thetaCuspSingleAtomReflectionScale 1 (u - t)) *
            thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)) <
        Real.exp (thetaCuspSingleAtomReflectionScale 1 (u - t)) *
          thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) := by
    simpa only [mul_assoc] using hsep
  by_contra hnot
  have hle : thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) ≤
      Real.exp (thetaCuspSingleAtomReflectionScale 1 (u + t) -
          thetaCuspSingleAtomReflectionScale 1 (u - t)) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_left hle hcommon.le
  exact (not_lt_of_ge hmul) hsep'

/-- The mixed-centre channel retains the adaptive support-gap fraction of master curvature loss. -/
theorem expScaleGap_sub_one_mul_neg_reflectedJetTwo_lt_mixedJetOne
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    let E := Real.exp (thetaCuspSingleAtomReflectionScale 1 (u + t) -
      thetaCuspSingleAtomReflectionScale 1 (u - t))
    (E - 1) * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) <
      (E + 1) * c5LikelihoodScaleMixedJetOne u t := by
  dsimp only
  have hsep :=
    expScaleGap_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_plus_lt_minus ht htu
  unfold thetaCuspReflectedLikelihoodCumulantJetTwo
    c5LikelihoodScaleMixedJetOne
  nlinarith

/-- Scale-weighted master curvature exposed by adaptive support-gap cooling. -/
def c5LikelihoodAdaptiveMasterCurvature (u t : ℝ) : ℝ :=
  2 * thetaCuspSingleAtomReflectionScale 1 (u + t) *
      thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) +
    2 * thetaCuspSingleAtomReflectionScale 1 (u - t) *
      thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)

/-- Adaptive cooling summed over both reflected endpoints gives a quantitative lower bound for
the favorable highest mixed-centre channel. -/
theorem adaptiveMasterCurvature_lt_c5LikelihoodScaleMixedJetTwo
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    c5LikelihoodAdaptiveMasterCurvature u t <
      c5LikelihoodScaleMixedJetTwo u t := by
  have hplus :=
    two_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
      (show 0 ≤ u + t by linarith)
  have hminus :=
    two_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
      (show 0 ≤ u - t by linarith)
  unfold c5LikelihoodAdaptiveMasterCurvature c5LikelihoodScaleMixedJetTwo
  linarith

/-- Universal consequence: highest mixed-centre gain exceeds six times the sole adverse master
curvature. -/
theorem six_mul_neg_reflectedJetTwo_lt_c5LikelihoodScaleMixedJetTwo
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    6 * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) <
      c5LikelihoodScaleMixedJetTwo u t := by
  have hplus := six_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
    (show 0 ≤ u + t by linarith)
  have hminus := six_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree
    (show 0 ≤ u - t by linarith)
  unfold thetaCuspReflectedLikelihoodCumulantJetTwo
    c5LikelihoodScaleMixedJetTwo
  linarith

/-- Exponentially renormalized likelihood curvature is strictly decreasing. -/
theorem strictAntiOn_expSix_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo :
    StrictAntiOn (fun x : ℝ => Real.exp (6 * x) *
      thetaCuspLikelihoodSourceLogPartitionJetTwo x) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro x hx
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (6 * y))
        (6 * Real.exp (6 * x)) x := by
      convert ((hasDerivAt_id x).const_mul 6).exp using 1 <;>
        simp [mul_comm]
    have hh := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos hx)
    exact (hexp.mul hh).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (6 * y))
        (6 * Real.exp (6 * x)) x := by
      convert ((hasDerivAt_id x).const_mul 6).exp using 1 <;>
        simp [mul_comm]
    have hh := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos hx.le)
    have hderiv := hexp.mul hh
    change deriv ((fun y : ℝ => Real.exp (6 * y)) *
      thetaCuspLikelihoodSourceLogPartitionJetTwo) x < 0
    rw [hderiv.deriv]
    have hcool :=
      six_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree hx.le
    have hexppos := Real.exp_pos (6 * x)
    nlinarith

/-- Endpoint likelihood curvature has strict exponential separation across a reflected packet. -/
theorem expWeighted_thetaCuspLikelihoodSourceLogPartitionJetTwo_plus_lt_minus
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    Real.exp (6 * (u + t)) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) <
      Real.exp (6 * (u - t)) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) := by
  exact strictAntiOn_expSix_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo
    (show u - t ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
    (show u + t ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
    (by linarith)

/-- Curvature endpoint separation in displacement-normalized form. -/
theorem expTwelve_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_plus_lt_minus
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    Real.exp (12 * t) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) <
      thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) := by
  have hsep :=
    expWeighted_thetaCuspLikelihoodSourceLogPartitionJetTwo_plus_lt_minus ht htu
  have heq : Real.exp (6 * (u + t)) =
      Real.exp (6 * (u - t)) * Real.exp (12 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hsep
  have hcommon := Real.exp_pos (6 * (u - t))
  have hsep' : Real.exp (6 * (u - t)) *
        (Real.exp (12 * t) *
          thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)) <
      Real.exp (6 * (u - t)) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) := by
    simpa only [mul_assoc] using hsep
  by_contra hnot
  have hle : thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) ≤
      Real.exp (12 * t) *
        thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t) := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_left hle hcommon.le
  exact (not_lt_of_ge hmul) hsep'

/-- The first mixed-centre channel retains an explicit exponential fraction of the master
curvature loss. -/
theorem expTwelve_sub_one_mul_neg_reflectedJetTwo_lt_mixedJetOne
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    (Real.exp (12 * t) - 1) *
        (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) <
      (Real.exp (12 * t) + 1) * c5LikelihoodScaleMixedJetOne u t := by
  have hsep :=
    expTwelve_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_plus_lt_minus ht htu
  unfold thetaCuspReflectedLikelihoodCumulantJetTwo
    c5LikelihoodScaleMixedJetOne
  nlinarith

/-- Strict convexity makes reflected likelihood action a genuine negative tax. -/
theorem thetaCuspReflectedLikelihoodCumulantAction_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedLikelihoodCumulantAction u t < 0 := by
  have hminus : u - t ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hplus : u + t ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hne : u + t ≠ u - t := by linarith
  have hmid := strictConvexOn_thetaCuspLikelihoodSourceLogPartition.2
    hplus hminus hne
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num [smul_eq_mul] at hmid
  have harg : (1 / 2 : ℝ) * (u + t) + 1 / 2 * (u - t) = u := by ring
  rw [harg] at hmid
  unfold thetaCuspReflectedLikelihoodCumulantAction
  linarith

/-- Centre action tax is smaller than displacement-score loss. -/
theorem c5LikelihoodScaleActionJetOne_lt_neg_displacementJetOne
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    c5LikelihoodScaleActionJetOne u t <
      -thetaCuspReflectedLikelihoodCumulantJetOne u t := by
  have hu : u ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hplus : u + t ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hmono := strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetOne
    hu hplus (by linarith)
  unfold c5LikelihoodScaleActionJetOne
    thetaCuspReflectedLikelihoodCumulantJetOne
  linarith

/-- Mixed curvature transport is smaller than displacement-curvature loss. -/
theorem c5LikelihoodScaleMixedJetOne_lt_neg_displacementJetTwo
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    c5LikelihoodScaleMixedJetOne u t <
      -thetaCuspReflectedLikelihoodCumulantJetTwo u t := by
  have hplus := thetaCuspLikelihoodSourceLogPartitionJetTwo_pos
    (show 0 ≤ u + t by linarith)
  unfold c5LikelihoodScaleMixedJetOne
    thetaCuspReflectedLikelihoodCumulantJetTwo
  linarith

/-- Second centre jet strictly dominates third displacement loss. -/
theorem neg_displacementJetThree_lt_c5LikelihoodScaleMixedJetTwo
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    -thetaCuspReflectedLikelihoodCumulantJetThree u t <
      c5LikelihoodScaleMixedJetTwo u t := by
  have hplus := thetaCuspLikelihoodSourceLogPartitionJetThree_neg
    (show 0 ≤ u + t by linarith)
  unfold c5LikelihoodScaleMixedJetTwo
    thetaCuspReflectedLikelihoodCumulantJetThree
  linarith

/-- Likelihood action tax is strictly smaller than displacement times its first-jet loss.  This is
the first link in the action--jet hierarchy used by the C5 likelihood homotopy. -/
theorem neg_thetaCuspReflectedLikelihoodCumulantAction_lt_mul_neg_jetOne
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    -thetaCuspReflectedLikelihoodCumulantAction u t <
      t * (-thetaCuspReflectedLikelihoodCumulantJetOne u t) := by
  let g := thetaCuspLikelihoodSourceLogPartition
  let h := thetaCuspLikelihoodSourceLogPartitionJetOne
  have hminus_nonneg : 0 ≤ u - t := by linarith
  have hu_nonneg : 0 ≤ u := by linarith
  have hcont : ContinuousOn g (Set.Ici 0) := by
    intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartition
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (h x) x := by
    intro x hx
    exact hasDerivAt_thetaCuspLikelihoodSourceLogPartition
      (thetaCuspLikelihoodCoordinate_pos hx)
  have hleft_cont : ContinuousOn g (Set.Icc (u - t) u) :=
    hcont.mono (by intro x hx; exact le_trans hminus_nonneg hx.1)
  have hright_cont : ContinuousOn g (Set.Icc u (u + t)) :=
    hcont.mono (by intro x hx; exact le_trans hu_nonneg hx.1)
  obtain ⟨x, hx, hxslope⟩ := exists_hasDerivAt_eq_slope g h
    (by linarith : u - t < u) hleft_cont (by
      intro y hy
      exact hderiv y (le_trans hminus_nonneg hy.1.le))
  obtain ⟨y, hy, hyslope⟩ := exists_hasDerivAt_eq_slope g h
    (by linarith : u < u + t) hright_cont (by
      intro z hz
      exact hderiv z (le_trans hu_nonneg hz.1.le))
  have hxmem : x ∈ Set.Ici (0 : ℝ) := le_trans hminus_nonneg hx.1.le
  have hymem : y ∈ Set.Ici (0 : ℝ) := le_trans hu_nonneg hy.1.le
  have hminus_mem : u - t ∈ Set.Ici (0 : ℝ) := hminus_nonneg
  have hplus_mem : u + t ∈ Set.Ici (0 : ℝ) :=
    hu_nonneg.trans (le_add_of_nonneg_right ht.le)
  have hxrise : h (u - t) < h x :=
    strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetOne
      hminus_mem hxmem hx.1
  have hyrise : h y < h (u + t) :=
    strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetOne
      hymem hplus_mem hy.2
  have hleft : g u - g (u - t) = t * h x := by
    dsimp only [g, h] at hxslope ⊢
    field_simp [ht.ne'] at hxslope
    linarith
  have hright : g (u + t) - g u = t * h y := by
    dsimp only [g, h] at hyslope ⊢
    field_simp [ht.ne'] at hyslope
    linarith
  unfold thetaCuspReflectedLikelihoodCumulantAction
    thetaCuspReflectedLikelihoodCumulantJetOne
  dsimp only [g, h] at hleft hright hxrise hyrise
  nlinarith [mul_lt_mul_of_pos_left hxrise ht,
    mul_lt_mul_of_pos_left hyrise ht]

/-- The centre-action likelihood channel is strictly dominated by displacement times the first
mixed centre channel.  Thus these two likelihood channels are not independent in C5 transport. -/
theorem c5LikelihoodScaleActionJetOne_lt_mul_mixedJetOne
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    c5LikelihoodScaleActionJetOne u t <
      t * c5LikelihoodScaleMixedJetOne u t := by
  let g := thetaCuspLikelihoodSourceLogPartitionJetOne
  let h := thetaCuspLikelihoodSourceLogPartitionJetTwo
  have hminus_nonneg : 0 ≤ u - t := by linarith
  have hu_nonneg : 0 ≤ u := by linarith
  have hplus_nonneg : 0 ≤ u + t := by linarith
  have hcont : ContinuousOn g (Set.Ici 0) := by
    intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (h x) x := by
    intro x hx
    exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
      (thetaCuspLikelihoodCoordinate_pos hx)
  have hleft_cont : ContinuousOn g (Set.Icc (u - t) u) :=
    hcont.mono (by intro x hx; exact le_trans hminus_nonneg hx.1)
  have hright_cont : ContinuousOn g (Set.Icc u (u + t)) :=
    hcont.mono (by intro x hx; exact le_trans hu_nonneg hx.1)
  obtain ⟨x, hx, hxslope⟩ := exists_hasDerivAt_eq_slope g h
    (by linarith : u - t < u) hleft_cont (by
      intro y hy
      exact hderiv y (le_trans hminus_nonneg hy.1.le))
  obtain ⟨y, hy, hyslope⟩ := exists_hasDerivAt_eq_slope g h
    (by linarith : u < u + t) hright_cont (by
      intro z hz
      exact hderiv z (le_trans hu_nonneg hz.1.le))
  have hxmem : x ∈ Set.Ici (0 : ℝ) := le_trans hminus_nonneg hx.1.le
  have hymem : y ∈ Set.Ici (0 : ℝ) := le_trans hu_nonneg hy.1.le
  have hminus_mem : u - t ∈ Set.Ici (0 : ℝ) := hminus_nonneg
  have hplus_mem : u + t ∈ Set.Ici (0 : ℝ) := hplus_nonneg
  have hxdrop : h x < h (u - t) :=
    strictAntiOn_thetaCuspLikelihoodSourceLogPartitionJetTwo
      hminus_mem hxmem hx.1
  have hydrop : h (u + t) < h y :=
    strictAntiOn_thetaCuspLikelihoodSourceLogPartitionJetTwo
      hymem hplus_mem hy.2
  have hleft : g u - g (u - t) = t * h x := by
    dsimp only [g, h] at hxslope ⊢
    field_simp [ht.ne'] at hxslope
    linarith
  have hright : g (u + t) - g u = t * h y := by
    dsimp only [g, h] at hyslope ⊢
    field_simp [ht.ne'] at hyslope
    linarith
  unfold c5LikelihoodScaleActionJetOne c5LikelihoodScaleMixedJetOne
  dsimp only [g, h] at hleft hright hxdrop hydrop
  nlinarith [mul_lt_mul_of_pos_left hxdrop ht,
    mul_lt_mul_of_pos_left hydrop ht]

/-- Likelihood curvature is convex on the physical source half-line. -/
theorem convexOn_thetaCuspLikelihoodSourceLogPartitionJetTwo :
    ConvexOn ℝ (Set.Ici 0) thetaCuspLikelihoodSourceLogPartitionJetTwo := by
  refine (StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) ?_ ?_).convexOn
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  · intro x hx y hy hxy
    rw [interior_Ici] at hx hy
    rw [(hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
        (thetaCuspLikelihoodCoordinate_pos hx.le)).deriv,
      (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
        (thetaCuspLikelihoodCoordinate_pos hy.le)).deriv]
    exact strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetThree
      (show x ∈ Set.Ici 0 by simpa only [Set.mem_Ici] using hx.le)
      (show y ∈ Set.Ici 0 by simpa only [Set.mem_Ici] using hy.le) hxy

/-- Reflected likelihood first-jet loss is at most displacement times second-jet loss.  This is the
upper Hermite--Hadamard coupling for likelihood curvature. -/
theorem neg_thetaCuspReflectedLikelihoodCumulantJetOne_le_mul_neg_jetTwo
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    -thetaCuspReflectedLikelihoodCumulantJetOne u t ≤
      t * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) := by
  let g := thetaCuspLikelihoodSourceLogPartitionJetOne
  let h := thetaCuspLikelihoodSourceLogPartitionJetTwo
  have ha : 0 ≤ u - t := by linarith
  have hab : u - t < u + t := by linarith
  have hcont : ContinuousOn h (Set.Icc (u - t) (u + t)) := by
    intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos (le_trans ha hx.1))).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable h MeasureTheory.volume (u - t) (u + t) :=
    hcont.intervalIntegrable_of_Icc hab.le
  have hconvIcc : ConvexOn ℝ (Set.Icc (u - t) (u + t)) h := by
    refine ⟨convex_Icc (u - t) (u + t), ?_⟩
    intro x hx y hy a b ha' hb' hab'
    exact convexOn_thetaCuspLikelihoodSourceLogPartitionJetTwo.2
      (le_trans ha hx.1) (le_trans ha hy.1) ha' hb' hab'
  have htrap := ConvexOn.integral_le_trapezoid hab
    hconvIcc hint
  have hftc : (∫ x in (u - t)..(u + t), h x) = g (u + t) - g (u - t) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
        (thetaCuspLikelihoodCoordinate_pos (by
          rw [Set.uIcc_of_le hab.le] at hx
          exact le_trans ha hx.1))
    · exact hint
  rw [hftc] at htrap
  unfold thetaCuspReflectedLikelihoodCumulantJetOne
    thetaCuspReflectedLikelihoodCumulantJetTwo
  dsimp only [g, h] at htrap ⊢
  nlinarith

/-- Exact likelihood action--jet hierarchy.  Every lower likelihood tax entering the C5 homotopy
is controlled by the second displacement loss. -/
theorem thetaCuspReflectedLikelihoodCumulantActionJetHierarchy
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    -thetaCuspReflectedLikelihoodCumulantAction u t <
        t * (-thetaCuspReflectedLikelihoodCumulantJetOne u t) ∧
      t * (-thetaCuspReflectedLikelihoodCumulantJetOne u t) ≤
        t ^ 2 * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) := by
  refine ⟨neg_thetaCuspReflectedLikelihoodCumulantAction_lt_mul_neg_jetOne ht htu, ?_⟩
  have hjet := neg_thetaCuspReflectedLikelihoodCumulantJetOne_le_mul_neg_jetTwo ht htu
  have hmul := mul_le_mul_of_nonneg_left hjet ht.le
  nlinarith

/-- **Single-master lower-jet reduction.**  After the favorable third channel is removed, every
likelihood quantity that can oppose first-atom C5 compensation is controlled by the single positive
master loss `-thetaCuspReflectedLikelihoodCumulantJetTwo u t`.  Thus the literal completed tail is
reduced from a five-channel likelihood perturbation to one scalar domination problem. -/
theorem c5LikelihoodLowerJetSingleMasterReduction
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < -thetaCuspReflectedLikelihoodCumulantJetTwo u t ∧
      -thetaCuspReflectedLikelihoodCumulantAction u t <
        t ^ 2 * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) ∧
      -thetaCuspReflectedLikelihoodCumulantJetOne u t ≤
        t * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) ∧
      0 < c5LikelihoodScaleActionJetOne u t ∧
      c5LikelihoodScaleActionJetOne u t <
        t * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) ∧
      0 < c5LikelihoodScaleMixedJetOne u t ∧
      c5LikelihoodScaleMixedJetOne u t <
        -thetaCuspReflectedLikelihoodCumulantJetTwo u t := by
  have htwo := thetaCuspReflectedLikelihoodCumulantJetTwo_neg ht htu
  have hhier := thetaCuspReflectedLikelihoodCumulantActionJetHierarchy ht htu
  have hjet := neg_thetaCuspReflectedLikelihoodCumulantJetOne_le_mul_neg_jetTwo ht htu
  have haction : -thetaCuspReflectedLikelihoodCumulantAction u t <
      t ^ 2 * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) :=
    lt_of_lt_of_le hhier.1 hhier.2
  have hspos := c5LikelihoodScaleActionJetOne_pos ht htu
  have hmpos := c5LikelihoodScaleMixedJetOne_pos ht htu
  have hsm := c5LikelihoodScaleActionJetOne_lt_mul_mixedJetOne ht htu
  have hmy := c5LikelihoodScaleMixedJetOne_lt_neg_displacementJetTwo ht htu
  have htmy := mul_lt_mul_of_pos_left hmy ht
  have hsy : c5LikelihoodScaleActionJetOne u t <
      t * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) :=
    lt_trans hsm htmy
  exact ⟨neg_pos.mpr htwo, haction, hjet,
    hspos, hsy, hmpos, hmy⟩

/-- Completed centre derivative of reflected action in atom-plus-likelihood coordinates. -/
def c5CompletedScaleActionJetOne (u t : ℝ) : ℝ :=
  c5SingleAtomScaleActionJetOne
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) +
    c5LikelihoodScaleActionJetOne u t

/-- Completed centre derivative of first displacement jet. -/
def c5CompletedScaleMixedJetOne (u t : ℝ) : ℝ :=
  c5SingleAtomScaleMixedJetOne
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t)
      (2 * Real.sinh (2 * t)) +
    c5LikelihoodScaleMixedJetOne u t

/-- Completed centre derivative of second displacement jet. -/
def c5CompletedScaleMixedJetTwo (u t : ℝ) : ℝ :=
  c5SingleAtomScaleMixedJetTwo
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) +
    c5LikelihoodScaleMixedJetTwo u t

/-- Completed division-free fixed-action centre transport numerator. -/
def c5CompletedVelocityCenterNumerator (u t : ℝ) : ℝ :=
  let a := thetaCuspCompletedReflectedCumulantJetOne u t
  let b := thetaCuspCompletedReflectedCumulantJetTwo u t
  let s := c5CompletedScaleActionJetOne u t
  let m := c5CompletedScaleMixedJetOne u t
  a * (t * m) - (a + t * b) * s

/-- Completed division-free velocity-slope centre transport numerator. -/
def c5CompletedVelocitySlopeCenterNumerator (u t : ℝ) : ℝ :=
  let a := thetaCuspCompletedReflectedCumulantJetOne u t
  let b := thetaCuspCompletedReflectedCumulantJetTwo u t
  let c := thetaCuspCompletedReflectedCumulantJetThree u t
  let s := c5CompletedScaleActionJetOne u t
  let m := c5CompletedScaleMixedJetOne u t
  let n := c5CompletedScaleMixedJetTwo u t
  a * (t * m + t ^ 2 * n) - (a + 3 * t * b + t ^ 2 * c) * s

/-- Completed transport with only third likelihood channel removed. -/
def c5CompletedVelocitySlopeLowerJetNumerator (u t : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let a := thetaCuspCompletedReflectedCumulantJetOne u t
  let b := thetaCuspCompletedReflectedCumulantJetTwo u t
  let c₀ := thetaCuspSingleAtomReflectedActionJetThree A z (2 * Real.sinh (2 * t))
  let s := c5CompletedScaleActionJetOne u t
  let m := c5CompletedScaleMixedJetOne u t
  let n₀ := c5SingleAtomScaleMixedJetTwo A z
  a * (t * m + t ^ 2 * n₀) - (a + 3 * t * b + t ^ 2 * c₀) * s

/-- Completed first action jet stays positive in open same-half-line chamber. -/
theorem c5CompletedActionJetOne_pos
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    0 < thetaCuspCompletedReflectedCumulantJetOne u t := by
  rw [← thetaCuspReflectedLogJetOne_eq_completed ht htu]
  exact thetaCuspReflectedLogJetOne_pos u ht

/-- Completed centre-action jet is positive on structural physical tail. -/
theorem c5CompletedScaleActionJetOne_pos
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < c5CompletedScaleActionJetOne u t := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  have hz : 0 < z := by
    dsimp only [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hL := c5SingleAtomScaleActionSlope_pos_of_sameHalfLine ht.le htu.le hscale
  have hatom : 0 < c5SingleAtomScaleActionJetOne A z := by
    have heq : c5SingleAtomScaleActionJetOne A z =
        z * (4 * A + c5SingleAtomScaleLambdaJetOne A /
          thetaCuspSingleAtomReflectionFactor A z) := by
      unfold c5SingleAtomScaleActionJetOne
      ring
    rw [heq]
    dsimp only [A, z] at hL ⊢
    exact mul_pos hz hL
  have hlike := c5LikelihoodScaleActionJetOne_pos ht htu.le
  unfold c5CompletedScaleActionJetOne
  exact add_pos hatom hlike

/-- Highest likelihood channel strictly improves completed velocity-slope transport. -/
theorem c5CompletedVelocitySlopeLowerJetNumerator_lt
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    c5CompletedVelocitySlopeLowerJetNumerator u t <
      c5CompletedVelocitySlopeCenterNumerator u t := by
  let a := thetaCuspCompletedReflectedCumulantJetOne u t
  let s := c5CompletedScaleActionJetOne u t
  let γ := thetaCuspReflectedLikelihoodCumulantJetThree u t
  let ν := c5LikelihoodScaleMixedJetTwo u t
  have ha : 0 < a := by
    simpa only [a] using c5CompletedActionJetOne_pos ht htu
  have hs : 0 < s := by
    simpa only [s] using c5CompletedScaleActionJetOne_pos ht htu hscale
  have hγ : γ < 0 := by
    simpa only [γ] using thetaCuspReflectedLikelihoodCumulantJetThree_neg ht htu.le
  have hν : 0 < ν := by
    simpa only [ν] using c5LikelihoodScaleMixedJetTwo_pos ht htu.le
  have haν : 0 < a * ν := mul_pos ha hν
  have hγs : γ * s < 0 := mul_neg_of_neg_of_pos hγ hs
  have hinner : 0 < a * ν - γ * s := by linarith
  have hgain : 0 < t ^ 2 * (a * ν - γ * s) :=
    mul_pos (sq_pos_of_pos ht) hinner
  unfold c5CompletedVelocitySlopeCenterNumerator
    c5CompletedVelocitySlopeLowerJetNumerator
    thetaCuspCompletedReflectedCumulantJetThree c5CompletedScaleMixedJetTwo
  dsimp only [a, s, γ, ν] at hgain ⊢
  linarith

/-- Quantitative highest-channel reserve: the source support gap pays more than six master
curvature units inside completed velocity-slope transport. -/
theorem six_mul_masterCurvature_lt_completedVelocitySlopeGain
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    6 * t ^ 2 * thetaCuspCompletedReflectedCumulantJetOne u t *
        (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) <
      c5CompletedVelocitySlopeCenterNumerator u t -
        c5CompletedVelocitySlopeLowerJetNumerator u t := by
  let a := thetaCuspCompletedReflectedCumulantJetOne u t
  let y := -thetaCuspReflectedLikelihoodCumulantJetTwo u t
  let s := c5CompletedScaleActionJetOne u t
  let c := thetaCuspReflectedLikelihoodCumulantJetThree u t
  let n := c5LikelihoodScaleMixedJetTwo u t
  have ha : 0 < a := by
    simpa only [a] using c5CompletedActionJetOne_pos ht htu
  have hs : 0 < s := by
    simpa only [s] using c5CompletedScaleActionJetOne_pos ht htu hscale
  have hc : c < 0 := by
    simpa only [c] using thetaCuspReflectedLikelihoodCumulantJetThree_neg ht htu.le
  have hn : 6 * y < n := by
    simpa only [y, n] using
      six_mul_neg_reflectedJetTwo_lt_c5LikelihoodScaleMixedJetTwo ht.le htu.le
  have hayn : 6 * a * y < a * n := by
    have hmul := mul_lt_mul_of_pos_left hn ha
    nlinarith
  have hcs : c * s < 0 := mul_neg_of_neg_of_pos hc hs
  have hinner : 6 * a * y < a * n - c * s := by linarith
  have hmul := mul_lt_mul_of_pos_left hinner (sq_pos_of_pos ht)
  unfold c5CompletedVelocitySlopeCenterNumerator
    c5CompletedVelocitySlopeLowerJetNumerator
    thetaCuspCompletedReflectedCumulantJetThree c5CompletedScaleMixedJetTwo
  dsimp only [a, y, s, c, n] at hmul ⊢
  nlinarith

/-- Sharp adaptive form of the highest-channel reserve. -/
theorem adaptiveMasterCurvature_lt_completedVelocitySlopeGain
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    t ^ 2 * thetaCuspCompletedReflectedCumulantJetOne u t *
        c5LikelihoodAdaptiveMasterCurvature u t <
      c5CompletedVelocitySlopeCenterNumerator u t -
        c5CompletedVelocitySlopeLowerJetNumerator u t := by
  let a := thetaCuspCompletedReflectedCumulantJetOne u t
  let z := c5LikelihoodAdaptiveMasterCurvature u t
  let s := c5CompletedScaleActionJetOne u t
  let c := thetaCuspReflectedLikelihoodCumulantJetThree u t
  let n := c5LikelihoodScaleMixedJetTwo u t
  have ha : 0 < a := by
    simpa only [a] using c5CompletedActionJetOne_pos ht htu
  have hs : 0 < s := by
    simpa only [s] using c5CompletedScaleActionJetOne_pos ht htu hscale
  have hc : c < 0 := by
    simpa only [c] using thetaCuspReflectedLikelihoodCumulantJetThree_neg ht htu.le
  have hn : z < n := by
    simpa only [z, n] using
      adaptiveMasterCurvature_lt_c5LikelihoodScaleMixedJetTwo ht.le htu.le
  have hazn : a * z < a * n := mul_lt_mul_of_pos_left hn ha
  have hcs : c * s < 0 := mul_neg_of_neg_of_pos hc hs
  have hinner : a * z < a * n - c * s := by linarith
  have hmul := mul_lt_mul_of_pos_left hinner (sq_pos_of_pos ht)
  unfold c5CompletedVelocitySlopeCenterNumerator
    c5CompletedVelocitySlopeLowerJetNumerator
    thetaCuspCompletedReflectedCumulantJetThree c5CompletedScaleMixedJetTwo
  dsimp only [a, z, s, c, n] at hmul ⊢
  nlinarith

/-- Literal completed compensation margin in atom-plus-likelihood coordinates. -/
def c5CompletedCompensationMargin (u t : ℝ) : ℝ :=
  let q := thetaCuspCompletedReflectedCumulantAction u t
  let v := t * thetaCuspCompletedReflectedCumulantJetOne u t
  let H := c5CompletedVelocityCenterNumerator u t
  let P := c5CompletedVelocitySlopeCenterNumerator u t
  5 * P - (14 + 10 * v + 8 * v / (Real.exp q - 1)) * H

/-- Lower-jet tail margin after deleting strictly favorable highest likelihood channel. -/
def c5CompletedLowerJetCompensationMargin (u t : ℝ) : ℝ :=
  let q := thetaCuspCompletedReflectedCumulantAction u t
  let v := t * thetaCuspCompletedReflectedCumulantJetOne u t
  let H := c5CompletedVelocityCenterNumerator u t
  let P₂ := c5CompletedVelocitySlopeLowerJetNumerator u t
  5 * P₂ - (14 + 10 * v + 8 * v / (Real.exp q - 1)) * H

/-- Lower-jet margin with the universal support-gap portion of the highest likelihood reserve put
back.  Positivity of this sharper margin is sufficient for literal direct-J orientation. -/
def c5CompletedMasterReservedCompensationMargin (u t : ℝ) : ℝ :=
  c5CompletedLowerJetCompensationMargin u t +
    30 * t ^ 2 * thetaCuspCompletedReflectedCumulantJetOne u t *
      (-thetaCuspReflectedLikelihoodCumulantJetTwo u t)

/-- Sharp adaptive support-gap reserve put back into the lower-jet compensation margin. -/
def c5CompletedAdaptiveReservedCompensationMargin (u t : ℝ) : ℝ :=
  c5CompletedLowerJetCompensationMargin u t +
    5 * t ^ 2 * thetaCuspCompletedReflectedCumulantJetOne u t *
      c5LikelihoodAdaptiveMasterCurvature u t

/-- Lower-jet margin is strict lower bound for literal completed compensation. -/
theorem c5CompletedLowerJetCompensationMargin_lt
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    c5CompletedLowerJetCompensationMargin u t <
      c5CompletedCompensationMargin u t := by
  have hP := c5CompletedVelocitySlopeLowerJetNumerator_lt ht htu hscale
  unfold c5CompletedLowerJetCompensationMargin c5CompletedCompensationMargin
  linarith

/-- Quantitative highest-channel theorem strengthens the old sign-only lower margin by thirty
master-curvature units in the literal C5 compensation. -/
theorem c5CompletedMasterReservedCompensationMargin_lt
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    c5CompletedMasterReservedCompensationMargin u t <
      c5CompletedCompensationMargin u t := by
  have hgain :=
    six_mul_masterCurvature_lt_completedVelocitySlopeGain ht htu hscale
  unfold c5CompletedMasterReservedCompensationMargin
    c5CompletedLowerJetCompensationMargin c5CompletedCompensationMargin
  nlinarith

/-- Adaptive support-gap reserve is a strict lower bound for literal completed compensation. -/
theorem c5CompletedAdaptiveReservedCompensationMargin_lt
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    c5CompletedAdaptiveReservedCompensationMargin u t <
      c5CompletedCompensationMargin u t := by
  have hgain :=
    adaptiveMasterCurvature_lt_completedVelocitySlopeGain ht htu hscale
  unfold c5CompletedAdaptiveReservedCompensationMargin
    c5CompletedLowerJetCompensationMargin c5CompletedCompensationMargin
  nlinarith

/-- Centre derivative of completed atom-plus-likelihood action. -/
theorem hasDerivAt_thetaCuspCompletedReflectedCumulantAction_center
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    HasDerivAt (fun x => thetaCuspCompletedReflectedCumulantAction x t)
      (c5CompletedScaleActionJetOne u t) u := by
  have hu : 0 ≤ u := le_trans ht htu
  have hfactor := thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
    (n := 1) (by norm_num) ht htu
  have hatom := hasDerivAt_thetaCuspSingleAtomReflectedAction_scale hu hfactor.ne'
  have hlike := hasDerivAt_thetaCuspReflectedLikelihoodCumulantAction_center
    (u := u) (t := t)
    (thetaCuspLikelihoodCoordinate_pos hu)
    (thetaCuspLikelihoodCoordinate_pos (by linarith))
    (thetaCuspLikelihoodCoordinate_pos (by linarith))
  unfold c5CompletedScaleActionJetOne thetaCuspCompletedReflectedCumulantAction
  exact (hatom.add hlike).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Centre derivative of completed first displacement jet. -/
theorem hasDerivAt_thetaCuspCompletedReflectedCumulantJetOne_center
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    HasDerivAt (fun x => thetaCuspCompletedReflectedCumulantJetOne x t)
      (c5CompletedScaleMixedJetOne u t) u := by
  have hu : 0 ≤ u := le_trans ht htu
  have hfactor := thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
    (n := 1) (by norm_num) ht htu
  have hatom := hasDerivAt_thetaCuspSingleAtomReflectedActionJetOne_scale
    (z := thetaCuspSingleAtomReflectionDefect t)
    (z' := 2 * Real.sinh (2 * t)) hu hfactor.ne'
  have hlike := hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne_center
    (u := u) (t := t)
    (thetaCuspLikelihoodCoordinate_pos (by linarith))
    (thetaCuspLikelihoodCoordinate_pos (by linarith))
  unfold c5CompletedScaleMixedJetOne thetaCuspCompletedReflectedCumulantJetOne
  exact (hatom.add hlike).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Centre derivative of completed second displacement jet. -/
theorem hasDerivAt_thetaCuspCompletedReflectedCumulantJetTwo_center
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    HasDerivAt (fun x => thetaCuspCompletedReflectedCumulantJetTwo x t)
      (c5CompletedScaleMixedJetTwo u t) u := by
  have hu : 0 ≤ u := le_trans ht htu
  have hfactor := thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
    (n := 1) (by norm_num) ht htu
  have hatom := hasDerivAt_thetaCuspSingleAtomReflectedActionJetTwo_scale
    (z := thetaCuspSingleAtomReflectionDefect t) hu hfactor.ne'
  have hlike := hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetTwo_center
    (u := u) (t := t)
    (thetaCuspLikelihoodCoordinate_pos (by linarith))
    (thetaCuspLikelihoodCoordinate_pos (by linarith))
  unfold c5CompletedScaleMixedJetTwo thetaCuspCompletedReflectedCumulantJetTwo
  exact (hatom.add hlike).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Intrinsic and completed centre action jets agree in open same-half-line chamber. -/
theorem thetaCuspReflectedLogCenterJetOne_eq_completed
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    thetaCuspReflectedLogCenterJetOne u t = c5CompletedScaleActionJetOne u t := by
  have heq : (fun x => thetaCuspReflectedLogAction x t) =ᶠ[nhds u]
      (fun x => thetaCuspCompletedReflectedCumulantAction x t) := by
    filter_upwards [Ioi_mem_nhds htu] with x hx
    exact thetaCuspReflectedLogAction_eq_completed ht.le hx.le
  have hs :=
    (hasDerivAt_thetaCuspReflectedLogAction_center u t).congr_of_eventuallyEq heq.symm
  have hc := hasDerivAt_thetaCuspCompletedReflectedCumulantAction_center ht.le htu.le
  exact hs.deriv.symm.trans hc.deriv

/-- Intrinsic and completed first mixed centre jets agree. -/
theorem thetaCuspReflectedLogCenterMixedJetOne_eq_completed
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    thetaCuspReflectedLogCenterMixedJetOne u t = c5CompletedScaleMixedJetOne u t := by
  have heq : (fun x => thetaCuspReflectedLogJetOne x t) =ᶠ[nhds u]
      (fun x => thetaCuspCompletedReflectedCumulantJetOne x t) := by
    filter_upwards [Ioi_mem_nhds htu] with x hx
    exact thetaCuspReflectedLogJetOne_eq_completed ht hx
  have hs :=
    (hasDerivAt_thetaCuspReflectedLogJetOne_center u t).congr_of_eventuallyEq heq.symm
  have hc := hasDerivAt_thetaCuspCompletedReflectedCumulantJetOne_center ht.le htu.le
  exact hs.deriv.symm.trans hc.deriv

/-- Intrinsic and completed second mixed centre jets agree. -/
theorem thetaCuspReflectedLogCenterMixedJetThree_eq_completed
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    thetaCuspReflectedLogCenterMixedJetThree u t = c5CompletedScaleMixedJetTwo u t := by
  have heq : (fun x => thetaCuspReflectedLogJetTwo x t) =ᶠ[nhds u]
      (fun x => thetaCuspCompletedReflectedCumulantJetTwo x t) := by
    filter_upwards [Ioi_mem_nhds htu] with x hx
    exact thetaCuspReflectedLogJetTwo_eq_completed ht hx
  have hs :=
    (hasDerivAt_thetaCuspReflectedLogJetTwo_center u t).congr_of_eventuallyEq heq.symm
  have hc := hasDerivAt_thetaCuspCompletedReflectedCumulantJetTwo_center ht.le htu.le
  exact hs.deriv.symm.trans hc.deriv

/-- Completed and intrinsic velocity centre numerators agree. -/
theorem c5CompletedVelocityCenterNumerator_eq_intrinsic
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    c5CompletedVelocityCenterNumerator u t =
      thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t := by
  unfold c5CompletedVelocityCenterNumerator
    thetaCuspReflectedActionVelocityFixedActionCenterNumerator
  rw [thetaCuspReflectedLogJetOne_eq_completed ht htu,
    thetaCuspReflectedLogJetTwo_eq_completed ht htu,
    thetaCuspReflectedLogCenterJetOne_eq_completed ht htu,
    thetaCuspReflectedLogCenterMixedJetOne_eq_completed ht htu]

/-- Completed and intrinsic velocity-slope centre numerators agree. -/
theorem c5CompletedVelocitySlopeCenterNumerator_eq_intrinsic
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    c5CompletedVelocitySlopeCenterNumerator u t =
      thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator u t := by
  unfold c5CompletedVelocitySlopeCenterNumerator
    thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator
  rw [thetaCuspReflectedLogJetOne_eq_completed ht htu,
    thetaCuspReflectedLogJetTwo_eq_completed ht htu,
    thetaCuspReflectedLogJetThree_eq_completed ht htu,
    thetaCuspReflectedLogCenterJetOne_eq_completed ht htu,
    thetaCuspReflectedLogCenterMixedJetOne_eq_completed ht htu,
    thetaCuspReflectedLogCenterMixedJetThree_eq_completed ht htu]

/-- Completed compensation margin is literal intrinsic compensation. -/
theorem c5CompletedCompensationMargin_eq_intrinsic
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    c5CompletedCompensationMargin u t =
      5 * thetaCuspReflectedActionVelocitySlopeCurrentFixedActionCenterNumerator u t -
        (14 + 10 * thetaCuspReflectedActionVelocity u t +
          8 * thetaCuspReflectedActionVelocity u t /
            (Real.exp (thetaCuspReflectedLogAction u t) - 1)) *
          thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t := by
  unfold c5CompletedCompensationMargin
  rw [c5CompletedVelocityCenterNumerator_eq_intrinsic ht htu,
    c5CompletedVelocitySlopeCenterNumerator_eq_intrinsic ht htu,
    ← thetaCuspReflectedLogAction_eq_completed ht.le htu.le,
    ← thetaCuspReflectedLogJetOne_eq_completed ht htu]
  unfold thetaCuspReflectedActionVelocity
  rfl

/-- Direct-J orientation is exactly positivity of completed atom-plus-likelihood compensation. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_completedCompensation
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    0 < thetaCuspReflectedActionC5FixedActionJacobian u t ↔
      0 < c5CompletedCompensationMargin u t := by
  rw [thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_compensation u ht]
  rw [c5CompletedCompensationMargin_eq_intrinsic ht htu]
  constructor <;> intro h <;> linarith

/-- Lower-jet compensation closes literal far-tail direct-J orientation. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_pos_of_lowerJetCompensation
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u)
    (hlower : 0 < c5CompletedLowerJetCompensationMargin u t) :
    0 < thetaCuspReflectedActionC5FixedActionJacobian u t := by
  rw [thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_completedCompensation
    ht htu]
  exact lt_trans hlower
    (c5CompletedLowerJetCompensationMargin_lt ht htu hscale)

/-- Support-gap reserved compensation closes literal far-tail direct-J orientation.  This is the
strongest current one-scalar endpoint of the likelihood lift. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_pos_of_masterReservedCompensation
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u)
    (hreserve : 0 < c5CompletedMasterReservedCompensationMargin u t) :
    0 < thetaCuspReflectedActionC5FixedActionJacobian u t := by
  rw [thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_completedCompensation
    ht htu]
  exact lt_trans hreserve
    (c5CompletedMasterReservedCompensationMargin_lt ht htu hscale)

/-- Adaptive support-gap reserved compensation closes literal far-tail direct-J orientation. -/
theorem thetaCuspReflectedActionC5FixedActionJacobian_pos_of_adaptiveReservedCompensation
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u)
    (hreserve : 0 < c5CompletedAdaptiveReservedCompensationMargin u t) :
    0 < thetaCuspReflectedActionC5FixedActionJacobian u t := by
  rw [thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_completedCompensation
    ht htu]
  exact lt_trans hreserve
    (c5CompletedAdaptiveReservedCompensationMargin_lt ht htu hscale)

end

end RHTower
