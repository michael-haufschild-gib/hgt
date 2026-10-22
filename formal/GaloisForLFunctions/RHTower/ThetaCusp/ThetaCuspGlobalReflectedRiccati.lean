import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAtomLikelihoodCrossDomination

/-!
# Global reflected Riccati law for the completed theta source

The same-half-line Riccati law and the modular seam are joined through a new center-zero
transport.  The strict fourth logarithmic Turán margin forces the center-zero Riccati margin to
increase from zero.  A purely algebraic two-chamber identity then reconstructs every
seam-crossing reflected margin.
-/

open Set Filter Topology
open scoped ContDiff

namespace RHTower

noncomputable section

/-- The completed logarithmic theta source is smooth to every order. -/
theorem contDiff_thetaCuspLogSource :
    ContDiff ℝ ∞ thetaCuspLogSource := by
  unfold thetaCuspLogSource
  exact contDiff_thetaCuspFullSource.log fun x =>
    (thetaCuspFullSource_pos_all x).ne'

/-- Logarithmic source jets differentiate in the expected order. -/
theorem hasDerivAt_iteratedDeriv_thetaCuspLogSource
    (m : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv m thetaCuspLogSource)
      (iteratedDeriv (m + 1) thetaCuspLogSource x) x := by
  have hdiff :=
    contDiff_thetaCuspLogSource.differentiable_iteratedDeriv m
      (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m))
  simpa only [iteratedDeriv_succ] using (hdiff x).hasDerivAt

/-- The logarithmic completed source inherits exact modular evenness. -/
theorem thetaCuspLogSource_neg (x : ℝ) :
    thetaCuspLogSource (-x) = thetaCuspLogSource x := by
  unfold thetaCuspLogSource
  rw [thetaCuspFullSource_neg]

/-- Every logarithmic source jet has the parity forced by modular reflection. -/
theorem iteratedDeriv_thetaCuspLogSource_neg (m : ℕ) (x : ℝ) :
    iteratedDeriv m thetaCuspLogSource (-x) =
      (-1 : ℝ) ^ m * iteratedDeriv m thetaCuspLogSource x := by
  have hfun : (fun y : ℝ => thetaCuspLogSource (-y)) =
      thetaCuspLogSource := by
    funext y
    exact thetaCuspLogSource_neg y
  have hder := congrArg (iteratedDeriv m) hfun
  have hx := congrFun hder (-x)
  rw [iteratedDeriv_comp_neg] at hx
  simpa [smul_eq_mul] using hx.symm

/-- Odd logarithmic source jets vanish at the modular center. -/
theorem iteratedDeriv_thetaCuspLogSource_zero_of_odd
    {m : ℕ} (hm : Odd m) :
    iteratedDeriv m thetaCuspLogSource 0 = 0 := by
  have h := iteratedDeriv_thetaCuspLogSource_neg m 0
  rw [neg_zero, hm.neg_one_pow] at h
  linarith

/-- Positive-ray decay slope of the completed logarithmic source. -/
def thetaCuspLogDecaySlope (x : ℝ) : ℝ :=
  -iteratedDeriv 1 thetaCuspLogSource x

/-- Positive-ray curvature of the completed logarithmic source. -/
def thetaCuspLogCurvature (x : ℝ) : ℝ :=
  -iteratedDeriv 2 thetaCuspLogSource x

/-- Derivative of completed logarithmic-source curvature. -/
def thetaCuspLogCurvatureJet (x : ℝ) : ℝ :=
  -iteratedDeriv 3 thetaCuspLogSource x

/-- Center-normalized logarithmic reflected action of the completed theta source. -/
def thetaCuspReflectedLogAction (u t : ℝ) : ℝ :=
  2 * thetaCuspLogSource u -
    thetaCuspLogSource (u + t) -
    thetaCuspLogSource (u - t)

/-- First displacement jet of the completed-source reflected action. -/
def thetaCuspReflectedLogJetOne (u t : ℝ) : ℝ :=
  thetaCuspLogDecaySlope (u + t) -
    thetaCuspLogDecaySlope (u - t)

/-- Second displacement jet of the completed-source reflected action. -/
def thetaCuspReflectedLogJetTwo (u t : ℝ) : ℝ :=
  thetaCuspLogCurvature (u + t) +
    thetaCuspLogCurvature (u - t)

/-- Third displacement jet of the completed-source reflected action. -/
def thetaCuspReflectedLogJetThree (u t : ℝ) : ℝ :=
  thetaCuspLogCurvatureJet (u + t) -
    thetaCuspLogCurvatureJet (u - t)

/-- Riccati margin of the intrinsic completed-source reflected action. -/
def thetaCuspReflectedLogRiccatiMargin (u t : ℝ) : ℝ :=
  2 * thetaCuspReflectedLogJetOne u t *
      thetaCuspReflectedLogJetTwo u t -
    thetaCuspReflectedLogJetThree u t

/-- The intrinsic reflected action differentiates to its first named jet. -/
theorem hasDerivAt_thetaCuspReflectedLogAction (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogAction u)
      (thetaCuspReflectedLogJetOne u t) t := by
  have hp :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 0 (u + t)).comp t
      ((hasDerivAt_id t).const_add u)
  have hm :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 0 (u - t)).comp t
      ((hasDerivAt_id t).const_sub u)
  unfold thetaCuspReflectedLogAction thetaCuspReflectedLogJetOne
    thetaCuspLogDecaySlope
  convert ((hasDerivAt_const t (2 * thetaCuspLogSource u)).sub hp).sub hm using 1
  all_goals first | rfl | simp [sub_eq_add_neg]

/-- The first reflected-action jet differentiates to the second. -/
theorem hasDerivAt_thetaCuspReflectedLogJetOne (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogJetOne u)
      (thetaCuspReflectedLogJetTwo u t) t := by
  have hp :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 (u + t)).comp t
      ((hasDerivAt_id t).const_add u)
  have hm :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 (u - t)).comp t
      ((hasDerivAt_id t).const_sub u)
  unfold thetaCuspReflectedLogJetOne thetaCuspReflectedLogJetTwo
    thetaCuspLogDecaySlope thetaCuspLogCurvature
  convert hp.neg.sub hm.neg using 1
  all_goals first | rfl | simp [sub_eq_add_neg]

/-- The second reflected-action jet differentiates to the third. -/
theorem hasDerivAt_thetaCuspReflectedLogJetTwo (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogJetTwo u)
      (thetaCuspReflectedLogJetThree u t) t := by
  have hp :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 (u + t)).comp t
      ((hasDerivAt_id t).const_add u)
  have hm :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 (u - t)).comp t
      ((hasDerivAt_id t).const_sub u)
  unfold thetaCuspReflectedLogJetTwo thetaCuspReflectedLogJetThree
    thetaCuspLogCurvature thetaCuspLogCurvatureJet
  convert hp.neg.add hm.neg using 1
  all_goals first | rfl | simp [sub_eq_add_neg]

/-- Intrinsic reflected action equals the negative logarithm of the normalized source product. -/
theorem thetaCuspReflectedLogAction_eq_neg_log_normalized
    (u t : ℝ) :
    thetaCuspReflectedLogAction u t =
      -Real.log
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
          thetaCuspFullSource u ^ (2 : ℕ)) := by
  have hp := (thetaCuspFullSource_pos_all (u + t)).ne'
  have hm := (thetaCuspFullSource_pos_all (u - t)).ne'
  have hu := (thetaCuspFullSource_pos_all u).ne'
  unfold thetaCuspReflectedLogAction thetaCuspLogSource
  rw [Real.log_div (mul_ne_zero hp hm) (pow_ne_zero 2 hu),
    Real.log_mul hp hm, Real.log_pow]
  ring

/-- Exponentiating the negative intrinsic action recovers the normalized source product. -/
theorem exp_neg_thetaCuspReflectedLogAction (u t : ℝ) :
    Real.exp (-thetaCuspReflectedLogAction u t) =
      thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
        thetaCuspFullSource u ^ (2 : ℕ) := by
  let ratio :=
    thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
      thetaCuspFullSource u ^ (2 : ℕ)
  have hratio : 0 < ratio := by
    exact div_pos
      (mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _))
      (sq_pos_of_pos (thetaCuspFullSource_pos_all _))
  rw [thetaCuspReflectedLogAction_eq_neg_log_normalized]
  simp only [neg_neg]
  exact Real.exp_log hratio

/-- Log-concavity makes every intrinsic reflected action nonnegative. -/
theorem thetaCuspReflectedLogAction_nonneg (u t : ℝ) :
    0 ≤ thetaCuspReflectedLogAction u t := by
  have hprod := thetaCuspFullSource_mul_reflect_le_sq u t
  have hden : 0 < thetaCuspFullSource u ^ (2 : ℕ) :=
    sq_pos_of_pos (thetaCuspFullSource_pos_all u)
  have hratioPos :
      0 < thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
        thetaCuspFullSource u ^ (2 : ℕ) :=
    div_pos
      (mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _))
      hden
  have hratioLe :
      thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
          thetaCuspFullSource u ^ (2 : ℕ) ≤ 1 :=
    (div_le_one hden).2 hprod
  rw [thetaCuspReflectedLogAction_eq_neg_log_normalized]
  exact neg_nonneg.mpr (Real.log_nonpos hratioPos.le hratioLe)

/-- Strict log-concavity makes every nonzero-displacement intrinsic action positive. -/
theorem thetaCuspReflectedLogAction_pos
    {u t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedLogAction u t := by
  have hprod :
      thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) <
        thetaCuspFullSource u ^ (2 : ℕ) := by
    simpa only [add_zero, sub_zero, pow_two] using
      strictAntiOn_thetaCuspFullSource_mul_reflect u
        (by norm_num) ht.le ht
  have hden : 0 < thetaCuspFullSource u ^ (2 : ℕ) :=
    sq_pos_of_pos (thetaCuspFullSource_pos_all u)
  have hratioPos :
      0 < thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
        thetaCuspFullSource u ^ (2 : ℕ) :=
    div_pos
      (mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _))
      hden
  have hratioLt :
      thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
          thetaCuspFullSource u ^ (2 : ℕ) < 1 :=
    (div_lt_one hden).2 hprod
  rw [thetaCuspReflectedLogAction_eq_neg_log_normalized]
  exact neg_pos.mpr (Real.log_neg hratioPos hratioLt)

/-- Differentiation wrapper for the completed atom-plus-likelihood action. -/
theorem hasDerivAt_thetaCuspCompletedReflectedCumulantAction
    {u t : ℝ}
    (hfactor :
      thetaCuspSingleAtomReflectionFactor
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) ≠ 0)
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspCompletedReflectedCumulantAction u)
      (thetaCuspCompletedReflectedCumulantJetOne u t) t := by
  exact (hasDerivAt_thetaCuspSingleAtomReflectedAction hfactor).add
    (hasDerivAt_thetaCuspReflectedLikelihoodCumulantAction hplus hminus)

/-- Differentiation wrapper for the first completed atom-plus-likelihood jet. -/
theorem hasDerivAt_thetaCuspCompletedReflectedCumulantJetOne
    {u t : ℝ}
    (hfactor :
      thetaCuspSingleAtomReflectionFactor
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) ≠ 0)
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspCompletedReflectedCumulantJetOne u)
      (thetaCuspCompletedReflectedCumulantJetTwo u t) t := by
  exact (hasDerivAt_thetaCuspSingleAtomReflectedActionJetOne hfactor).add
    (hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne hplus hminus)

/-- Differentiation wrapper for the second completed atom-plus-likelihood jet. -/
theorem hasDerivAt_thetaCuspCompletedReflectedCumulantJetTwo
    {u t : ℝ}
    (hfactor :
      thetaCuspSingleAtomReflectionFactor
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) ≠ 0)
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (thetaCuspCompletedReflectedCumulantJetTwo u)
      (thetaCuspCompletedReflectedCumulantJetThree u t) t := by
  exact (hasDerivAt_thetaCuspSingleAtomReflectedActionJetTwo hfactor).add
    (hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetTwo hplus hminus)

/-- On the same-half-line chamber, intrinsic and atom-plus-likelihood actions coincide. -/
theorem thetaCuspReflectedLogAction_eq_completed
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspReflectedLogAction u t =
      thetaCuspCompletedReflectedCumulantAction u t := by
  rw [thetaCuspReflectedLogAction_eq_neg_log_normalized]
  exact
    neg_log_thetaCuspFullSource_reflected_normalized_eq_completedCumulantAction
      ht htu

/-- First intrinsic and atom-plus-likelihood jets coincide in the open same-half-line chamber. -/
theorem thetaCuspReflectedLogJetOne_eq_completed
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    thetaCuspReflectedLogJetOne u t =
      thetaCuspCompletedReflectedCumulantJetOne u t := by
  have hu : 0 ≤ u := by linarith
  have hfactor :
      0 < thetaCuspSingleAtomReflectionFactor
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) :=
    thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
      (by norm_num) ht.le htu.le
  have hplus : 0 < thetaCuspLikelihoodCoordinate (u + t) :=
    thetaCuspLikelihoodCoordinate_pos (by positivity)
  have hminus : 0 < thetaCuspLikelihoodCoordinate (u - t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have heq :
      thetaCuspReflectedLogAction u =ᶠ[nhds t]
        thetaCuspCompletedReflectedCumulantAction u := by
    filter_upwards [Ioi_mem_nhds ht, Iio_mem_nhds htu] with s hs0 hsu
    exact thetaCuspReflectedLogAction_eq_completed hs0.le hsu.le
  have hs :=
    (hasDerivAt_thetaCuspReflectedLogAction u t).congr_of_eventuallyEq
      heq.symm
  have hc :=
    hasDerivAt_thetaCuspCompletedReflectedCumulantAction
      hfactor.ne' hplus hminus
  exact hs.deriv.symm.trans hc.deriv

/-- Second intrinsic and atom-plus-likelihood jets coincide in the open same-half-line chamber. -/
theorem thetaCuspReflectedLogJetTwo_eq_completed
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    thetaCuspReflectedLogJetTwo u t =
      thetaCuspCompletedReflectedCumulantJetTwo u t := by
  have hu : 0 ≤ u := by linarith
  have hfactor :
      0 < thetaCuspSingleAtomReflectionFactor
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) :=
    thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
      (by norm_num) ht.le htu.le
  have hplus : 0 < thetaCuspLikelihoodCoordinate (u + t) :=
    thetaCuspLikelihoodCoordinate_pos (by positivity)
  have hminus : 0 < thetaCuspLikelihoodCoordinate (u - t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have heq :
      thetaCuspReflectedLogJetOne u =ᶠ[nhds t]
        thetaCuspCompletedReflectedCumulantJetOne u := by
    filter_upwards [Ioi_mem_nhds ht, Iio_mem_nhds htu] with s hs0 hsu
    exact thetaCuspReflectedLogJetOne_eq_completed hs0 hsu
  have hs :=
    (hasDerivAt_thetaCuspReflectedLogJetOne u t).congr_of_eventuallyEq
      heq.symm
  have hc :=
    hasDerivAt_thetaCuspCompletedReflectedCumulantJetOne
      hfactor.ne' hplus hminus
  exact hs.deriv.symm.trans hc.deriv

/-- Third intrinsic and atom-plus-likelihood jets coincide in the open same-half-line chamber. -/
theorem thetaCuspReflectedLogJetThree_eq_completed
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    thetaCuspReflectedLogJetThree u t =
      thetaCuspCompletedReflectedCumulantJetThree u t := by
  have hu : 0 ≤ u := by linarith
  have hfactor :
      0 < thetaCuspSingleAtomReflectionFactor
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) :=
    thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
      (by norm_num) ht.le htu.le
  have hplus : 0 < thetaCuspLikelihoodCoordinate (u + t) :=
    thetaCuspLikelihoodCoordinate_pos (by positivity)
  have hminus : 0 < thetaCuspLikelihoodCoordinate (u - t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have heq :
      thetaCuspReflectedLogJetTwo u =ᶠ[nhds t]
        thetaCuspCompletedReflectedCumulantJetTwo u := by
    filter_upwards [Ioi_mem_nhds ht, Iio_mem_nhds htu] with s hs0 hsu
    exact thetaCuspReflectedLogJetTwo_eq_completed hs0 hsu
  have hs :=
    (hasDerivAt_thetaCuspReflectedLogJetTwo u t).congr_of_eventuallyEq
      heq.symm
  have hc :=
    hasDerivAt_thetaCuspCompletedReflectedCumulantJetTwo
      hfactor.ne' hplus hminus
  exact hs.deriv.symm.trans hc.deriv

/-- Positive logarithmic decay slope on the positive source half-line. -/
theorem neg_iteratedDeriv_one_thetaCuspLogSource_pos
    {x : ℝ} (hx : 0 < x) :
    0 < -iteratedDeriv 1 thetaCuspLogSource x := by
  have hderivAnti : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun y _ =>
        (hasDerivAt_thetaCuspLogSource y).differentiableAt
  have hzero :=
    iteratedDeriv_thetaCuspLogSource_zero_of_odd
      (show Odd 1 by exact ⟨0, by omega⟩)
  have hzero' : deriv thetaCuspLogSource 0 = 0 := by
    simpa only [iteratedDeriv_one] using hzero
  have hlt : deriv thetaCuspLogSource x < deriv thetaCuspLogSource 0 :=
    hderivAnti hx
  rw [hzero'] at hlt
  simpa only [iteratedDeriv_one, neg_pos] using hlt

/-- Center-zero Riccati margin of the completed logarithmic source. -/
def thetaCuspCenterLogRiccatiMargin (x : ℝ) : ℝ :=
  4 * iteratedDeriv 1 thetaCuspLogSource x *
        iteratedDeriv 2 thetaCuspLogSource x +
    iteratedDeriv 3 thetaCuspLogSource x

/-- Exact derivative of the center-zero Riccati margin. -/
theorem hasDerivAt_thetaCuspCenterLogRiccatiMargin (x : ℝ) :
    HasDerivAt thetaCuspCenterLogRiccatiMargin
      (iteratedDeriv 4 thetaCuspLogSource x +
        4 * iteratedDeriv 2 thetaCuspLogSource x ^ (2 : ℕ) +
        4 * iteratedDeriv 1 thetaCuspLogSource x *
          iteratedDeriv 3 thetaCuspLogSource x) x := by
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  have h2 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x
  have h3 := hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x
  unfold thetaCuspCenterLogRiccatiMargin
  convert ((h1.mul h2).const_mul 4).add h3 using 1
  any_goals rfl
  · funext y
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · ring

/-- In the only potentially adverse curvature-jet chamber, theta support-gap cumulants force
small logarithmic slope and small negative third curvature jet. -/
theorem thetaCuspCenterLogRiccati_adverse_bounds
    {x : ℝ} (hx : 0 < x)
    (hd : -iteratedDeriv 3 thetaCuspLogSource x < 0) :
    -iteratedDeriv 1 thetaCuspLogSource x < 19 / 12 ∧
      -(-iteratedDeriv 3 thetaCuspLogSource x) < 24 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let q := thetaCuspBornWittenWeight 1 x
  let m := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  let g₁ := thetaCuspLikelihoodSourceLogPartitionJetOne x
  let g₃ := thetaCuspLikelihoodSourceLogPartitionJetThree x
  let b₃ := thetaCuspBornWittenLogThirdDerivative 1 x
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale
        (n := 1) (by norm_num) hx.le
  have hq : 3 / 2 < q := by
    simpa only [q] using
      three_halves_lt_thetaCuspBornWittenWeight
        (n := 1) (by norm_num) hx.le
  have hq0 : 0 < q := by linarith
  have hAq : A = q + 3 / 2 := by
    dsimp [A, q, thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq]
    unfold thetaCuspMorseScale
    norm_num
    rw [show 2 * x = x + x by ring, Real.exp_add]
    ring
  have hg₃ : g₃ < 0 := by
    simpa only [g₃] using
      thetaCuspLikelihoodSourceLogPartitionJetThree_neg hx.le
  have hthird :
      iteratedDeriv 3 thetaCuspLogSource x = -b₃ + g₃ := by
    rw [iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx,
      thetaCuspFirstAtomLogJetThree,
      ← thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hx]
  have hb₃ : b₃ < 0 := by
    rw [hthird] at hd
    linarith
  have hq2 : q < 2 := by
    by_contra hnot
    have hq2 : 2 ≤ q := le_of_not_gt hnot
    have hpoly : 0 ≤ 4 * q ^ (3 : ℕ) - 6 * q - 18 := by
      rw [show 4 * q ^ (3 : ℕ) - 6 * q - 18 =
          (q - 2) * (4 * q ^ (2 : ℕ) + 8 * q + 10) + 2 by ring]
      positivity
    have hs : 0 ≤ 4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ) := by
      rw [show 4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ) =
          (4 * q ^ (3 : ℕ) - 6 * q - 18) / q ^ (3 : ℕ) by
        field_simp [hq0.ne']]
      positivity
    dsimp [b₃, thetaCuspBornWittenLogThirdDerivative] at hb₃
    exact (not_lt_of_ge (mul_nonneg (by linarith) hs)) hb₃
  have hb₃lower : -24 < b₃ := by
    have hfactor :
        0 < (2 * q - 3) *
          (4 * q ^ (3 : ℕ) + 24 * q ^ (2 : ℕ) + 30 * q + 18) := by
      exact mul_pos (by linarith) (by positivity)
    change -24 <
      (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ))
    have hid :
      (2 * q + 3) * (4 - 6 / q ^ (2 : ℕ) - 18 / q ^ (3 : ℕ)) + 24 =
          ((2 * q - 3) *
            (4 * q ^ (3 : ℕ) + 24 * q ^ (2 : ℕ) + 30 * q + 18)) / q ^ (3 : ℕ) := by
      field_simp [hq0.ne']
      ring
    have hquot :
        0 < ((2 * q - 3) *
            (4 * q ^ (3 : ℕ) + 24 * q ^ (2 : ℕ) + 30 * q + 18)) / q ^ (3 : ℕ) :=
      div_pos hfactor (pow_pos hq0 3)
    linarith
  have hd24 : -(-iteratedDeriv 3 thetaCuspLogSource x) < 24 := by
    rw [hthird]
    linarith
  have hm : 0 < m := by
    simpa only [m] using
      thetaCuspLikelihoodMean_pos (thetaCuspLikelihoodCoordinate_pos hx.le)
  have hmSmall : 12 * m < 1 := by
    simpa only [m] using
      twelve_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx.le
  have hAupper : A < 7 / 2 := by rw [hAq]; linarith
  have hAm : 2 * A * m < 7 / 12 := by
    nlinarith [mul_pos (sub_pos.mpr hAupper) hm]
  have hsuper :
      2 * thetaCuspBornWittenSuperpotential 1 x < 1 := by
    have hprofile :=
      two_thetaCuspBornWittenSuperpotential_eq_readoutProfile
        (n := 1) (by norm_num) hx.le
    have hinv : 3 / 2 < 3 / q := by
      apply (lt_div_iff₀ hq0).2
      nlinarith
    rw [hprofile]
    linarith
  have hfirst :
      iteratedDeriv 1 thetaCuspLogSource x =
        -2 * thetaCuspBornWittenSuperpotential 1 x + g₁ := by
    rw [iteratedDeriv_one_thetaCuspLogSource_eq_full_jets hx,
      thetaCuspFirstAtomLogJetOne,
      ← thetaCuspLikelihoodSourceLogPartitionJetOne_eq_higherLikelihoodLogJetOne hx]
  have hg₁ :
      g₁ = -2 * A * m := by
    unfold g₁ thetaCuspLikelihoodSourceLogPartitionJetOne
    rfl
  constructor
  · rw [hfirst, hg₁]
    linarith
  · exact hd24

/-- The strict fourth-Turán source margin transports the center-zero Riccati margin strictly
upward throughout the positive half-line. -/
theorem deriv_thetaCuspCenterLogRiccatiMargin_pos
    {x : ℝ} (hx : 0 < x) :
    0 < deriv thetaCuspCenterLogRiccatiMargin x := by
  rw [(hasDerivAt_thetaCuspCenterLogRiccatiMargin x).deriv]
  have hTuran :=
    thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty hx
  have hh := neg_iteratedDeriv_one_thetaCuspLogSource_pos hx
  by_cases hd : 0 ≤ -iteratedDeriv 3 thetaCuspLogSource x
  · nlinarith [mul_nonneg hh.le hd]
  · have hdneg : -iteratedDeriv 3 thetaCuspLogSource x < 0 :=
      lt_of_not_ge hd
    have hb := thetaCuspCenterLogRiccati_adverse_bounds hx hdneg
    nlinarith [mul_pos
      (sub_pos.mpr hb.1)
      (sub_pos.mpr hb.2)]

/-- The center-zero completed-source Riccati margin is nonnegative, and strict away from the
modular center. -/
theorem thetaCuspCenterLogRiccatiMargin_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspCenterLogRiccatiMargin x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · have h1 :=
      iteratedDeriv_thetaCuspLogSource_zero_of_odd
        (show Odd 1 by exact ⟨0, by omega⟩)
    have h3 :=
      iteratedDeriv_thetaCuspLogSource_zero_of_odd
        (show Odd 3 by exact ⟨1, by omega⟩)
    simp [thetaCuspCenterLogRiccatiMargin, h1, h3]
  · have hcontinuous : Continuous thetaCuspCenterLogRiccatiMargin := by
      have hj (m : ℕ) :
          Continuous (iteratedDeriv m thetaCuspLogSource) :=
        (contDiff_thetaCuspLogSource.differentiable_iteratedDeriv m
          (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m))).continuous
      unfold thetaCuspCenterLogRiccatiMargin
      fun_prop
    have hmono :
        StrictMonoOn thetaCuspCenterLogRiccatiMargin (Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact hcontinuous.continuousOn
      · intro y hy
        rw [interior_Ici] at hy
        exact deriv_thetaCuspCenterLogRiccatiMargin_pos hy
    have hzero :
        thetaCuspCenterLogRiccatiMargin 0 = 0 := by
      have h1 :=
        iteratedDeriv_thetaCuspLogSource_zero_of_odd
          (show Odd 1 by exact ⟨0, by omega⟩)
      have h3 :=
        iteratedDeriv_thetaCuspLogSource_zero_of_odd
          (show Odd 3 by exact ⟨1, by omega⟩)
      simp [thetaCuspCenterLogRiccatiMargin, h1, h3]
    rw [← hzero]
    exact (hmono (by simp) (by simp [hx.le]) hx).le

/-- The center-zero margin in decay-slope, curvature, and curvature-jet coordinates. -/
theorem thetaCuspCenterLogRiccatiMargin_eq_slope_curvature
    (x : ℝ) :
    thetaCuspCenterLogRiccatiMargin x =
      4 * thetaCuspLogDecaySlope x * thetaCuspLogCurvature x -
        thetaCuspLogCurvatureJet x := by
  unfold thetaCuspCenterLogRiccatiMargin thetaCuspLogDecaySlope
    thetaCuspLogCurvature thetaCuspLogCurvatureJet
  ring

/-- The completed logarithmic decay slope is monotone on the whole real line. -/
theorem monotone_thetaCuspLogDecaySlope :
    Monotone thetaCuspLogDecaySlope := by
  have hanti : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun y _ =>
        (hasDerivAt_thetaCuspLogSource y).differentiableAt
  intro a b hab
  unfold thetaCuspLogDecaySlope
  simp only [iteratedDeriv_one]
  exact neg_le_neg (hanti.antitone hab)

/-- The completed logarithmic decay slope is nonnegative on the positive ray. -/
theorem thetaCuspLogDecaySlope_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspLogDecaySlope x := by
  rcases hx.eq_or_lt with rfl | hx
  · unfold thetaCuspLogDecaySlope
    rw [iteratedDeriv_thetaCuspLogSource_zero_of_odd
      (show Odd 1 by exact ⟨0, by omega⟩)]
    norm_num
  · exact (neg_iteratedDeriv_one_thetaCuspLogSource_pos hx).le

/-- Difference-chamber Riccati margin expressed directly at its two positive endpoints. -/
def thetaCuspLogDifferenceRiccatiMargin (a b : ℝ) : ℝ :=
  2 * (thetaCuspLogDecaySlope a - thetaCuspLogDecaySlope b) *
      (thetaCuspLogCurvature a + thetaCuspLogCurvature b) -
    (thetaCuspLogCurvatureJet a - thetaCuspLogCurvatureJet b)

/-- Midpoint reflection and endpoint-difference coordinates give the same intrinsic margin. -/
theorem thetaCuspReflectedLogRiccatiMargin_midpoint
    (a b : ℝ) :
    thetaCuspReflectedLogRiccatiMargin ((a + b) / 2) ((a - b) / 2) =
      thetaCuspLogDifferenceRiccatiMargin a b := by
  unfold thetaCuspReflectedLogRiccatiMargin
    thetaCuspReflectedLogJetOne thetaCuspReflectedLogJetTwo
    thetaCuspReflectedLogJetThree thetaCuspLogDifferenceRiccatiMargin
  ring_nf

/-- Strict positive-endpoint difference margins are inherited from the completed
atom-plus-likelihood theorem. -/
theorem thetaCuspLogDifferenceRiccatiMargin_nonneg_of_pos
    {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    0 ≤ thetaCuspLogDifferenceRiccatiMargin a b := by
  let u := (a + b) / 2
  let t := (a - b) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htu : t < u := by dsimp [t, u]; linarith
  have h₁ := thetaCuspReflectedLogJetOne_eq_completed ht htu
  have h₂ := thetaCuspReflectedLogJetTwo_eq_completed ht htu
  have h₃ := thetaCuspReflectedLogJetThree_eq_completed ht htu
  have hmargin :=
    thetaCuspCompletedReflectedCumulantRiccatiMargin_nonneg
      (u := u) ht.le htu.le
  rw [thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_jets] at hmargin
  rw [← h₁, ← h₂, ← h₃] at hmargin
  rw [← thetaCuspReflectedLogRiccatiMargin_midpoint a b]
  simpa only [thetaCuspReflectedLogRiccatiMargin, u, t] using hmargin

/-- The endpoint-difference margin remains nonnegative when the lower endpoint reaches the
modular center. -/
theorem thetaCuspLogDifferenceRiccatiMargin_nonneg_at_zero
    {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ thetaCuspLogDifferenceRiccatiMargin a 0 := by
  rcases ha.eq_or_lt with rfl | ha
  · unfold thetaCuspLogDifferenceRiccatiMargin
    ring_nf
    exact le_rfl
  · let f : ℝ → ℝ := fun b => thetaCuspLogDifferenceRiccatiMargin a b
    have hj (m : ℕ) :
        Continuous (iteratedDeriv m thetaCuspLogSource) :=
      (contDiff_thetaCuspLogSource.differentiable_iteratedDeriv m
        (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m))).continuous
    have hf : Continuous f := by
      dsimp only [f]
      unfold thetaCuspLogDifferenceRiccatiMargin thetaCuspLogDecaySlope
        thetaCuspLogCurvature thetaCuspLogCurvatureJet
      fun_prop
    haveI := nhdsWithin_Ioi_neBot (a := (0 : ℝ)) (b := (0 : ℝ)) le_rfl
    have htend :
        Tendsto f (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (f 0)) :=
      hf.continuousAt.continuousWithinAt
    apply isClosed_Ici.mem_of_tendsto htend
    filter_upwards [
        eventually_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds ha)] with b hb hba
    exact thetaCuspLogDifferenceRiccatiMargin_nonneg_of_pos hb hba

/-- **Closed same-half-line law.**  Every ordered pair of nonnegative endpoints has
nonnegative completed-source difference Riccati margin. -/
theorem thetaCuspLogDifferenceRiccatiMargin_nonneg
    {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    0 ≤ thetaCuspLogDifferenceRiccatiMargin a b := by
  rcases hb.eq_or_lt with rfl | hb
  · exact thetaCuspLogDifferenceRiccatiMargin_nonneg_at_zero
      (le_trans (by norm_num) hab)
  · rcases hab.eq_or_lt with rfl | hab
    · unfold thetaCuspLogDifferenceRiccatiMargin
      ring_nf
      exact le_rfl
    · exact thetaCuspLogDifferenceRiccatiMargin_nonneg_of_pos hb hab

/-- The logarithmic decay slope is odd. -/
theorem thetaCuspLogDecaySlope_neg (x : ℝ) :
    thetaCuspLogDecaySlope (-x) = -thetaCuspLogDecaySlope x := by
  unfold thetaCuspLogDecaySlope
  rw [iteratedDeriv_thetaCuspLogSource_neg]
  norm_num

/-- The logarithmic curvature is even. -/
theorem thetaCuspLogCurvature_neg (x : ℝ) :
    thetaCuspLogCurvature (-x) = thetaCuspLogCurvature x := by
  unfold thetaCuspLogCurvature
  rw [iteratedDeriv_thetaCuspLogSource_neg]
  norm_num

/-- The logarithmic curvature jet is odd. -/
theorem thetaCuspLogCurvatureJet_neg (x : ℝ) :
    thetaCuspLogCurvatureJet (-x) = -thetaCuspLogCurvatureJet x := by
  unfold thetaCuspLogCurvatureJet
  rw [iteratedDeriv_thetaCuspLogSource_neg]
  norm_num

/-- Modular reflection makes the intrinsic Riccati margin even in its center. -/
theorem thetaCuspReflectedLogRiccatiMargin_neg_center
    (u t : ℝ) :
    thetaCuspReflectedLogRiccatiMargin (-u) t =
      thetaCuspReflectedLogRiccatiMargin u t := by
  unfold thetaCuspReflectedLogRiccatiMargin
    thetaCuspReflectedLogJetOne thetaCuspReflectedLogJetTwo
    thetaCuspReflectedLogJetThree
  rw [show -u + t = -(u - t) by ring,
    show -u - t = -(u + t) by ring,
    thetaCuspLogDecaySlope_neg, thetaCuspLogDecaySlope_neg,
    thetaCuspLogCurvature_neg, thetaCuspLogCurvature_neg,
    thetaCuspLogCurvatureJet_neg, thetaCuspLogCurvatureJet_neg]
  ring

/-- In the seam chamber, midpoint reflection becomes the scalar sum Riccati margin of the
two nonnegative reflected endpoints. -/
theorem thetaCuspReflectedLogRiccatiMargin_eq_sum
    (u t : ℝ) :
    thetaCuspReflectedLogRiccatiMargin u t =
      2 *
          (thetaCuspLogDecaySlope (u + t) +
            thetaCuspLogDecaySlope (t - u)) *
          (thetaCuspLogCurvature (u + t) +
            thetaCuspLogCurvature (t - u)) -
        (thetaCuspLogCurvatureJet (u + t) +
          thetaCuspLogCurvatureJet (t - u)) := by
  unfold thetaCuspReflectedLogRiccatiMargin
    thetaCuspReflectedLogJetOne thetaCuspReflectedLogJetTwo
    thetaCuspReflectedLogJetThree
  rw [show u - t = -(t - u) by ring,
    thetaCuspLogDecaySlope_neg, thetaCuspLogCurvature_neg,
    thetaCuspLogCurvatureJet_neg]
  ring

/-- **Nonnegative-center global law.**  Same-half-line control and center-zero transport join
without a seam hypothesis. -/
theorem thetaCuspReflectedLogRiccatiMargin_nonneg_of_center_nonneg
    {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) :
    0 ≤ thetaCuspReflectedLogRiccatiMargin u t := by
  by_cases htu : t ≤ u
  · have hdiff :=
      thetaCuspLogDifferenceRiccatiMargin_nonneg
        (b := u - t) (a := u + t) (by linarith) (by linarith)
    simpa only [
      thetaCuspReflectedLogRiccatiMargin,
      thetaCuspReflectedLogJetOne,
      thetaCuspReflectedLogJetTwo,
      thetaCuspReflectedLogJetThree,
      thetaCuspLogDifferenceRiccatiMargin] using hdiff
  · have hut : u ≤ t := le_of_lt (lt_of_not_ge htu)
    let a := u + t
    let b := t - u
    have hb : 0 ≤ b := by dsimp [b]; linarith
    have hba : b ≤ a := by dsimp [a, b]; linarith
    have hh :
        thetaCuspLogDecaySlope b ≤ thetaCuspLogDecaySlope a :=
      monotone_thetaCuspLogDecaySlope hba
    have hb0 : 0 ≤ thetaCuspLogDecaySlope b :=
      thetaCuspLogDecaySlope_nonneg hb
    have hdiff :
        0 ≤ 2 *
              (thetaCuspLogDecaySlope a - thetaCuspLogDecaySlope b) *
              (thetaCuspLogCurvature a + thetaCuspLogCurvature b) -
            (thetaCuspLogCurvatureJet a - thetaCuspLogCurvatureJet b) := by
      simpa only [thetaCuspLogDifferenceRiccatiMargin] using
        thetaCuspLogDifferenceRiccatiMargin_nonneg hb hba
    have hcenterA :
        0 ≤ 4 * thetaCuspLogDecaySlope a * thetaCuspLogCurvature a -
          thetaCuspLogCurvatureJet a := by
      rw [← thetaCuspCenterLogRiccatiMargin_eq_slope_curvature]
      exact thetaCuspCenterLogRiccatiMargin_nonneg
        (by dsimp [a]; positivity)
    have hcenterB :
        0 ≤ 4 * thetaCuspLogDecaySlope b * thetaCuspLogCurvature b -
          thetaCuspLogCurvatureJet b := by
      rw [← thetaCuspCenterLogRiccatiMargin_eq_slope_curvature]
      exact thetaCuspCenterLogRiccatiMargin_nonneg hb
    have hsum :=
      HilbertMetric.sumRiccatiMargin_nonneg_of_difference_and_center
        hh hb0 hdiff hcenterA hcenterB
    rw [thetaCuspReflectedLogRiccatiMargin_eq_sum]
    simpa only [a, b] using hsum

/-- **Global completed-source Riccati law.**  Every center and every nonnegative displacement
has nonnegative reflected margin. -/
theorem thetaCuspReflectedLogRiccatiMargin_nonneg
    {u t : ℝ} (ht : 0 ≤ t) :
    0 ≤ thetaCuspReflectedLogRiccatiMargin u t := by
  by_cases hu : 0 ≤ u
  · exact thetaCuspReflectedLogRiccatiMargin_nonneg_of_center_nonneg hu ht
  · have hneg :=
      thetaCuspReflectedLogRiccatiMargin_nonneg_of_center_nonneg
        (u := -u) (by linarith) ht
    rw [thetaCuspReflectedLogRiccatiMargin_neg_center] at hneg
    exact hneg

/-- The completed-source correlation angle is concave on every closed nonnegative displacement
interval, uniformly in the reflection center. -/
theorem concaveOn_thetaCuspReflectedLogCorrelationAngle
    {u T : ℝ} (hT : 0 ≤ T) :
    ConcaveOn ℝ (Icc 0 T)
      (HilbertMetric.riccatiCorrelationAngle
        (thetaCuspReflectedLogAction u)) := by
  apply HilbertMetric.concaveOn_riccatiCorrelationAngle_of_margin_nonneg
    (q := thetaCuspReflectedLogAction u)
    (q₁ := thetaCuspReflectedLogJetOne u)
    (q₂ := thetaCuspReflectedLogJetTwo u)
    (q₃ := thetaCuspReflectedLogJetThree u)
    hT
  · unfold thetaCuspReflectedLogAction
    ring_nf
  · unfold thetaCuspReflectedLogJetOne
    ring_nf
  · exact fun t _ => hasDerivAt_thetaCuspReflectedLogAction u t
  · exact fun t _ => hasDerivAt_thetaCuspReflectedLogJetOne u t
  · exact fun t _ => hasDerivAt_thetaCuspReflectedLogJetTwo u t
  · exact fun t _ => thetaCuspReflectedLogAction_nonneg u t
  · intro t ht
    apply thetaCuspReflectedLogAction_pos
    rw [interior_Icc] at ht
    exact ht.1
  · intro t ht
    simpa only [thetaCuspReflectedLogRiccatiMargin] using
      thetaCuspReflectedLogRiccatiMargin_nonneg ht.1

/-- **Global completed-source angle law.**  The correlation angle is subadditive for every
center; no same-half-line or seam proposition remains. -/
theorem thetaCuspFullSource_reflectedCorrelationAngle_subadditive_global
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.arccos
        (thetaCuspFullSource (u + (x + y)) *
            thetaCuspFullSource (u - (x + y)) /
          thetaCuspFullSource u ^ (2 : ℕ)) ≤
      Real.arccos
          (thetaCuspFullSource (u + x) * thetaCuspFullSource (u - x) /
            thetaCuspFullSource u ^ (2 : ℕ)) +
        Real.arccos
          (thetaCuspFullSource (u + y) * thetaCuspFullSource (u - y) /
            thetaCuspFullSource u ^ (2 : ℕ)) := by
  let q : ℝ → ℝ := thetaCuspReflectedLogAction u
  let q₁ : ℝ → ℝ := thetaCuspReflectedLogJetOne u
  let q₂ : ℝ → ℝ := thetaCuspReflectedLogJetTwo u
  let q₃ : ℝ → ℝ := thetaCuspReflectedLogJetThree u
  have hT : 0 ≤ x + y := add_nonneg hx hy
  have hangle :=
    HilbertMetric.riccatiCorrelationAngle_subadditive_of_margin_nonneg
      hT (q := q) (q₁ := q₁) (q₂ := q₂) (q₃ := q₃)
      (by
        unfold q thetaCuspReflectedLogAction
        ring_nf)
      (by
        unfold q₁ thetaCuspReflectedLogJetOne
        ring_nf)
      (fun t _ => hasDerivAt_thetaCuspReflectedLogAction u t)
      (fun t _ => hasDerivAt_thetaCuspReflectedLogJetOne u t)
      (fun t _ => hasDerivAt_thetaCuspReflectedLogJetTwo u t)
      (fun t _ => thetaCuspReflectedLogAction_nonneg u t)
      (fun t ht => thetaCuspReflectedLogAction_pos (by
        rw [interior_Icc] at ht
        exact ht.1))
      (fun t ht => by
        simpa only [q₁, q₂, q₃, thetaCuspReflectedLogRiccatiMargin] using
          thetaCuspReflectedLogRiccatiMargin_nonneg ht.1)
      hx hy le_rfl
  simp only [HilbertMetric.riccatiCorrelationAngle, q] at hangle
  rw [exp_neg_thetaCuspReflectedLogAction,
    exp_neg_thetaCuspReflectedLogAction,
    exp_neg_thetaCuspReflectedLogAction] at hangle
  exact hangle

end

end RHTower
