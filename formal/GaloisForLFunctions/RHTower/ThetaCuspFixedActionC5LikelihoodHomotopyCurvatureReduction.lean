import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodLiftReduction

/-!
# Exact curvature reduction for the C5 likelihood homotopy

The structural-tail likelihood lift interpolates the seven completed action, displacement, and
centre jets affinely from the exact first atom to the full theta source.  This file differentiates
that literal homotopy, without replacing its Bose denominator or any source jet.

The decisive cancellation is that both transport numerators are quadratic in the interpolation
parameter.  Hence the third derivative of the compensation margin is independent of the two
highest channels in the velocity--slope numerator.  It is exactly

`-(W''' * H + 3 * W'' * H' + 3 * W' * H'')`,

where `W` is the literal Bose coefficient and `H` is the lower velocity transport.  Thus the open
RH chain is reduced from a nonlinear seven-jet curvature problem to one three-term lower-transport
balance:

`lower-transport sum < 0 -> M''' > 0 -> convex likelihood lift -> structural-tail direct-J
orientation -> reflection-odd rank-four/Ptolemy -> CLG/TTF or Weil positivity -> RH`.
-/

namespace RHTower

noncomputable section

/-- Constant data of one affine C5 likelihood homotopy. -/
structure C5LikelihoodAffineData where
  t : ℝ
  q : ℝ
  dq : ℝ
  a : ℝ
  da : ℝ
  b : ℝ
  db : ℝ
  c : ℝ
  dc : ℝ
  s : ℝ
  ds : ℝ
  m : ℝ
  dm : ℝ
  n : ℝ
  dn : ℝ

namespace C5LikelihoodAffineData

/-- Affine interpolation of one scalar jet. -/
def affine (x dx l : ℝ) : ℝ := x + l * dx

theorem hasDerivAt_affine (x dx l : ℝ) :
    HasDerivAt (fun μ : ℝ => affine x dx μ) dx l := by
  simpa only [affine, id_eq, add_comm, one_mul] using
    ((hasDerivAt_id l).mul_const dx).const_add x

def action (d : C5LikelihoodAffineData) (l : ℝ) : ℝ := affine d.q d.dq l
def jetOne (d : C5LikelihoodAffineData) (l : ℝ) : ℝ := affine d.a d.da l
def jetTwo (d : C5LikelihoodAffineData) (l : ℝ) : ℝ := affine d.b d.db l
def jetThree (d : C5LikelihoodAffineData) (l : ℝ) : ℝ := affine d.c d.dc l
def scaleAction (d : C5LikelihoodAffineData) (l : ℝ) : ℝ := affine d.s d.ds l
def scaleMixedOne (d : C5LikelihoodAffineData) (l : ℝ) : ℝ := affine d.m d.dm l
def scaleMixedTwo (d : C5LikelihoodAffineData) (l : ℝ) : ℝ := affine d.n d.dn l

/-- Lower fixed-action velocity transport along the affine homotopy. -/
def velocityCenter (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  jetOne d l * (d.t * scaleMixedOne d l) -
    (jetOne d l + d.t * jetTwo d l) * scaleAction d l

/-- First interpolation derivative of lower velocity transport. -/
def velocityCenterOne (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  d.da * (d.t * scaleMixedOne d l) + jetOne d l * (d.t * d.dm) -
    (d.da + d.t * d.db) * scaleAction d l -
    (jetOne d l + d.t * jetTwo d l) * d.ds

/-- Constant second interpolation derivative of lower velocity transport. -/
def velocityCenterTwo (d : C5LikelihoodAffineData) : ℝ :=
  2 * (d.da * (d.t * d.dm) - (d.da + d.t * d.db) * d.ds)

/-- Velocity--slope transport along the affine homotopy. -/
def velocitySlope (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  jetOne d l * (d.t * scaleMixedOne d l + d.t ^ (2 : ℕ) * scaleMixedTwo d l) -
    (jetOne d l + 3 * d.t * jetTwo d l + d.t ^ (2 : ℕ) * jetThree d l) *
      scaleAction d l

/-- First interpolation derivative of velocity--slope transport. -/
def velocitySlopeOne (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  d.da * (d.t * scaleMixedOne d l + d.t ^ (2 : ℕ) * scaleMixedTwo d l) +
    jetOne d l * (d.t * d.dm + d.t ^ (2 : ℕ) * d.dn) -
    (d.da + 3 * d.t * d.db + d.t ^ (2 : ℕ) * d.dc) * scaleAction d l -
    (jetOne d l + 3 * d.t * jetTwo d l + d.t ^ (2 : ℕ) * jetThree d l) * d.ds

/-- Constant second interpolation derivative of velocity--slope transport. -/
def velocitySlopeTwo (d : C5LikelihoodAffineData) : ℝ :=
  2 * (d.da * (d.t * d.dm + d.t ^ (2 : ℕ) * d.dn) -
    (d.da + 3 * d.t * d.db + d.t ^ (2 : ℕ) * d.dc) * d.ds)

theorem hasDerivAt_action (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.action d.dq l := hasDerivAt_affine d.q d.dq l

theorem hasDerivAt_jetOne (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.jetOne d.da l := hasDerivAt_affine d.a d.da l

theorem hasDerivAt_jetTwo (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.jetTwo d.db l := hasDerivAt_affine d.b d.db l

theorem hasDerivAt_jetThree (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.jetThree d.dc l := hasDerivAt_affine d.c d.dc l

theorem hasDerivAt_scaleAction (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.scaleAction d.ds l := hasDerivAt_affine d.s d.ds l

theorem hasDerivAt_scaleMixedOne (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.scaleMixedOne d.dm l := hasDerivAt_affine d.m d.dm l

theorem hasDerivAt_scaleMixedTwo (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.scaleMixedTwo d.dn l := hasDerivAt_affine d.n d.dn l

theorem hasDerivAt_velocityCenter (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.velocityCenter (d.velocityCenterOne l) l := by
  have ha := d.hasDerivAt_jetOne l
  have hb := d.hasDerivAt_jetTwo l
  have hs := d.hasDerivAt_scaleAction l
  have hm := d.hasDerivAt_scaleMixedOne l
  have hraw := (ha.mul (hm.const_mul d.t)).sub
    ((ha.add (hb.const_mul d.t)).mul hs)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · rfl
  · unfold velocityCenterOne
    simp only [Pi.add_apply]
    ring

theorem hasDerivAt_velocityCenterOne (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.velocityCenterOne d.velocityCenterTwo l := by
  have ha := d.hasDerivAt_jetOne l
  have hb := d.hasDerivAt_jetTwo l
  have hs := d.hasDerivAt_scaleAction l
  have hm := d.hasDerivAt_scaleMixedOne l
  have hraw :=
    ((((hm.const_mul d.t).const_mul d.da).add
      ((ha.const_mul (d.t * d.dm)))).sub
      (hs.const_mul (d.da + d.t * d.db))).sub
      ((ha.add (hb.const_mul d.t)).const_mul d.ds)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold velocityCenterOne
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · unfold velocityCenterTwo
    ring

theorem hasDerivAt_velocityCenterTwo (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt (fun _ : ℝ => d.velocityCenterTwo) 0 l :=
  hasDerivAt_const l d.velocityCenterTwo

theorem hasDerivAt_velocitySlope (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.velocitySlope (d.velocitySlopeOne l) l := by
  have ha := d.hasDerivAt_jetOne l
  have hb := d.hasDerivAt_jetTwo l
  have hc := d.hasDerivAt_jetThree l
  have hs := d.hasDerivAt_scaleAction l
  have hm := d.hasDerivAt_scaleMixedOne l
  have hn := d.hasDerivAt_scaleMixedTwo l
  have hraw :=
    (ha.mul ((hm.const_mul d.t).add (hn.const_mul (d.t ^ (2 : ℕ))))).sub
      (((ha.add (hb.const_mul (3 * d.t))).add (hc.const_mul (d.t ^ (2 : ℕ)))).mul hs)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · rfl
  · unfold velocitySlopeOne
    simp only [Pi.add_apply]
    ring

theorem hasDerivAt_velocitySlopeOne (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt d.velocitySlopeOne d.velocitySlopeTwo l := by
  have ha := d.hasDerivAt_jetOne l
  have hb := d.hasDerivAt_jetTwo l
  have hc := d.hasDerivAt_jetThree l
  have hs := d.hasDerivAt_scaleAction l
  have hm := d.hasDerivAt_scaleMixedOne l
  have hn := d.hasDerivAt_scaleMixedTwo l
  have hraw :=
    (((((hm.const_mul d.t).add (hn.const_mul (d.t ^ (2 : ℕ)))).const_mul d.da).add
      (ha.const_mul (d.t * d.dm + d.t ^ (2 : ℕ) * d.dn))).sub
      (hs.const_mul (d.da + 3 * d.t * d.db + d.t ^ (2 : ℕ) * d.dc))).sub
      (((ha.add (hb.const_mul (3 * d.t))).add (hc.const_mul (d.t ^ (2 : ℕ)))).const_mul d.ds)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold velocitySlopeOne
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · unfold velocitySlopeTwo
    ring

theorem hasDerivAt_velocitySlopeTwo (d : C5LikelihoodAffineData) (l : ℝ) :
    HasDerivAt (fun _ : ℝ => d.velocitySlopeTwo) 0 l :=
  hasDerivAt_const l d.velocitySlopeTwo

/-! ## Literal Bose coefficient and its first three affine jets -/

def boseReciprocal (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  1 / (Real.exp (d.action l) - 1)

def boseReciprocalOne (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  let e := Real.exp (d.action l)
  let r := e - 1
  (-e) * d.dq / r ^ (2 : ℕ)

def boseReciprocalTwo (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  let e := Real.exp (d.action l)
  let r := e - 1
  e * (e + 1) * d.dq ^ (2 : ℕ) / r ^ (3 : ℕ)

def boseReciprocalThree (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  let e := Real.exp (d.action l)
  let r := e - 1
  (-e) * (e ^ (2 : ℕ) + 4 * e + 1) * d.dq ^ (3 : ℕ) / r ^ (4 : ℕ)

theorem hasDerivAt_boseReciprocal (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.boseReciprocal (d.boseReciprocalOne l) l := by
  have hE := (d.hasDerivAt_action l).exp
  have hR := hE.sub_const 1
  have hraw := hR.inv hr
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold boseReciprocal
    simp only [one_div, Pi.inv_apply]
  · unfold boseReciprocalOne
    dsimp only
    ring

theorem hasDerivAt_boseReciprocalOne (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.boseReciprocalOne (d.boseReciprocalTwo l) l := by
  have hE := (d.hasDerivAt_action l).exp
  have hR := hE.sub_const 1
  have hraw := ((hE.mul_const (-d.dq)).div (hR.pow 2) (pow_ne_zero 2 hr))
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold boseReciprocalOne
    dsimp only
    simp only [Pi.div_apply, Pi.pow_apply]
    ring
  · unfold boseReciprocalTwo
    dsimp only
    simp only [Pi.pow_apply]
    norm_num
    field_simp [hr]
    ring

theorem hasDerivAt_boseReciprocalTwo (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.boseReciprocalTwo (d.boseReciprocalThree l) l := by
  have hE := (d.hasDerivAt_action l).exp
  have hR := hE.sub_const 1
  have hnum := ((hE.mul (hE.const_add 1)).mul_const (d.dq ^ (2 : ℕ)))
  have hraw := hnum.div (hR.pow 3) (pow_ne_zero 3 hr)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold boseReciprocalTwo
    dsimp only
    simp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · unfold boseReciprocalThree
    dsimp only
    simp only [Pi.mul_apply, Pi.pow_apply]
    norm_num
    field_simp [hr]
    ring

/-- Literal coefficient multiplying lower velocity transport in C5 compensation. -/
def boseCoefficient (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  let v := d.t * d.jetOne l
  14 + 10 * v + 8 * v * d.boseReciprocal l

def boseCoefficientOne (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  let v := d.t * d.jetOne l
  let dv := d.t * d.da
  10 * dv + 8 * (dv * d.boseReciprocal l + v * d.boseReciprocalOne l)

def boseCoefficientTwo (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  let v := d.t * d.jetOne l
  let dv := d.t * d.da
  8 * (2 * dv * d.boseReciprocalOne l + v * d.boseReciprocalTwo l)

def boseCoefficientThree (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  let v := d.t * d.jetOne l
  let dv := d.t * d.da
  8 * (3 * dv * d.boseReciprocalTwo l + v * d.boseReciprocalThree l)

theorem hasDerivAt_boseCoefficient (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.boseCoefficient (d.boseCoefficientOne l) l := by
  have hv := (d.hasDerivAt_jetOne l).const_mul d.t
  have hg := d.hasDerivAt_boseReciprocal hr
  have hraw := ((hv.const_mul 10).const_add 14).add ((hv.mul hg).const_mul 8)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold boseCoefficient
    dsimp only
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · unfold boseCoefficientOne
    dsimp only

theorem hasDerivAt_boseCoefficientOne (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.boseCoefficientOne (d.boseCoefficientTwo l) l := by
  have hv := (d.hasDerivAt_jetOne l).const_mul d.t
  have hg := d.hasDerivAt_boseReciprocal hr
  have hg1 := d.hasDerivAt_boseReciprocalOne hr
  have hraw :=
    (((hg.const_mul (d.t * d.da)).add (hv.mul hg1)).const_mul 8).const_add
      (10 * (d.t * d.da))
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold boseCoefficientOne
    dsimp only
    simp only [Pi.add_apply, Pi.mul_apply]
  · unfold boseCoefficientTwo
    dsimp only
    ring

theorem hasDerivAt_boseCoefficientTwo (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.boseCoefficientTwo (d.boseCoefficientThree l) l := by
  have hv := (d.hasDerivAt_jetOne l).const_mul d.t
  have hg1 := d.hasDerivAt_boseReciprocalOne hr
  have hg2 := d.hasDerivAt_boseReciprocalTwo hr
  have hraw :=
    (((hg1.const_mul (2 * (d.t * d.da))).add (hv.mul hg2)).const_mul 8)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold boseCoefficientTwo
    dsimp only
    simp only [Pi.add_apply, Pi.mul_apply]
  · unfold boseCoefficientThree
    dsimp only
    ring

/-! ## Compensation curvature and highest-channel cancellation -/

def compensation (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  5 * d.velocitySlope l - d.boseCoefficient l * d.velocityCenter l

def compensationOne (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  5 * d.velocitySlopeOne l -
    d.boseCoefficientOne l * d.velocityCenter l -
    d.boseCoefficient l * d.velocityCenterOne l

def compensationTwo (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  5 * d.velocitySlopeTwo -
    d.boseCoefficientTwo l * d.velocityCenter l -
    2 * d.boseCoefficientOne l * d.velocityCenterOne l -
    d.boseCoefficient l * d.velocityCenterTwo

/-- Exact third-curvature balance.  No third displacement or second mixed-centre perturbation
survives. -/
def compensationThree (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  -(d.boseCoefficientThree l * d.velocityCenter l +
    3 * d.boseCoefficientTwo l * d.velocityCenterOne l +
    3 * d.boseCoefficientOne l * d.velocityCenterTwo)

theorem hasDerivAt_compensation (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.compensation (d.compensationOne l) l := by
  have hP := d.hasDerivAt_velocitySlope l
  have hB := d.hasDerivAt_boseCoefficient hr
  have hH := d.hasDerivAt_velocityCenter l
  have hraw := (hP.const_mul 5).sub (hB.mul hH)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold compensation
    simp only [Pi.mul_apply, Pi.sub_apply]
  · unfold compensationOne
    ring

theorem hasDerivAt_compensationOne (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.compensationOne (d.compensationTwo l) l := by
  have hP := d.hasDerivAt_velocitySlopeOne l
  have hB := d.hasDerivAt_boseCoefficient hr
  have hB1 := d.hasDerivAt_boseCoefficientOne hr
  have hH := d.hasDerivAt_velocityCenter l
  have hH1 := d.hasDerivAt_velocityCenterOne l
  have hraw := (((hP.const_mul 5).sub (hB1.mul hH)).sub (hB.mul hH1))
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold compensationOne
    simp only [Pi.mul_apply, Pi.sub_apply]
  · unfold compensationTwo
    ring

/-- **Third-curvature reduction.**  Differentiating the literal compensation twice leaves a third
derivative containing only the Bose coefficient and lower velocity transport.  The entire
velocity--slope numerator, hence both highest likelihood channels, cancels identically. -/
theorem hasDerivAt_compensationTwo (d : C5LikelihoodAffineData) {l : ℝ}
    (hr : Real.exp (d.action l) - 1 ≠ 0) :
    HasDerivAt d.compensationTwo (d.compensationThree l) l := by
  have hP := d.hasDerivAt_velocitySlopeTwo l
  have hB := d.hasDerivAt_boseCoefficient hr
  have hB1 := d.hasDerivAt_boseCoefficientOne hr
  have hB2 := d.hasDerivAt_boseCoefficientTwo hr
  have hH := d.hasDerivAt_velocityCenter l
  have hH1 := d.hasDerivAt_velocityCenterOne l
  have hH2 := d.hasDerivAt_velocityCenterTwo l
  have hraw :=
    (((((hP.const_mul 5).sub (hB2.mul hH)).sub
      ((hB1.mul hH1).const_mul 2)).sub (hB.mul hH2)))
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold compensationTwo
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  · unfold compensationThree
    ring

/-- Changing either highest displacement channel cannot alter third homotopy curvature.  This
kills every attempted `M'''` proof based on the favorable third likelihood reserve: that reserve
is essential to the margin and its first two jets, but cancels identically from the third. -/
theorem compensationThree_update_highest
    (d : C5LikelihoodAffineData) (c dc n dn l : ℝ) :
    ({ d with c := c, dc := dc, n := n, dn := dn }).compensationThree l =
      d.compensationThree l := by
  rfl

/-- Exact sign endpoint left after highest-channel cancellation. -/
theorem compensationThree_pos_iff_lowerTransportBalance_neg
    (d : C5LikelihoodAffineData) (l : ℝ) :
    0 < d.compensationThree l ↔
      d.boseCoefficientThree l * d.velocityCenter l +
        3 * d.boseCoefficientTwo l * d.velocityCenterOne l +
        3 * d.boseCoefficientOne l * d.velocityCenterTwo < 0 := by
  exact neg_pos

end C5LikelihoodAffineData

/-! ## Literal theta-source specialization -/

/-- Actual first-atom-to-full-theta affine jet packet. -/
def thetaCuspC5LikelihoodHomotopyData (u t : ℝ) : C5LikelihoodAffineData :=
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let z' := 2 * Real.sinh (2 * t)
  { t := t
    q := thetaCuspSingleAtomReflectedAction A t
    dq := thetaCuspReflectedLikelihoodCumulantAction u t
    a := thetaCuspSingleAtomReflectedActionJetOne A z z'
    da := thetaCuspReflectedLikelihoodCumulantJetOne u t
    b := thetaCuspSingleAtomReflectedActionJetTwo A z
    db := thetaCuspReflectedLikelihoodCumulantJetTwo u t
    c := thetaCuspSingleAtomReflectedActionJetThree A z z'
    dc := thetaCuspReflectedLikelihoodCumulantJetThree u t
    s := c5SingleAtomScaleActionJetOne A z
    ds := c5LikelihoodScaleActionJetOne u t
    m := c5SingleAtomScaleMixedJetOne A z z'
    dm := c5LikelihoodScaleMixedJetOne u t
    n := c5SingleAtomScaleMixedJetTwo A z
    dn := c5LikelihoodScaleMixedJetTwo u t }

/-- Literal compensation evaluated on the actual affine theta likelihood homotopy. -/
def thetaCuspC5LikelihoodHomotopyCompensation (u t l : ℝ) : ℝ :=
  (thetaCuspC5LikelihoodHomotopyData u t).compensation l

def thetaCuspC5LikelihoodHomotopyCompensationOne (u t l : ℝ) : ℝ :=
  (thetaCuspC5LikelihoodHomotopyData u t).compensationOne l

def thetaCuspC5LikelihoodHomotopyCompensationTwo (u t l : ℝ) : ℝ :=
  (thetaCuspC5LikelihoodHomotopyData u t).compensationTwo l

/-- The exact lower-transport expression equal to the literal third homotopy derivative. -/
def thetaCuspC5LikelihoodHomotopyCompensationThree (u t l : ℝ) : ℝ :=
  (thetaCuspC5LikelihoodHomotopyData u t).compensationThree l

/-- The left endpoint is exactly the already-proved first-atom compensation, not a surrogate. -/
theorem thetaCuspC5LikelihoodHomotopyCompensation_zero (u t : ℝ) :
    thetaCuspC5LikelihoodHomotopyCompensation u t 0 =
      c5SingleAtomCompensationMargin
        (thetaCuspSingleAtomReflectionScale 1 u) t := by
  unfold thetaCuspC5LikelihoodHomotopyCompensation
    thetaCuspC5LikelihoodHomotopyData
    C5LikelihoodAffineData.compensation
    C5LikelihoodAffineData.velocitySlope
    C5LikelihoodAffineData.velocityCenter
    C5LikelihoodAffineData.boseCoefficient
    C5LikelihoodAffineData.boseReciprocal
    C5LikelihoodAffineData.action
    C5LikelihoodAffineData.jetOne
    C5LikelihoodAffineData.jetTwo
    C5LikelihoodAffineData.jetThree
    C5LikelihoodAffineData.scaleAction
    C5LikelihoodAffineData.scaleMixedOne
    C5LikelihoodAffineData.scaleMixedTwo
    C5LikelihoodAffineData.affine
    c5SingleAtomCompensationMargin
    c5SingleAtomVelocityCenterNumerator
    c5SingleAtomVelocitySlopeCenterNumerator
  dsimp only
  ring_nf

/-- The right endpoint is exactly the literal completed theta compensation. -/
theorem thetaCuspC5LikelihoodHomotopyCompensation_one (u t : ℝ) :
    thetaCuspC5LikelihoodHomotopyCompensation u t 1 =
      c5CompletedCompensationMargin u t := by
  unfold thetaCuspC5LikelihoodHomotopyCompensation
    thetaCuspC5LikelihoodHomotopyData
    C5LikelihoodAffineData.compensation
    C5LikelihoodAffineData.velocitySlope
    C5LikelihoodAffineData.velocityCenter
    C5LikelihoodAffineData.boseCoefficient
    C5LikelihoodAffineData.boseReciprocal
    C5LikelihoodAffineData.action
    C5LikelihoodAffineData.jetOne
    C5LikelihoodAffineData.jetTwo
    C5LikelihoodAffineData.jetThree
    C5LikelihoodAffineData.scaleAction
    C5LikelihoodAffineData.scaleMixedOne
    C5LikelihoodAffineData.scaleMixedTwo
    C5LikelihoodAffineData.affine
    c5CompletedCompensationMargin
    c5CompletedVelocityCenterNumerator
    c5CompletedVelocitySlopeCenterNumerator
    thetaCuspCompletedReflectedCumulantAction
    thetaCuspCompletedReflectedCumulantJetOne
    thetaCuspCompletedReflectedCumulantJetTwo
    thetaCuspCompletedReflectedCumulantJetThree
    c5CompletedScaleActionJetOne
    c5CompletedScaleMixedJetOne
    c5CompletedScaleMixedJetTwo
  dsimp only
  ring_nf

theorem thetaCuspC5LikelihoodHomotopyAction_pos
    {u t l : ℝ} (ht : 0 < t) (htu : t ≤ u) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    0 < (thetaCuspC5LikelihoodHomotopyData u t).action l := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let q₀ := thetaCuspSingleAtomReflectedAction A t
  let dq := thetaCuspReflectedLikelihoodCumulantAction u t
  have hq₀ : 0 < q₀ := by
    simpa only [A, q₀] using
      thetaCuspSingleAtomReflectedAction_pos_of_sameHalfLine (n := 1) (by norm_num) ht htu
  have hfull : 0 < q₀ + dq := by
    have hintrinsic := thetaCuspReflectedLogAction_pos (u := u) ht
    rw [thetaCuspReflectedLogAction_eq_completed ht.le htu] at hintrinsic
    simpa only [q₀, dq, A, thetaCuspCompletedReflectedCumulantAction] using hintrinsic
  change 0 < q₀ + l * dq
  have heq : q₀ + l * dq = (1 - l) * q₀ + l * (q₀ + dq) := by ring
  rw [heq]
  by_cases hlast : l = 1
  · simpa only [hlast, sub_self, zero_mul, one_mul, zero_add] using hfull
  · have hlt : l < 1 := lt_of_le_of_ne hl1 hlast
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hlt) hq₀)
      (mul_nonneg hl0 hfull.le)

theorem thetaCuspC5LikelihoodHomotopy_exp_action_sub_one_ne
    {u t l : ℝ} (ht : 0 < t) (htu : t ≤ u) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Real.exp ((thetaCuspC5LikelihoodHomotopyData u t).action l) - 1 ≠ 0 := by
  have hq := thetaCuspC5LikelihoodHomotopyAction_pos ht htu hl0 hl1
  have hexp : 1 < Real.exp ((thetaCuspC5LikelihoodHomotopyData u t).action l) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hq
  linarith

theorem hasDerivAt_thetaCuspC5LikelihoodHomotopyCompensation
    {u t l : ℝ} (ht : 0 < t) (htu : t ≤ u) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    HasDerivAt (thetaCuspC5LikelihoodHomotopyCompensation u t)
      (thetaCuspC5LikelihoodHomotopyCompensationOne u t l) l := by
  exact (thetaCuspC5LikelihoodHomotopyData u t).hasDerivAt_compensation
    (thetaCuspC5LikelihoodHomotopy_exp_action_sub_one_ne ht htu hl0 hl1)

theorem hasDerivAt_thetaCuspC5LikelihoodHomotopyCompensationOne
    {u t l : ℝ} (ht : 0 < t) (htu : t ≤ u) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    HasDerivAt (thetaCuspC5LikelihoodHomotopyCompensationOne u t)
      (thetaCuspC5LikelihoodHomotopyCompensationTwo u t l) l := by
  exact (thetaCuspC5LikelihoodHomotopyData u t).hasDerivAt_compensationOne
    (thetaCuspC5LikelihoodHomotopy_exp_action_sub_one_ne ht htu hl0 hl1)

/-- Source-specialized third-curvature reduction.  This is the literal `M'''(l)` profile on the
closed likelihood segment, with all highest-channel dependence eliminated. -/
theorem hasDerivAt_thetaCuspC5LikelihoodHomotopyCompensationTwo
    {u t l : ℝ} (ht : 0 < t) (htu : t ≤ u) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    HasDerivAt (thetaCuspC5LikelihoodHomotopyCompensationTwo u t)
      (thetaCuspC5LikelihoodHomotopyCompensationThree u t l) l := by
  exact (thetaCuspC5LikelihoodHomotopyData u t).hasDerivAt_compensationTwo
    (thetaCuspC5LikelihoodHomotopy_exp_action_sub_one_ne ht htu hl0 hl1)

/-- Literal source `M'''` is positive exactly when the new three-term lower-transport balance is
negative.  No condition involving the third displacement or second mixed-centre likelihood jets
remains. -/
theorem thetaCuspC5LikelihoodHomotopyCompensationThree_pos_iff
    (u t l : ℝ) :
    0 < thetaCuspC5LikelihoodHomotopyCompensationThree u t l ↔
      let d := thetaCuspC5LikelihoodHomotopyData u t
      d.boseCoefficientThree l * d.velocityCenter l +
        3 * d.boseCoefficientTwo l * d.velocityCenterOne l +
        3 * d.boseCoefficientOne l * d.velocityCenterTwo < 0 := by
  exact C5LikelihoodAffineData.compensationThree_pos_iff_lowerTransportBalance_neg
    (thetaCuspC5LikelihoodHomotopyData u t) l

end

end RHTower
