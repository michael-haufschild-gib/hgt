import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleBoundaryPrimitives

/-!
# Exact aperture differential laws for the Gamma pole boundary masses

The fixed-lower-endpoint primitives have explicit first and second derivatives
at every positive aperture. The logarithmic lower endpoint is handled solely by
integrability; the fundamental theorem of calculus is applied at the positive
upper endpoint. All exponential endpoint terms are retained in the weighted law.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RHTower

/-- Local derivative of the admitted boundary logarithm, away from its singular endpoint. -/
theorem hasDerivAt_ccmGammaPoleBoundaryLog {s : ℝ} (hs : 0<s) :
    HasDerivAt ccmGammaPoleBoundaryLog (-1/(Real.exp s-1)) s := by
  have hm : 1-Real.exp (-s)≠0 := ne_of_gt
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hE : Real.exp s-1≠0 := ne_of_gt
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr hs))
  have hd := ((((hasDerivAt_id s).neg.exp).const_sub 1).log hm).neg
  convert! hd using 1
  simp only [Pi.neg_apply,id_eq,neg_neg,mul_neg_one]
  rw [Real.exp_neg]
  field_simp

private theorem integral_upper_deriv (f : ℝ → ℝ) {s : ℝ}
    (hi : IntervalIntegrable f volume 0 (2*s)) (hm : Measurable f) (hc : ContinuousAt f (2*s)) :
    HasDerivAt (fun y => ∫ t in 0..2*y, f t) (2*f (2*s)) s := by
  have hd := (intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurable.stronglyMeasurableAtFilter hc).comp s
    ((hasDerivAt_id s).const_mul 2)
  convert! hd using 1
  ring

/-- The actual cross-boundary primitive has an elementary positive local slope. -/
theorem hasDerivAt_ccmGammaPoleCrossBoundaryPrimitive {s : ℝ} (hs : 0<s) :
    HasDerivAt ccmGammaPoleCrossBoundaryPrimitive (2*ccmGammaPoleBoundaryLog (2*s)) s := by
  exact integral_upper_deriv ccmGammaPoleBoundaryLog
    (intervalIntegrable_ccmGammaPoleBoundaryLog (by linarith))
    (by unfold ccmGammaPoleBoundaryLog; fun_prop)
    (hasDerivAt_ccmGammaPoleBoundaryLog (by linarith : 0<2*s)).continuousAt

/-- Exact second-order cross-boundary law at every positive aperture. -/
theorem deriv_deriv_ccmGammaPoleCrossBoundaryPrimitive {s : ℝ} (hs : 0<s) :
    deriv (deriv ccmGammaPoleCrossBoundaryPrimitive) s= -4/(Real.exp (2*s)-1) := by
  have hd : HasDerivAt (fun y => 2*ccmGammaPoleBoundaryLog (2*y))
      (-4/(Real.exp (2*s)-1)) s := by
    have h := ((hasDerivAt_ccmGammaPoleBoundaryLog (by linarith : 0<2*s)).comp s
      ((hasDerivAt_id s).const_mul 2)).const_mul 2
    convert! h using 1
    ring
  have he : (fun y => 2*ccmGammaPoleBoundaryLog (2*y)) =ᶠ[𝓝 s]
      deriv ccmGammaPoleCrossBoundaryPrimitive := by
    filter_upwards [eventually_gt_nhds hs] with y hy
    exact (hasDerivAt_ccmGammaPoleCrossBoundaryPrimitive hy).deriv.symm
  exact (hd.congr_of_eventuallyEq he.symm).deriv

private def leftPrimitive (s : ℝ) : ℝ :=
  ∫ t in 0..2*s, Real.exp (-t)*ccmGammaPoleBoundaryLog (2*t)

private def rightPrimitive (s : ℝ) : ℝ :=
  ∫ t in 0..2*s, Real.exp t*(ccmGammaPoleBoundaryLog t-ccmGammaPoleBoundaryLog (2*t)/2)

private def leftResponse (s : ℝ) : ℝ := Real.exp s/2*leftPrimitive s
private def rightResponse (s : ℝ) : ℝ := Real.exp (-s)*rightPrimitive s

private theorem leftPrimitive_deriv {s : ℝ} (hs : 0<s) :
    HasDerivAt leftPrimitive (2*(Real.exp (-(2*s))*ccmGammaPoleBoundaryLog (4*s))) s := by
  have hi := (intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (show 0<2*s by linarith)).continuousOn_mul
    (show ContinuousOn (fun t : ℝ => Real.exp (-t)) (uIcc 0 (2*s)) by fun_prop)
  have hl : ContinuousAt (fun t => ccmGammaPoleBoundaryLog (2*t)) (2*s) :=
    (hasDerivAt_ccmGammaPoleBoundaryLog (by linarith : 0<2*(2*s))).continuousAt.comp
      (by fun_prop)
  have hc : ContinuousAt (fun t => Real.exp (-t)*ccmGammaPoleBoundaryLog (2*t)) (2*s) :=
    (by fun_prop : ContinuousAt (fun t : ℝ => Real.exp (-t)) (2*s)).mul hl
  simpa only [leftPrimitive,show 2*(2*s)=4*s by ring] using! integral_upper_deriv _ hi
    (by unfold ccmGammaPoleBoundaryLog; fun_prop) hc

private theorem rightPrimitive_deriv {s : ℝ} (hs : 0<s) :
    HasDerivAt rightPrimitive
      (2*(Real.exp (2*s)*(ccmGammaPoleBoundaryLog (2*s)-ccmGammaPoleBoundaryLog (4*s)/2))) s := by
  have hi := ((intervalIntegrable_ccmGammaPoleBoundaryLog (show 0<2*s by linarith)).sub
    ((intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (show 0<2*s by linarith)).div_const 2)).continuousOn_mul
    (show ContinuousOn Real.exp (uIcc 0 (2*s)) by fun_prop)
  have h1 := (hasDerivAt_ccmGammaPoleBoundaryLog (by linarith : 0<2*s)).continuousAt
  have h2 : ContinuousAt (fun t => ccmGammaPoleBoundaryLog (2*t)) (2*s) :=
    (hasDerivAt_ccmGammaPoleBoundaryLog (by linarith : 0<2*(2*s))).continuousAt.comp (by fun_prop)
  have hc := Real.continuous_exp.continuousAt.mul (h1.sub (h2.div_const 2))
  simpa only [rightPrimitive,Pi.sub_apply,show 2*(2*s)=4*s by ring] using! integral_upper_deriv _ hi
    (by unfold ccmGammaPoleBoundaryLog; fun_prop) hc

private theorem leftResponse_deriv {s : ℝ} (hs : 0<s) :
    HasDerivAt leftResponse
      (leftResponse s+Real.exp (-s)*ccmGammaPoleBoundaryLog (4*s)) s := by
  have hd := ((Real.hasDerivAt_exp s).div_const 2).mul (leftPrimitive_deriv hs)
  convert! hd using 1
  dsimp [leftResponse]
  have he : Real.exp s*Real.exp (-(2*s))=Real.exp (-s) := by
    rw [← Real.exp_add,show s+(-(2*s))= -s by ring]
  nlinarith [congrArg (fun x => x*ccmGammaPoleBoundaryLog (4*s)) he]

private theorem rightResponse_deriv {s : ℝ} (hs : 0<s) :
    HasDerivAt rightResponse
      (-rightResponse s+2*Real.exp s*(ccmGammaPoleBoundaryLog (2*s)-ccmGammaPoleBoundaryLog (4*s)/2)) s := by
  have hd := ((hasDerivAt_id s).neg.exp).mul (rightPrimitive_deriv hs)
  convert! hd using 1
  dsimp [rightResponse]
  have he : Real.exp (-s)*Real.exp (2*s)=Real.exp s := by
    rw [← Real.exp_add,show -s+2*s=s by ring]
  nlinarith [congrArg (fun x => x*(ccmGammaPoleBoundaryLog (2*s)-ccmGammaPoleBoundaryLog (4*s)/2)) he]

/-- Exact first derivative of the weighted boundary primitive, with all endpoint terms retained. -/
def ccmGammaPoleSelfBoundarySlope (s : ℝ) : ℝ :=
  leftResponse s-rightResponse s+Real.exp (-s)*ccmGammaPoleBoundaryLog (4*s)+
    2*Real.exp s*(ccmGammaPoleBoundaryLog (2*s)-ccmGammaPoleBoundaryLog (4*s)/2)

theorem hasDerivAt_ccmGammaPoleSelfBoundaryPrimitive {s : ℝ} (hs : 0<s) :
    HasDerivAt ccmGammaPoleSelfBoundaryPrimitive (ccmGammaPoleSelfBoundarySlope s) s := by
  convert! (leftResponse_deriv hs).add (rightResponse_deriv hs) using 1
  unfold ccmGammaPoleSelfBoundarySlope
  ring

private theorem forcing_scalar_identity {s : ℝ} (hs : 0<s) :
    -4*Real.exp (-s)/(Real.exp (4*s)-1)+
      4*Real.exp s*(-1/(Real.exp (2*s)-1)+1/(Real.exp (4*s)-1)) =
      -4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1) := by
  have h2 : Real.exp (2*s)-1≠0 := ne_of_gt
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
  have h4 : Real.exp (4*s)-1≠0 := ne_of_gt
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
  rw [show 4*s=(s+s)+(s+s) by ring] at h4 ⊢
  rw [show 2*s=s+s by ring] at h2 ⊢
  simp only [Real.exp_add] at h2 h4 ⊢
  rw [Real.exp_neg]
  ring_nf at h2 h4 ⊢
  field_simp [h2,h4]
  ring

/-- The weighted Gamma boundary slope has an exact second-order differential law. -/
theorem hasDerivAt_ccmGammaPoleSelfBoundarySlope {s : ℝ} (hs : 0<s) :
    HasDerivAt ccmGammaPoleSelfBoundarySlope
      (ccmGammaPoleSelfBoundaryPrimitive s-
        4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1)) s := by
  have h2 : HasDerivAt (fun y => ccmGammaPoleBoundaryLog (2*y))
      (-2/(Real.exp (2*s)-1)) s := by
    convert! (hasDerivAt_ccmGammaPoleBoundaryLog (by linarith : 0<2*s)).comp s
      ((hasDerivAt_id s).const_mul 2) using 1
    ring
  have h4 : HasDerivAt (fun y => ccmGammaPoleBoundaryLog (4*y))
      (-4/(Real.exp (4*s)-1)) s := by
    convert! (hasDerivAt_ccmGammaPoleBoundaryLog (by linarith : 0<4*s)).comp s
      ((hasDerivAt_id s).const_mul 4) using 1
    ring
  have he : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-s)) s := by
    simpa only [Pi.neg_apply,id_eq,mul_neg_one] using! (hasDerivAt_id s).neg.exp
  have hleft := he.mul h4
  have hright := ((Real.hasDerivAt_exp s).const_mul 2).mul (h2.sub (h4.div_const 2))
  convert! (((leftResponse_deriv hs).sub (rightResponse_deriv hs)).add hleft).add hright using 1
  change leftResponse s+rightResponse s-
    4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1) = _
  have hf := forcing_scalar_identity hs
  simp only [Pi.sub_apply]
  linear_combination -hf

/-- Exact shifted second derivative of the actual weighted boundary primitive. -/
theorem deriv_deriv_ccmGammaPoleSelfBoundaryPrimitive_sub {s : ℝ} (hs : 0<s) :
    deriv (deriv ccmGammaPoleSelfBoundaryPrimitive) s-ccmGammaPoleSelfBoundaryPrimitive s =
      -4*Real.exp (-s)*(1+Real.exp (4*s))/(Real.exp (4*s)-1) := by
  have he : deriv ccmGammaPoleSelfBoundaryPrimitive =ᶠ[𝓝 s] ccmGammaPoleSelfBoundarySlope := by
    filter_upwards [eventually_gt_nhds hs] with y hy
    exact (hasDerivAt_ccmGammaPoleSelfBoundaryPrimitive hy).deriv
  rw [((hasDerivAt_ccmGammaPoleSelfBoundarySlope hs).congr_of_eventuallyEq he).deriv]
  ring

end RHTower
