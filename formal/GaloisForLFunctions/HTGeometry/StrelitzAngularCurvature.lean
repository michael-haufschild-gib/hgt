import GaloisForLFunctions.HTGeometry.StrelitzLogRadialDerivatives
import GaloisForLFunctions.HTGeometry.StrelitzMaximumModulusSet
import GaloisForLFunctions.HTGeometry.NevanlinnaCoeffFun
import GaloisForLFunctions.RHTower.Suzuki.SuzukiInteriorExcursionSpectralTurningPoint

/-!
# Angular curvature at Strelitz maximum points

Along the circle path `t ↦ z exp(it)`, the logarithmic modulus has first derivative
`-Im(z f'/f)`.  Differentiating once more gives
`-Re(z (z f'/f)')`.  At a maximum-modulus point this second derivative is nonpositive, so the
real part of the second Euler jet is nonnegative.  The final theorem derives every differentiability
condition internally for an entire coefficient sum.
-/

open Set Filter

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Angular derivative of the logarithmic modulus. -/
theorem hasDerivAt_log_norm_circlePath
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ} {t : ℝ}
    (hfz : f (circlePath z t) ≠ 0) :
    HasDerivAt (fun s => Real.log ‖f (circlePath z s)‖)
      (-(eulerLogDeriv f (circlePath z t)).im) t := by
  have hpath : HasDerivAt (circlePath z)
      (circlePath z t * Complex.I) t := by
    simpa [circlePath, mul_assoc] using hasDerivAt_circlePath z t
  have hcomp : HasDerivAt (fun s => f (circlePath z s))
      ((circlePath z t * Complex.I) * deriv f (circlePath z t)) t := by
    exact HasDerivAt.scomp t (hf (circlePath z t)).hasDerivAt hpath
  have hlog := RHTower.hasDerivAt_log_norm_comp hcomp hfz
  have hquot :
      ((circlePath z t * Complex.I) * deriv f (circlePath z t)) /
          f (circlePath z t) =
        Complex.I * eulerLogDeriv f (circlePath z t) := by
    rw [eulerLogDeriv]
    ring
  rw [hquot] at hlog
  simpa [Complex.mul_re] using hlog

/-- Angular derivative of `-Im(z f'/f)`. -/
theorem hasDerivAt_neg_im_eulerLogDeriv_circlePath
    {f : ℂ → ℂ} {z : ℂ} {t : ℝ}
    (hu : DifferentiableAt ℂ (eulerLogDeriv f) (circlePath z t)) :
    HasDerivAt (fun s => -(eulerLogDeriv f (circlePath z s)).im)
      (-(eulerLogDerivSecond f (circlePath z t)).re) t := by
  have hpath : HasDerivAt (circlePath z)
      (circlePath z t * Complex.I) t := by
    simpa [circlePath, mul_assoc] using hasDerivAt_circlePath z t
  have hcomp : HasDerivAt (fun s => eulerLogDeriv f (circlePath z s))
      ((circlePath z t * Complex.I) * deriv (eulerLogDeriv f) (circlePath z t)) t := by
    exact HasDerivAt.scomp t hu.hasDerivAt hpath
  have him : HasDerivAt
      (fun s => (eulerLogDeriv f (circlePath z s)).im)
      ((circlePath z t * Complex.I) *
        deriv (eulerLogDeriv f) (circlePath z t)).im t := by
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hcomp).congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  have hneg : HasDerivAt
      (fun s => -(eulerLogDeriv f (circlePath z s)).im)
      (-((circlePath z t * Complex.I) *
        deriv (eulerLogDeriv f) (circlePath z t)).im) t := him.neg
  have hjet :
      ((circlePath z t * Complex.I) * deriv (eulerLogDeriv f) (circlePath z t)).im =
        (eulerLogDerivSecond f (circlePath z t)).re := by
    rw [eulerLogDerivSecond]
    ring_nf
    simp [Complex.mul_im, Complex.mul_re]
    ring
  simpa [hjet] using hneg

/-- At a nonvanishing angular local maximum, the second Euler jet has nonnegative real part. -/
theorem eulerLogDerivSecond_re_nonneg_of_isLocalMax
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ}
    (hfz : f z ≠ 0)
    (hu : DifferentiableAt ℂ (eulerLogDeriv f) z)
    (hmax : IsLocalMax (fun t : ℝ => ‖f (circlePath z t)‖) 0) :
    0 ≤ (eulerLogDerivSecond f z).re := by
  let g : ℝ → ℝ := fun t => Real.log ‖f (circlePath z t)‖
  let q : ℝ → ℝ := fun t => -(eulerLogDeriv f (circlePath z t)).im
  have hfcont : ContinuousAt (fun t : ℝ => f (circlePath z t)) 0 := by
    have hpathdiff : Differentiable ℝ (circlePath z) :=
      fun t => (hasDerivAt_circlePath z t).differentiableAt
    have hpathcont : Continuous (circlePath z) := hpathdiff.continuous
    exact (hf.continuous.comp hpathcont).continuousAt
  have hfnonzero : ∀ᶠ t : ℝ in nhds 0, f (circlePath z t) ≠ 0 := by
    have h0 : f (circlePath z 0) ≠ 0 := by simpa using hfz
    exact hfcont.eventually_ne h0
  have hderivEq : deriv g =ᶠ[nhds 0] q := by
    filter_upwards [hfnonzero] with t ht
    exact (hasDerivAt_log_norm_circlePath hf ht).deriv
  have hq : HasDerivAt q (-(eulerLogDerivSecond f z).re) 0 := by
    have hu0 : DifferentiableAt ℂ (eulerLogDeriv f) (circlePath z 0) := by
      simpa using hu
    simpa [q] using hasDerivAt_neg_im_eulerLogDeriv_circlePath hu0
  have hsecond : deriv (deriv g) 0 = -(eulerLogDerivSecond f z).re := by
    calc
      deriv (deriv g) 0 = deriv q 0 := hderivEq.deriv_eq
      _ = -(eulerLogDerivSecond f z).re := hq.deriv
  have hmaxg : IsLocalMax g 0 := by
    filter_upwards [hmax, hfnonzero] with t htmax htnz
    dsimp [g]
    have htpos : 0 < ‖f (circlePath z t)‖ := norm_pos_iff.mpr htnz
    have hzpos : 0 < ‖f (circlePath z 0)‖ := by
      simpa using norm_pos_iff.mpr hfz
    exact Real.strictMonoOn_log.monotoneOn htpos hzpos htmax
  have hcontg : ContinuousAt g 0 :=
    (hasDerivAt_log_norm_circlePath hf (z := z) (t := 0) (by simpa using hfz)).continuousAt
  have hnonpos :=
    RHTower.suzukiSecondDeriv_nonpos_of_isLocalMax hmaxg hcontg
  rw [hsecond] at hnonpos
  linarith

/-- Every nonvanishing maximum-modulus point of an entire coefficient sum has nonnegative
second-Euler-jet real part. -/
theorem eulerLogDerivSecond_re_nonneg_of_mem_circleMaximumSet
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {z : ℂ}
    (hfz : coeffFun a z ≠ 0)
    (hmax : z ∈ circleMaximumSet (coeffFun a)) :
    0 ≤ (eulerLogDerivSecond (coeffFun a) z).re := by
  have hf : Differentiable ℂ (coeffFun a) := differentiable_coeffFun ha
  have hfa : AnalyticAt ℂ (coeffFun a) z :=
    GaloisForLFunctions.Nevanlinna.analyticOnNhd_coeffFun ha z (by simp)
  have hu : DifferentiableAt ℂ (eulerLogDeriv (coeffFun a)) z := by
    exact (differentiableAt_id.mul hfa.deriv.differentiableAt).div
      hfa.differentiableAt hfz
  apply eulerLogDerivSecond_re_nonneg_of_isLocalMax hf hfz hu
  filter_upwards [] with t
  rw [circlePath_zero]
  apply hmax
  simp [circlePath, Complex.norm_exp]

end

end GaloisForLFunctions.HTGeometry
