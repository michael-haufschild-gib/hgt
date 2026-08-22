import GaloisForLFunctions.RHTower.ThetaTiltReflectedWork
import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxSourceWeld
import GaloisForLFunctions.RHTower.XiShiftLoewnerEulerSplit

/-!
# Global strict log-convexity of the completed theta source

The abstract theta-source interface has faster-than-every-exponential decay, but the earlier
real-tilt moment API exposed strict variance only on `|a| < 1`.  This module removes that artificial
window.  An all-order bilateral Laplace moment differentiates to its successor on the whole plane.
For the literal completed theta source, every real tilt therefore has a strictly positive Hankel
discriminant and variance.

The global theta-source weld identifies its partition function with centered Xi.  Consequently the
real centered Xi logarithmic derivative is the mean of a positive full-support exponential family
and is strictly increasing on all of `ℝ`.  This is unconditional; it is a real-axis source law and
does not constrain nonreal zeros.
-/

open Complex MeasureTheory Set Filter Topology Real

namespace RHTower

noncomputable section

/-- All-order bilateral Laplace moment of a theta source. -/
def thetaSourceLaplaceMoment (S : ThetaSource) (m : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (w * (x : ℂ))

/-- Whole-plane moment ladder: each bilateral Laplace moment differentiates to its successor. -/
theorem hasDerivAt_thetaSourceLaplaceMoment (S : ThetaSource) (m : ℕ) (w : ℂ) :
    HasDerivAt (thetaSourceLaplaceMoment S m)
      (thetaSourceLaplaceMoment S (m + 1) w) w := by
  obtain ⟨C, _, hbd⟩ := S.exists_ball_bound w (m + 1)
  have hF : ∀ u : ℂ, AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (u * (x : ℂ))) volume :=
    fun u => (S.continuous_integrand u m).aestronglyMeasurable
  have hF' : AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) ^ (m + 1) * (S.k x : ℂ) *
        Complex.exp (w * (x : ℂ))) volume :=
    (S.continuous_integrand w (m + 1)).aestronglyMeasurable
  have hdiff : ∀ x : ℝ, ∀ u : ℂ, HasDerivAt
      (fun v : ℂ => (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (v * (x : ℂ)))
      ((x : ℂ) ^ (m + 1) * (S.k x : ℂ) * Complex.exp (u * (x : ℂ))) u := by
    intro x u
    have h := (hasDerivAt_laplace_integrand S x u).const_mul ((x : ℂ) ^ m)
    have heq : (fun v : ℂ =>
        (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (v * (x : ℂ))) =ᶠ[nhds u]
        (fun v : ℂ => (x : ℂ) ^ m *
          ((S.k x : ℂ) * Complex.exp (v * (x : ℂ)))) :=
      Filter.Eventually.of_forall fun v => by ring
    refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [pow_succ]
    ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (u : ℂ) (x : ℝ) =>
      (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (u * (x : ℂ)))
    (F' := fun (u : ℂ) (x : ℝ) =>
      (x : ℂ) ^ (m + 1) * (S.k x : ℂ) * Complex.exp (u * (x : ℂ)))
    (x₀ := w) (bound := fun x : ℝ => C * (|x| ^ (m + 1) * Real.exp (-1 * |x|)))
    (Metric.ball_mem_nhds w one_pos)
    (Filter.Eventually.of_forall hF)
    (S.integrable_mul_exp w m)
    hF'
    (Filter.Eventually.of_forall fun x u hu =>
      hbd u (le_of_lt (by simpa [Complex.dist_eq] using hu)) x)
    ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs (m + 1) one_pos).const_mul C)
    (Filter.Eventually.of_forall fun x u _ => hdiff x u)
  exact hres.2

/-- Complex source moments restrict to the existing real theta-tilt moments. -/
theorem thetaSourceLaplaceMoment_cusp_ofReal (a : ℝ) (m : ℕ) :
    thetaSourceLaplaceMoment thetaCuspTiltSource m (a : ℂ) =
      (thetaTiltMoment a m : ℂ) := by
  rw [thetaSourceLaplaceMoment, thetaTiltMoment]
  calc
    (∫ x : ℝ, (x : ℂ) ^ m * (thetaCuspTiltSource.k x : ℂ) *
        Complex.exp ((a : ℂ) * (x : ℂ))) =
        ∫ x : ℝ, ((x ^ m * Real.exp (a * x) * thetaCuspFullSource x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [thetaCuspTiltSource_k, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
        ← Complex.ofReal_pow]
      push_cast
      ring
    _ = ((∫ x : ℝ, x ^ m * Real.exp (a * x) * thetaCuspFullSource x : ℝ) : ℂ) :=
      integral_ofReal

/-- The real theta moment ladder is differentiable at every tilt, not only `|a| < 1`. -/
theorem hasDerivAt_thetaTiltMoment_global (a : ℝ) (m : ℕ) :
    HasDerivAt (fun t : ℝ => thetaTiltMoment t m) (thetaTiltMoment a (m + 1)) a := by
  have hc := hasDerivAt_thetaSourceLaplaceMoment thetaCuspTiltSource m (a : ℂ)
  have hcR := hc.comp_ofReal
  have hr : HasDerivAt
      (fun y : ℝ => (thetaSourceLaplaceMoment thetaCuspTiltSource m (y : ℂ)).re)
      (thetaSourceLaplaceMoment thetaCuspTiltSource (m + 1) (a : ℂ)).re a :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hcR
  simpa only [thetaSourceLaplaceMoment_cusp_ofReal, Complex.ofReal_re] using hr

/-- Every polynomial moment of every real theta tilt is integrable. -/
theorem integrable_thetaTiltIntegrand_global (a : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (a * x) * thetaCuspFullSource x) := by
  have hc := thetaCuspTiltSource.integrable_mul_exp (a : ℂ) k
  have hr := hc.re
  refine hr.congr (Filter.Eventually.of_forall fun x => ?_)
  change ((x : ℂ) ^ k * (thetaCuspTiltSource.k x : ℂ) *
    Complex.exp ((a : ℂ) * (x : ℂ))).re = _
  rw [thetaCuspTiltSource_k, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Partition function is strictly positive at every real tilt. -/
theorem thetaTiltMoment_zero_pos_global (a : ℝ) : 0 < thetaTiltMoment a 0 := by
  have hpos : ∀ x : ℝ, 0 < x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x := by
    intro x
    positivity [thetaCuspFullSource_pos_all x]
  rw [thetaTiltMoment,
    integral_pos_iff_support_of_nonneg (fun x => (hpos x).le)
      (integrable_thetaTiltIntegrand_global a 0)]
  have hsupp : (Function.support
      fun x : ℝ => x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hpos x).ne'
  rw [hsupp]
  simp

theorem integrable_pow_thetaTiltMeasure_global (a : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (thetaTiltMeasure a) := by
  rw [thetaTiltMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      (measurable_thetaTiltDensity a).aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (thetaTiltDensity_pos a _).le, smul_eq_mul]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    integrable_thetaTiltIntegrand_global a k

/-- Every finite Hankel matrix of every real theta tilt is strictly positive definite. -/
theorem det_thetaTilt_momentHankelMatrix_pos_global (a : ℝ) (n : ℕ) :
    0 < (HTGeometry.momentHankelMatrix (thetaTiltMoment a) n).det :=
  (HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
    (thetaTiltMoment a) (fun k => thetaTiltMoment_eq_integral_measure k)
    (integrable_pow_thetaTiltMeasure_global a)
    (thetaTiltMeasure_compl_finset_pos a) n).det_pos

/-- Every real exponential tilt of the completed theta source has strictly positive variance. -/
theorem thetaTiltVariance_pos_global (a : ℝ) : 0 < thetaTiltVariance a := by
  have hdet := det_thetaTilt_momentHankelMatrix_pos_global a 2
  have hdisc : 0 < thetaTiltMoment a 0 * thetaTiltMoment a 2 - thetaTiltMoment a 1 ^ 2 := by
    simpa [HTGeometry.momentHankelMatrix, Matrix.det_fin_two, pow_two] using hdet
  have h0 := thetaTiltMoment_zero_pos_global a
  rw [thetaTiltVariance, thetaTiltMean]
  rw [show thetaTiltMoment a 2 / thetaTiltMoment a 0
      - (thetaTiltMoment a 1 / thetaTiltMoment a 0) ^ 2
      = (thetaTiltMoment a 0 * thetaTiltMoment a 2 - thetaTiltMoment a 1 ^ 2)
        / thetaTiltMoment a 0 ^ 2 by field_simp [h0.ne']]
  positivity

/-- Derivative of global theta-tilt mean is its strictly positive variance. -/
theorem hasDerivAt_thetaTiltMean_global (a : ℝ) :
    HasDerivAt thetaTiltMean (thetaTiltVariance a) a := by
  have h1 := hasDerivAt_thetaTiltMoment_global a 1
  have h0 := hasDerivAt_thetaTiltMoment_global a 0
  have hpos := thetaTiltMoment_zero_pos_global a
  have hdiv := h1.div h0 (ne_of_gt hpos)
  refine hdiv.congr_deriv ?_
  rw [thetaTiltVariance, thetaTiltMean]
  field_simp

/-- Centered Xi real logarithmic derivative is the global theta-tilt mean. -/
theorem thetaTiltMean_eq_xiRealLogDeriv (a : ℝ) :
    thetaTiltMean a = xiRealLogDeriv a := by
  rw [xiRealLogDeriv, ← logDeriv_xiCent, logDeriv_apply]
  have hfun : xiCent = bilateralLaplace thetaCuspTiltSource := by
    funext w
    exact (bilateralLaplace_thetaCuspTiltSource_eq_xiCent w).symm
  rw [hfun, deriv_bilateralLaplace]
  have hzero : bilateralLaplace thetaCuspTiltSource (a : ℂ) =
      (thetaTiltMoment a 0 : ℂ) := by
    simpa [thetaSourceLaplaceMoment, bilateralLaplace] using
      thetaSourceLaplaceMoment_cusp_ofReal a 0
  have hone : bilateralLaplaceDeriv thetaCuspTiltSource (a : ℂ) =
      (thetaTiltMoment a 1 : ℂ) := by
    simpa [thetaSourceLaplaceMoment, bilateralLaplaceDeriv] using
      thetaSourceLaplaceMoment_cusp_ofReal a 1
  rw [hzero, hone, thetaTiltMean]
  have h0 := thetaTiltMoment_zero_pos_global a
  simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    Complex.normSq_ofReal]
  field_simp [h0.ne']
  ring

/-- Global real-axis strict convexity law for completed Xi. -/
theorem strictMono_xiRealLogDeriv : StrictMono xiRealLogDeriv := by
  have hmean : StrictMono thetaTiltMean := strictMono_of_deriv_pos fun a => by
    rw [(hasDerivAt_thetaTiltMean_global a).deriv]
    exact thetaTiltVariance_pos_global a
  intro a b hab
  rw [← thetaTiltMean_eq_xiRealLogDeriv,
    ← thetaTiltMean_eq_xiRealLogDeriv]
  exact hmean hab

/-- Functional-equation parity of the centered real logarithmic derivative. -/
theorem xiRealLogDeriv_neg (u : ℝ) :
    xiRealLogDeriv (-u) = -xiRealLogDeriv u := by
  have h := re_logDeriv_xi_reflect_line (1 / 2 + u) 0
  norm_num only [ofReal_zero, zero_mul, add_zero] at h
  have hleft : ((1 - (1 / 2 + u) : ℝ) : ℂ) =
      (1 / 2 : ℂ) + ((-u : ℝ) : ℂ) := by
    push_cast
    ring
  have hright : (((1 / 2 + u : ℝ) : ℂ)) =
      (1 / 2 : ℂ) + (u : ℂ) := by
    push_cast
    ring
  rw [hleft, hright] at h
  exact h

end

end RHTower
