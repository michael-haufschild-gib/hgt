import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma46
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Differentiability of Suzuki's literal canonical kernel

This module begins the analytic dependency closure for Suzuki (2012), Lemma `lem_ad1`.  It proves
the exact derivative of the incomplete-beta tail on `(0,1)` directly from the fundamental theorem
of calculus.  No smooth proxy replaces Suzuki's printed kernel.
-/

open ArithmeticFunction Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Integrand in Suzuki's literal incomplete-beta tail. -/
def suzukiBetaTailIntegrand (omega t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
    (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)

/-- Interior continuity of the exact beta-tail integrand. -/
theorem continuousAt_suzukiBetaTailIntegrand
    {omega t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ContinuousAt (suzukiBetaTailIntegrand omega) t := by
  exact ((continuousAt_cpow_const
      (Complex.ofReal_mem_slitPlane.2 ht0)).comp
        Complex.continuous_ofReal.continuousAt).mul
    ((continuousAt_cpow_const
      (Complex.ofReal_mem_slitPlane.2 (by linarith : 0 < 1 - t))).comp_of_eq
        (show ContinuousAt (fun u : ℝ => (1 : ℂ) - (u : ℂ)) t from
          continuousAt_const.sub Complex.continuous_ofReal.continuousAt) (by push_cast; rfl))

/-- On `[0,1]`, Suzuki's set integral is the corresponding oriented interval integral. -/
theorem suzukiBetaTail_eq_intervalIntegral
    {omega x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    suzukiBetaTail omega x =
      ∫ t in x ^ 2..1, suzukiBetaTailIntegrand omega t := by
  rw [suzukiBetaTail]
  change (∫ t in Ioc (x ^ 2) 1, suzukiBetaTailIntegrand omega t) = _
  have hsq : x ^ 2 ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ hx0 zero_le_one).2 hx1
  simpa only [one_pow] using (intervalIntegral.integral_of_le hsq).symm

/-- Exact derivative of Suzuki's incomplete-beta tail on its open support.  The displayed
continuous-linear-map application is scalar multiplication of the beta integrand by `2x`, with
the minus sign from differentiating the lower integration endpoint. -/
theorem hasDerivAt_suzukiBetaTail
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (suzukiBetaTail omega)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (-suzukiBetaTailIntegrand omega (x ^ 2))) (2 * x)) x := by
  have hIntOn := integrableOn_suzukiBetaIntegrand_Ioc (omega := omega) (delta := x)
    (by linarith) hx0 hx1
  have hsq : x ^ 2 ≤ (1 : ℝ) := by nlinarith
  have hInt : IntervalIntegrable (suzukiBetaTailIntegrand omega) volume (x ^ 2) 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hsq).2
    change IntegrableOn (suzukiBetaTailIntegrand omega) (Ioc (x ^ 2) 1) at hIntOn
    exact hIntOn
  have hcont := continuousAt_suzukiBetaTailIntegrand (omega := omega)
    (sq_pos_of_pos hx0) (by nlinarith)
  have hlower : HasDerivAt
      (fun u => ∫ t in u..1, suzukiBetaTailIntegrand omega t)
      (-suzukiBetaTailIntegrand omega (x ^ 2)) (x ^ 2) :=
    intervalIntegral.integral_hasDerivAt_left hInt
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun t ht => continuousAt_suzukiBetaTailIntegrand ht.1 ht.2)
        (x ^ 2) ⟨sq_pos_of_pos hx0, by nlinarith⟩) hcont
  have hsquare := hasDerivAt_pow 2 x
  have hcomp := hlower.hasFDerivAt.comp_hasDerivAt_of_eq x hsquare rfl
  have hev : suzukiBetaTail omega =ᶠ[𝓝 x]
      fun z => ∫ t in z ^ 2..1, suzukiBetaTailIntegrand omega t := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with z hz
    exact suzukiBetaTail_eq_intervalIntegral hz.1.le hz.2.le
  simpa only [Function.comp_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] using
    hcomp.congr_of_eventuallyEq hev

/-- Explicit derivative field of the incomplete-beta tail. -/
def suzukiBetaTailDerivative (omega x : ℝ) : ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    (-suzukiBetaTailIntegrand omega (x ^ 2))) (2 * x)

theorem suzukiBetaTailDerivative_eq_smul (omega x : ℝ) :
    suzukiBetaTailDerivative omega x =
      (2 * x : ℝ) • (-suzukiBetaTailIntegrand omega (x ^ 2)) := by
  rfl

/-- Real-coordinate formula for the beta-tail derivative.  Unlike the complex-power presentation,
this formula extends continuously to the endpoint `x = 1` when `omega > 1`. -/
def suzukiBetaTailDerivativeRealFormula (omega x : ℝ) : ℂ :=
  (2 * x : ℝ) •
    (-((((x ^ 2) ^ (1 / 2 - omega) : ℝ) : ℂ) *
      (((1 - x ^ 2) ^ (omega - 1) : ℝ) : ℂ)))

theorem suzukiBetaTailDerivative_eq_realFormula
    {omega x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    suzukiBetaTailDerivative omega x =
      suzukiBetaTailDerivativeRealFormula omega x := by
  rw [suzukiBetaTailDerivative_eq_smul, suzukiBetaTailDerivativeRealFormula,
    suzukiBetaTailIntegrand]
  have hq : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [← Complex.ofReal_cpow (sq_nonneg x) (1 / 2 - omega)]
  have he : ((omega : ℂ) - 1) = ((omega - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_cpow hq (omega - 1)]

/-- Continuous endpoint extension of the exact beta-tail derivative on any compact subinterval
away from `0`. -/
theorem continuousOn_suzukiBetaTailDerivativeRealFormula
    {omega delta : ℝ} (homega : 1 < omega) (hdelta0 : 0 < delta) :
    ContinuousOn (suzukiBetaTailDerivativeRealFormula omega) (Icc delta 1) := by
  have hx2 : ContinuousOn (fun x : ℝ => (x ^ 2) ^ (1 / 2 - omega))
      (Icc delta 1) := by
    apply (continuousOn_id.pow 2).rpow_const
    intro x hx
    left
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hdelta0 hx.1))
  have hq : ContinuousOn (fun x : ℝ => (1 - x ^ 2) ^ (omega - 1))
      (Icc delta 1) := by
    apply (continuousOn_const.sub (continuousOn_id.pow 2)).rpow_const
    intro x _
    right
    linarith
  have hcx2 : ContinuousOn
      (fun x : ℝ => (((x ^ 2) ^ (1 / 2 - omega) : ℝ) : ℂ)) (Icc delta 1) := by
    exact (Complex.ofRealCLM.continuous.comp_continuousOn hx2).congr
      (fun x _ => by simp [Function.comp_apply])
  have hcq : ContinuousOn
      (fun x : ℝ => (((1 - x ^ 2) ^ (omega - 1) : ℝ) : ℂ)) (Icc delta 1) := by
    exact (Complex.ofRealCLM.continuous.comp_continuousOn hq).congr
      (fun x _ => by simp [Function.comp_apply])
  unfold suzukiBetaTailDerivativeRealFormula
  exact (continuousOn_const.mul continuousOn_id).smul (hcx2.mul hcq).neg

/-- The exact beta-tail derivative varies continuously on the open support. -/
theorem continuousOn_suzukiBetaTailDerivative
    (omega : ℝ) : ContinuousOn (suzukiBetaTailDerivative omega) (Ioo 0 1) := by
  intro x hx
  have hform : suzukiBetaTailDerivative omega = fun z : ℝ =>
      (2 * z : ℝ) • (-suzukiBetaTailIntegrand omega (z ^ 2)) := by
    funext z
    exact suzukiBetaTailDerivative_eq_smul omega z
  rw [hform]
  have hinner : ContinuousAt
      (fun z : ℝ => suzukiBetaTailIntegrand omega (z ^ 2)) x :=
    (continuousAt_suzukiBetaTailIntegrand (sq_pos_of_pos hx.1)
      (by simpa only [one_pow] using (sq_lt_sq₀ hx.1.le zero_le_one).2 hx.2)).comp_of_eq
        (hasDerivAt_pow 2 x).continuousAt rfl
  exact ((continuousAt_const.mul continuousAt_id).smul hinner.neg).continuousWithinAt

theorem deriv_suzukiBetaTail
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x) (hx1 : x < 1) :
    deriv (suzukiBetaTail omega) x = suzukiBetaTailDerivative omega x := by
  exact (hasDerivAt_suzukiBetaTail homega hx0 hx1).deriv

/-- Suzuki's literal incomplete-beta tail is continuously differentiable on `(0,1)`. -/
theorem contDiffOn_one_suzukiBetaTail
    {omega : ℝ} (homega : 1 < omega) :
    ContDiffOn ℝ 1 (suzukiBetaTail omega) (Ioo 0 1) := by
  refine (contDiffOn_succ_iff_derivWithin (n := 0) isOpen_Ioo.uniqueDiffOn).2
    ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (hasDerivAt_suzukiBetaTail homega hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro h
    norm_num at h
  · rw [contDiffOn_zero]
    refine (continuousOn_suzukiBetaTailDerivative omega).congr ?_
    intro x hx
    rw [derivWithin_of_isOpen isOpen_Ioo hx,
      deriv_suzukiBetaTail homega hx.1 hx.2]

/-- Real-coordinate smooth formula for Suzuki's literal `g_omega` on `(0,1)`. -/
def suzukiSourceGSmoothFormula (omega x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) ^ (omega : ℂ) /
      Complex.Gamma (omega : ℂ)) *
    ((((x ^ (2 - omega : ℝ) : ℝ) : ℂ) *
        (((1 - x ^ 2) ^ (omega - 1 : ℝ) : ℝ) : ℂ)) -
      (omega : ℂ) * (((x ^ (omega - 1 : ℝ) : ℝ) : ℂ)) *
        suzukiBetaTail omega x)

/-- Exact derivative field of Suzuki's printed `g_omega` on `(0,1)`.  The factor
`(1 - x^(2 : ℕ))^(omega - 2)` is the only potentially unbounded term at the support endpoint.  Its
exponent is greater than `-1` exactly in Suzuki's range `omega > 1`, which is the local `L¹`
mechanism used in `lem_ad1`. -/
def suzukiSourceGDerivative (omega x : ℝ) : ℂ :=
  let C : ℂ := 2 * (Real.pi : ℂ) ^ (omega : ℂ) / Complex.Gamma (omega : ℂ)
  let p' : ℂ := (((2 - omega) * x ^ (1 - omega) : ℝ) : ℂ)
  let q : ℂ := (((1 - x ^ 2) ^ (omega - 1) : ℝ) : ℂ)
  let p : ℂ := (((x ^ (2 - omega) : ℝ) : ℂ))
  let q' : ℂ := (((-2 * x) * (omega - 1) *
    (1 - x ^ 2) ^ (omega - 2) : ℝ) : ℂ)
  let r' : ℂ := (((omega - 1) * x ^ (omega - 2) : ℝ) : ℂ)
  let r : ℂ := (((x ^ (omega - 1) : ℝ) : ℂ))
  C * ((p' * q + p * q') -
    (((omega : ℂ) * r') * suzukiBetaTail omega x +
      ((omega : ℂ) * r) * suzukiBetaTailDerivative omega x))

/-- Exact differentiation of the source-faithful smooth formula for `g_omega`. -/
theorem hasDerivAt_suzukiSourceGSmoothFormula
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (suzukiSourceGSmoothFormula omega)
      (suzukiSourceGDerivative omega x) x := by
  have hxpow : HasDerivAt (fun z : ℝ => z ^ (2 - omega))
      ((2 - omega) * x ^ (1 - omega)) x := by
    convert Real.hasDerivAt_rpow_const (x := x) (p := 2 - omega)
      (Or.inl hx0.ne') using 1 <;> first | rfl | ring
  have hq : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    change HasDerivAt ((fun _ : ℝ => 1) - fun z : ℝ => z ^ 2) (-2 * x) x
    apply ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).congr_deriv
    norm_num
  have hq0 : 0 < 1 - x ^ 2 := by nlinarith
  have hqpow : HasDerivAt (fun z : ℝ => (1 - z ^ 2) ^ (omega - 1))
      ((-2 * x) * (omega - 1) * (1 - x ^ 2) ^ (omega - 2)) x := by
    convert hq.rpow_const (p := omega - 1) (Or.inl hq0.ne') using 1 <;>
      first | rfl | ring
  have homegapow : HasDerivAt (fun z : ℝ => z ^ (omega - 1))
      ((omega - 1) * x ^ (omega - 2)) x := by
    convert Real.hasDerivAt_rpow_const (x := x) (p := omega - 1)
      (Or.inl hx0.ne') using 1 <;> first | rfl | ring
  have hbeta := hasDerivAt_suzukiBetaTail homega hx0 hx1
  have hleft := hxpow.ofReal_comp.mul hqpow.ofReal_comp
  have hright := (homegapow.ofReal_comp.const_mul (omega : ℂ)).mul hbeta
  have hfinal := (hleft.sub hright).const_mul
    (2 * (Real.pi : ℂ) ^ (omega : ℂ) / Complex.Gamma (omega : ℂ))
  change HasDerivAt (fun y => suzukiSourceGSmoothFormula omega y)
    (suzukiSourceGDerivative omega x) x
  simpa only [suzukiSourceGSmoothFormula, suzukiSourceGDerivative,
    suzukiBetaTailDerivative, Pi.mul_apply, Pi.sub_apply] using hfinal

/-- The unique singular power in `g_omega'` is interval-integrable up to the endpoint `1`.
This is the sharp analytic use of `omega > 1`: `omega - 2 > -1`. -/
theorem intervalIntegrable_suzukiSourceGCuspPower
    {omega delta : ℝ} (homega : 1 < omega)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) ^ (omega - 2)) volume delta 1 := by
  have hp : -1 < omega - 2 := by linarith
  have hbase0 : IntervalIntegrable (fun u : ℝ => u ^ (omega - 2))
      volume 0 (1 - delta) :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hbaseRaw := hbase0.comp_sub_left 1
  have hbase : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (omega - 2))
      volume delta 1 := by
    convert hbaseRaw.symm using 1 <;> ring
  have hcont : ContinuousOn (fun x : ℝ => (1 + x) ^ (omega - 2))
      (uIcc delta 1) := by
    apply (continuousOn_const.add continuousOn_id).rpow_const
    intro x hx
    rw [uIcc_of_le hdelta1.le] at hx
    left
    change 1 + x ≠ 0
    linarith [hx.1]
  have hprod := hbase.mul_continuousOn hcont
  apply hprod.congr
  intro x hx
  rw [uIoc_of_le hdelta1.le] at hx
  change (1 - x) ^ (omega - 2) * (1 + x) ^ (omega - 2) =
    (1 - x ^ 2) ^ (omega - 2)
  rw [← Real.mul_rpow (by linarith [hx.2] : 0 ≤ 1 - x)
    (by linarith [hx.1, hdelta0] : 0 ≤ 1 + x)]
  congr 2
  ring

/-- The complete exact derivative field `g_omega'` is interval-integrable up to its cusp at `1`.
This is the local `W^{1,1}` input missing from a pointwise dominated-differentiation argument. -/
theorem intervalIntegrable_suzukiSourceGDerivative
    {omega delta : ℝ} (homega : 1 < omega)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    IntervalIntegrable (suzukiSourceGDerivative omega) volume delta 1 := by
  have hdeltaLe : delta ≤ 1 := hdelta1.le
  have hpowReal (p : ℝ) : ContinuousOn (fun x : ℝ => x ^ p) (uIcc delta 1) := by
    apply continuousOn_id.rpow_const
    intro x hx
    left
    rw [uIcc_of_le hdeltaLe] at hx
    exact ne_of_gt (lt_of_lt_of_le hdelta0 hx.1)
  have hpowCast (p : ℝ) : ContinuousOn (fun x : ℝ => ((x ^ p : ℝ) : ℂ))
      (uIcc delta 1) := by
    exact (Complex.ofRealCLM.continuous.comp_continuousOn (hpowReal p)).congr
      (fun x _ => by simp [Function.comp_apply])
  have hqReal : ContinuousOn (fun x : ℝ => (1 - x ^ 2) ^ (omega - 1))
      (uIcc delta 1) := by
    apply (continuousOn_const.sub (continuousOn_id.pow 2)).rpow_const
    intro _ _
    exact Or.inr (by linarith)
  have hqCast : ContinuousOn
      (fun x : ℝ => (((1 - x ^ 2) ^ (omega - 1) : ℝ) : ℂ))
      (uIcc delta 1) := by
    exact (Complex.ofRealCLM.continuous.comp_continuousOn hqReal).congr
      (fun x _ => by simp [Function.comp_apply])
  have hbeta : ContinuousOn (suzukiBetaTail omega) (uIcc delta 1) := by
    simpa only [uIcc_of_le hdeltaLe] using
      continuousOn_suzukiBetaTail_Icc (omega := omega) (lt_trans zero_lt_one homega)
        hdelta0 hdelta1
  have hbetaD : ContinuousOn (suzukiBetaTailDerivative omega) (uIcc delta 1) := by
    have hreal := continuousOn_suzukiBetaTailDerivativeRealFormula homega hdelta0
    rw [uIcc_of_le hdeltaLe]
    exact hreal.congr fun x hx =>
      (suzukiBetaTailDerivative_eq_realFormula
        (by linarith [hdelta0, hx.1] : 0 ≤ x) hx.2)
  have hcuspReal := intervalIntegrable_suzukiSourceGCuspPower homega hdelta0 hdelta1
  have hqPrimeReal : IntervalIntegrable
      (fun x : ℝ => (-2 * x) * (omega - 1) * (1 - x ^ 2) ^ (omega - 2))
      volume delta 1 := by
    have hcoeff : ContinuousOn (fun x : ℝ => (-2 * x) * (omega - 1))
        (uIcc delta 1) := (continuousOn_const.mul continuousOn_id).mul continuousOn_const
    exact hcuspReal.continuousOn_mul hcoeff
  have hqPrimeCast : IntervalIntegrable
      (fun x : ℝ => (((-2 * x) * (omega - 1) *
        (1 - x ^ 2) ^ (omega - 2) : ℝ) : ℂ)) volume delta 1 := by
    have hsmul := hqPrimeReal.smul_continuousOn
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℂ)) (uIcc delta 1))
    simpa only [Complex.real_smul, mul_one] using hsmul
  have hpPrime : ContinuousOn
      (fun x : ℝ => ((((2 - omega) * x ^ (1 - omega) : ℝ) : ℂ)))
      (uIcc delta 1) := by
    exact (continuousOn_const.mul (hpowCast (1 - omega))).congr
      (fun x _ => by push_cast; rfl)
  have hp : ContinuousOn (fun x : ℝ => (((x ^ (2 - omega) : ℝ) : ℂ)))
      (uIcc delta 1) := hpowCast (2 - omega)
  have hrPrime : ContinuousOn
      (fun x : ℝ => ((((omega - 1) * x ^ (omega - 2) : ℝ) : ℂ)))
      (uIcc delta 1) := by
    exact (continuousOn_const.mul (hpowCast (omega - 2))).congr
      (fun x _ => by push_cast; rfl)
  have hr : ContinuousOn (fun x : ℝ => (((x ^ (omega - 1) : ℝ) : ℂ)))
      (uIcc delta 1) := hpowCast (omega - 1)
  have hleftOne : ContinuousOn (fun x =>
      (((2 - omega) * x ^ (1 - omega) : ℝ) : ℂ) *
        (((1 - x ^ 2) ^ (omega - 1) : ℝ) : ℂ)) (uIcc delta 1) :=
    hpPrime.mul hqCast
  have hleftTwo : IntervalIntegrable (fun x =>
      (((x ^ (2 - omega) : ℝ) : ℂ)) *
        (((-2 * x) * (omega - 1) *
          (1 - x ^ 2) ^ (omega - 2) : ℝ) : ℂ)) volume delta 1 :=
    hqPrimeCast.continuousOn_mul hp
  have hrightOne : ContinuousOn (fun x =>
      (((omega : ℂ) * (((omega - 1) * x ^ (omega - 2) : ℝ) : ℂ)) *
        suzukiBetaTail omega x)) (uIcc delta 1) :=
    (continuousOn_const.mul hrPrime).mul hbeta
  have hrightTwo : ContinuousOn
      (fun x => ((omega : ℂ) * (((x ^ (omega - 1) : ℝ) : ℂ))) *
        suzukiBetaTailDerivative omega x) (uIcc delta 1) :=
    (continuousOn_const.mul hr).mul hbetaD
  have hinside := (hleftOne.intervalIntegrable.add hleftTwo).sub
    (hrightOne.add hrightTwo).intervalIntegrable
  change IntervalIntegrable (fun x => suzukiSourceGDerivative omega x) volume delta 1
  simpa only [suzukiSourceGDerivative, Pi.add_apply] using hinside.const_mul
    (2 * (Real.pi : ℂ) ^ (omega : ℂ) / Complex.Gamma (omega : ℂ))

/-- On its open support, the smooth formula is definitionally faithful to Suzuki's printed
complex-power formula. -/
theorem suzukiSourceG_eq_smoothFormula
    {omega x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    suzukiSourceG omega x = suzukiSourceGSmoothFormula omega x := by
  rw [suzukiSourceG, if_pos ⟨hx0, hx1⟩, suzukiSourceGSmoothFormula]
  have hbase : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [← Complex.ofReal_cpow hx0.le (2 - omega),
    ← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
    ← Complex.ofReal_cpow hx0.le (omega - 1)]
  have hone : ((omega : ℂ) - ((1 : ℝ) : ℂ)) =
      ((omega - 1 : ℝ) : ℂ) := by rw [← Complex.ofReal_sub]
  rw [hone, ← Complex.ofReal_cpow hbase (omega - 1)]

/-- Exact derivative of Suzuki's literal, totalized `g_omega` at every interior support point. -/
theorem hasDerivAt_suzukiSourceG
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (suzukiSourceG omega) (suzukiSourceGDerivative omega x) x := by
  have hev : suzukiSourceG omega =ᶠ[𝓝 x] suzukiSourceGSmoothFormula omega := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with z hz
    exact suzukiSourceG_eq_smoothFormula hz.1 hz.2
  exact (hasDerivAt_suzukiSourceGSmoothFormula homega hx0 hx1).congr_of_eventuallyEq hev

/-- Total derivative field for the compactly supported literal kernel.  Its value at the two
support endpoints is immaterial; the strict support test makes both values zero. -/
def suzukiSourceGDerivativeTotal (omega x : ℝ) : ℂ :=
  if 0 < x ∧ x < 1 then suzukiSourceGDerivative omega x else 0

/-- Away from the single support cusp `x = 1`, the total derivative field is the exact derivative
of Suzuki's literal kernel at every positive point. -/
theorem hasDerivAt_suzukiSourceG_total
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt (suzukiSourceG omega) (suzukiSourceGDerivativeTotal omega x) x := by
  rcases lt_or_gt_of_ne hx1 with hxlt | hxgt
  · rw [suzukiSourceGDerivativeTotal, if_pos ⟨hx0, hxlt⟩]
    exact hasDerivAt_suzukiSourceG homega hx0 hxlt
  · rw [suzukiSourceGDerivativeTotal, if_neg (fun h => (not_lt_of_ge hxgt.le) h.2)]
    have hev : suzukiSourceG omega =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hxgt] with z hz
      rw [suzukiSourceG, if_neg]
      exact fun h => (not_lt_of_ge hz.le) h.2
    exact (hasDerivAt_const x 0).congr_of_eventuallyEq hev

/-- The total derivative is interval-integrable on every compact positive window that contains
the support cusp. -/
theorem intervalIntegrable_suzukiSourceGDerivativeTotal
    {omega delta B : ℝ} (homega : 1 < omega)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (hB : 1 ≤ B) :
    IntervalIntegrable (suzukiSourceGDerivativeTotal omega) volume delta B := by
  have hleftRaw := intervalIntegrable_suzukiSourceGDerivative homega hdelta0 hdelta1
  have hleft : IntervalIntegrable (suzukiSourceGDerivativeTotal omega) volume delta 1 := by
    apply hleftRaw.congr_uIoo
    intro x hx
    rw [uIoo_of_le hdelta1.le] at hx
    rw [suzukiSourceGDerivativeTotal, if_pos ⟨lt_of_lt_of_le hdelta0 hx.1.le, hx.2⟩]
  have hright : IntervalIntegrable (suzukiSourceGDerivativeTotal omega) volume 1 B := by
    apply IntervalIntegrable.zero.congr_uIoo
    intro x hx
    rw [uIoo_of_le hB] at hx
    rw [suzukiSourceGDerivativeTotal, if_neg (by
      rintro ⟨_, hlt⟩
      exact (not_lt_of_ge hx.1.le) hlt)]
    rfl
  exact hleft.trans hright

/-- Arbitrary compact-positive-window form of total derivative integrability. -/
theorem intervalIntegrable_suzukiSourceGDerivativeTotal_of_pos
    {omega u v : ℝ} (homega : 1 < omega) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (suzukiSourceGDerivativeTotal omega) volume u v := by
  let m : ℝ := min (min u v) 1
  let delta : ℝ := m / 2
  let B : ℝ := max (max u v) 1
  have hm0 : 0 < m := by
    dsimp [m]
    exact lt_min (lt_min hu hv) zero_lt_one
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta < 1 := by
    have hm1 : m ≤ 1 := by dsimp [m]; exact min_le_right _ _
    dsimp [delta]
    linarith
  have hB : 1 ≤ B := by dsimp [B]; exact le_max_right _ _
  have hall := intervalIntegrable_suzukiSourceGDerivativeTotal
    homega hdelta0 hdelta1 hB
  apply hall.mono_set
  intro x hx
  rw [uIcc] at hx
  rw [uIcc_of_le (hdelta1.le.trans hB)]
  have hdeltaMin : delta ≤ min u v := by
    have hmMin : m ≤ min u v := by dsimp [m]; exact min_le_left _ _
    have hdM : delta ≤ m := by dsimp [delta]; linarith
    exact hdM.trans hmMin
  have hmaxB : max u v ≤ B := by dsimp [B]; exact le_max_left _ _
  exact ⟨hdeltaMin.trans hx.1, hx.2.trans hmaxB⟩

/-- Fundamental-theorem identity across the integrable cusp endpoint.  The derivative is required
only on the open interval, while continuity supplies the totalized value `g_omega(1) = 0`. -/
theorem integral_suzukiSourceGDerivative_eq_sub
    {omega delta u v : ℝ} (homega : 1 < omega)
    (hdelta0 : 0 < delta) (hdeltaU : delta ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1) :
    (∫ x in u..v, suzukiSourceGDerivative omega x) =
      suzukiSourceG omega v - suzukiSourceG omega u := by
  have hu0 : 0 < u := lt_of_lt_of_le hdelta0 hdeltaU
  let d := u / 2
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hdU : d < u := by dsimp [d]; linarith
  have hd1 : d < 1 := lt_of_lt_of_le hdU (huv.trans hv1)
  have hintAll := intervalIntegrable_suzukiSourceGDerivative homega hd0 hd1
  have hint : IntervalIntegrable (suzukiSourceGDerivative omega) volume u v := by
    apply hintAll.mono_set
    intro x hx
    rw [uIcc_of_le huv] at hx
    rw [uIcc_of_le hd1.le]
    exact ⟨hdU.le.trans hx.1, hx.2.trans hv1⟩
  have hcont : ContinuousOn (suzukiSourceG omega) (Icc u v) := by
    intro x hx
    exact (continuousAt_suzukiSourceG homega
      (lt_of_lt_of_le hu0 hx.1)).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hcont
    (fun x hx => hasDerivAt_suzukiSourceG homega
      (lt_of_lt_of_le hu0 hx.1.le)
      (lt_of_lt_of_le hx.2 hv1)) hint

/-- The exact interior formula for `g_omega` is continuously differentiable. -/
theorem contDiffOn_one_suzukiSourceGSmoothFormula
    {omega : ℝ} (homega : 1 < omega) :
    ContDiffOn ℝ 1 (suzukiSourceGSmoothFormula omega) (Ioo 0 1) := by
  have hxpow : ContDiffOn ℝ 1 (fun x : ℝ => x ^ (2 - omega : ℝ)) (Ioo 0 1) :=
    contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx.1)
  have honeBase : ContDiffOn ℝ 1 (fun x : ℝ => 1 - x ^ 2) (Ioo 0 1) :=
    contDiffOn_const.sub (contDiffOn_id.pow 2)
  have honepow : ContDiffOn ℝ 1
      (fun x : ℝ => (1 - x ^ 2) ^ (omega - 1 : ℝ)) (Ioo 0 1) :=
    honeBase.rpow_const_of_ne (fun x hx => ne_of_gt (by nlinarith [hx.1, hx.2]))
  have homegapow : ContDiffOn ℝ 1
      (fun x : ℝ => x ^ (omega - 1 : ℝ)) (Ioo 0 1) :=
    contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx.1)
  have hcastX : ContDiffOn ℝ 1
      (fun x : ℝ => ((x ^ (2 - omega : ℝ) : ℝ) : ℂ)) (Ioo 0 1) := by
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hxpow).congr
      (fun x _ => by simp [Function.comp_apply])
  have hcastOne : ContDiffOn ℝ 1
      (fun x : ℝ => (((1 - x ^ 2) ^ (omega - 1 : ℝ) : ℝ) : ℂ)) (Ioo 0 1) := by
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn honepow).congr
      (fun x _ => by simp [Function.comp_apply])
  have hcastOmega : ContDiffOn ℝ 1
      (fun x : ℝ => ((x ^ (omega - 1 : ℝ) : ℝ) : ℂ)) (Ioo 0 1) := by
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn homegapow).congr
      (fun x _ => by simp [Function.comp_apply])
  exact contDiffOn_const.mul
    ((hcastX.mul hcastOne).sub
      ((contDiffOn_const.mul hcastOmega).mul
        (contDiffOn_one_suzukiBetaTail homega)))

/-- Suzuki's literal `g_omega` is continuously differentiable throughout `(0,1)`. -/
theorem contDiffOn_one_suzukiSourceG_Ioo
    {omega : ℝ} (homega : 1 < omega) :
    ContDiffOn ℝ 1 (suzukiSourceG omega) (Ioo 0 1) := by
  exact (contDiffOn_one_suzukiSourceGSmoothFormula homega).congr
    (fun x hx => suzukiSourceG_eq_smoothFormula hx.1 hx.2)

/-- Away from the support endpoint `1`, the literal `g_omega` is `C¹` at every positive point. -/
theorem contDiffAt_one_suzukiSourceG_of_pos_ne_one
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x) (hx1 : x ≠ 1) :
    ContDiffAt ℝ 1 (suzukiSourceG omega) x := by
  rcases lt_or_gt_of_ne hx1 with hxlt | hxgt
  · exact (contDiffOn_one_suzukiSourceG_Ioo homega x ⟨hx0, hxlt⟩).contDiffAt
      (Ioo_mem_nhds hx0 hxlt)
  · have hzero : ContDiffOn ℝ 1 (suzukiSourceG omega) (Ioi 1) := by
      exact contDiffOn_const.congr (fun z hz => by
        rw [suzukiSourceG, if_neg]
        exact fun h => (not_lt_of_ge hz.le) h.2)
    exact (hzero x hxgt).contDiffAt (Ioi_mem_nhds hxgt)

/-- Suzuki's literal floor-truncated arithmetic kernel is continuously differentiable at every
positive noninteger.  These are exactly the regular points asserted before Lemma `lem_ad1`. -/
theorem contDiffAt_one_suzukiSourceHFinite_of_not_nat
    {omega x : ℝ} (homega : 1 < omega) (hx0 : 0 < x)
    (hxNat : ∀ n : ℕ, x ≠ (n : ℝ)) :
    ContDiffAt ℝ 1 (suzukiSourceHFinite omega) x := by
  let B := x + 1
  let N := ⌊B⌋₊
  let fixed : ℝ → ℂ := fun z =>
    (1 / (z : ℂ)) * ∑ n ∈ Finset.Icc 1 N,
      ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceG omega (n / z)
  have hsum : ContDiffAt ℝ 1 (fun z : ℝ => ∑ n ∈ Finset.Icc 1 N,
      ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceG omega (n / z)) x := by
    apply ContDiffAt.sum
    intro n hn
    have hnOne : (1 : ℝ) ≤ n := by
      exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hratio0 : 0 < (n : ℝ) / x :=
      div_pos (lt_of_lt_of_le zero_lt_one hnOne) hx0
    have hratio1 : (n : ℝ) / x ≠ 1 := by
      intro h
      have hnx : (n : ℝ) = x := (div_eq_one_iff_eq hx0.ne').mp h
      exact hxNat n hnx.symm
    have hratioDiff : ContDiffAt ℝ 1 (fun z : ℝ => (n : ℝ) / z) x :=
      contDiffAt_const.div contDiffAt_id hx0.ne'
    exact contDiffAt_const.mul
      ((contDiffAt_one_suzukiSourceG_of_pos_ne_one homega hratio0 hratio1).comp
        x hratioDiff)
  have hcast : ContDiffAt ℝ 1 (fun z : ℝ => (z : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hrealInv : ContDiffAt ℝ 1 (fun z : ℝ => 1 / z) x :=
    contDiffAt_const.div contDiffAt_id hx0.ne'
  have hinv : ContDiffAt ℝ 1 (fun z : ℝ => 1 / (z : ℂ)) x :=
    by
      have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hrealInv
      exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
        simp only [Function.comp_apply, Complex.ofRealCLM_apply]
        rw [Complex.ofReal_div, Complex.ofReal_one])
  have hfixed : ContDiffAt ℝ 1 fixed x := hinv.mul hsum
  have hev : suzukiSourceHFinite omega =ᶠ[𝓝 x] fixed := by
    have hB : x < B := by dsimp [B]; linarith
    filter_upwards [Ioi_mem_nhds hx0, Iio_mem_nhds hB] with z hz0 hzB
    apply suzukiSourceHFinite_eq_fixedSum hz0
    dsimp only [N]
    exact Nat.floor_mono hzB.le
  exact hfixed.congr_of_eventuallyEq hev

/-- Regular `x`-locus in Suzuki's Lemma `lem_ad1`: positive points away from every breakpoint
`n/a`, including the `n=0` endpoint. -/
def SuzukiHankelRegularX (a : ℝ) : Set ℝ :=
  {x | 0 < x ∧ ∀ n : ℕ, x ≠ (n : ℝ) / a}

/-- The boundary term `x ↦ h_omega(ax)` is `C¹` at every point in Suzuki's exact regular locus. -/
theorem contDiffAt_one_suzukiHankelBoundaryGlobal
    {omega a x : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (hx : x ∈ SuzukiHankelRegularX a) :
    ContDiffAt ℝ 1 (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x := by
  have hax0 : 0 < a * x := mul_pos (by linarith) hx.1
  have haxNat : ∀ n : ℕ, a * x ≠ (n : ℝ) := by
    intro n hEq
    apply hx.2 n
    rw [eq_div_iff (by linarith : a ≠ 0)]
    simpa only [mul_comm] using hEq
  exact (contDiffAt_one_suzukiSourceHFinite_of_not_nat homega hax0 haxNat).comp
    x (contDiffAt_const.mul contDiffAt_id)

theorem contDiffOn_one_suzukiHankelBoundaryGlobal
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    ContDiffOn ℝ 1 (fun x : ℝ => suzukiSourceHFinite omega (a * x))
      (SuzukiHankelRegularX a) := by
  intro x hx
  exact (contDiffAt_one_suzukiHankelBoundaryGlobal homega ha hx).contDiffWithinAt

end RHTower
