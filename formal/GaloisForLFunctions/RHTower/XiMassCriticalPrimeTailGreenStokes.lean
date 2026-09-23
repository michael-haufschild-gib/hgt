import GaloisForLFunctions.RHTower.XiMassCriticalWeilPairingCriterion
import GaloisForLFunctions.RHTower.PrimeTailReflectionFoldedSecondOrderResolvent

/-!
# Zero-rate prime-tail Green--Stokes realization of the Xi-mass Weil pairing

The fixed critical half-density Weil measure is the position moment of the canonical prime-tail
forcing.  This module realizes that position factor dynamically.  Each forcing atom is propagated
by the source-fixed zero-rate second-order Green kernel `-(L-t) 1_{t<L}`.  Two genuine improper
integrations by parts recover the atom at its source time.  Summing the resulting Green pairings
gives exactly the negative Xi-mass critical Weil pairing.

No homogeneous datum, divisor specialization, finite cutoff, RH premise, or numerical computation
enters the construction.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Frequency moments of the Xi-mass cross profile.  Moment `k+1` is the real-frequency
derivative of moment `k`. -/
def xiMassSpectralCrossMoment (a sigma u : ℝ) (k : ℕ) (h : ℝ) : ℂ :=
  ∫ x : ℝ,
    xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) x *
      (-(I * (x : ℂ))) ^ k * Complex.exp (-(I * (h : ℂ) * (x : ℂ)))

@[simp]
theorem xiMassSpectralCrossMoment_zero (a sigma u h : ℝ) :
    xiMassSpectralCrossMoment a sigma u 0 h =
      xiMassSpectralCrossProfile a sigma u h := by
  rw [xiMassSpectralCrossMoment, xiMassSpectralCrossProfile_eq_stripFourier, stripFourier]
  simp

/-- A Fourier moment still has exponential decay in the integration variable, after losing only
half of the original rate to its polynomial weight. -/
theorem norm_xiMassSpectralCrossMomentAmplitude_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) (k : ℕ) (x : ℝ) :
    ‖xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) x *
        (-(I * (x : ℂ))) ^ k‖ ≤
      (2 / sigma) ^ k * (k.factorial : ℝ) *
        Real.exp (-(sigma / 2 * |x|)) := by
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha
  have htest := norm_xiMassAnalyticTest_le
    (τ := ((sigma : ℂ) + (u : ℂ) * I)) ha (by simpa using hsigma.le) hmem
  have hmoment := pow_abs_mul_exp_neg_le hsigma k x
  rw [norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have htest' :
      ‖xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ)‖ ≤
        Real.exp (-(sigma * |x|)) := by simpa using htest
  calc
    ‖xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ)‖ * |x| ^ k ≤
        Real.exp (-(sigma * |x|)) * |x| ^ k :=
      mul_le_mul_of_nonneg_right htest' (by positivity)
    _ = |x| ^ k * Real.exp (-(sigma * |x|)) := by ring
    _ ≤ (2 / sigma) ^ k * (k.factorial : ℝ) *
        Real.exp (-(sigma / 2 * |x|)) := hmoment

/-- Differentiation of the complete mass profile never leaves the same moment tower. -/
theorem hasDerivAt_xiMassSpectralCrossMoment
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) (k : ℕ) (h : ℝ) :
    HasDerivAt (xiMassSpectralCrossMoment a sigma u k)
      (xiMassSpectralCrossMoment a sigma u (k + 1) h) h := by
  let g : ℝ → ℂ := fun x =>
    xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) x * (-(I * (x : ℂ))) ^ k
  let K : ℝ := (2 / sigma) ^ k * (k.factorial : ℝ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hgmeas : AEStronglyMeasurable g volume := by
    apply Continuous.aestronglyMeasurable
    dsimp only [g]
    apply Continuous.mul
    · rw [continuous_iff_continuousAt]
      intro x
      have hmem : (x : ℂ) ∈ xiMassStrip a := by
        change |((x : ℂ)).im| < a
        simpa using ha
      exact (hasDerivAt_xiMassAnalyticTest ha _ hmem).continuousAt.comp
        Complex.continuous_ofReal.continuousAt
    · fun_prop
  have hgbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(sigma / 2 * |x|)) := by
    intro x
    exact norm_xiMassSpectralCrossMomentAmplitude_le ha hsigma u k x
  have hstrip : |((h : ℝ) : ℂ).im| < sigma / 2 := by simp [hsigma]
  have hcomplex := hasDerivAt_expFourier hgmeas hK hgbound hstrip
  have hreal := hcomplex.scomp h Complex.ofRealCLM.hasDerivAt
  change HasDerivAt (fun r : ℝ => expFourier g (r : ℂ)) _ h at hreal
  have hreal' : HasDerivAt (fun r : ℝ => expFourier g (r : ℂ))
      (∫ x : ℝ, g x * (-(I * x)) * Complex.exp (-(I * (h : ℂ) * x))) h := by
    simpa using hreal
  have hfun : (fun r : ℝ => expFourier g (r : ℂ)) =
      xiMassSpectralCrossMoment a sigma u k := by
    funext r
    rfl
  rw [hfun] at hreal'
  refine hreal'.congr_deriv ?_
  rw [xiMassSpectralCrossMoment]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp only [g]
  rw [pow_succ]
  ring

/-- Position-weighted profile whose prime-tail forcing pairing is the critical Weil pairing. -/
def xiMassPrimeTailPositionProfile (a sigma u : ℝ) (h : ℝ) : ℂ :=
  (h : ℂ) * xiMassSpectralCrossMoment a sigma u 0 h

/-- Explicit first derivative of the position-weighted profile. -/
def xiMassPrimeTailPositionProfileDeriv (a sigma u : ℝ) (h : ℝ) : ℂ :=
  xiMassSpectralCrossMoment a sigma u 0 h +
    (h : ℂ) * xiMassSpectralCrossMoment a sigma u 1 h

/-- Explicit second derivative of the position-weighted profile. -/
def xiMassPrimeTailPositionProfileSecond (a sigma u : ℝ) (h : ℝ) : ℂ :=
  2 * xiMassSpectralCrossMoment a sigma u 1 h +
    (h : ℂ) * xiMassSpectralCrossMoment a sigma u 2 h

theorem hasDerivAt_xiMassPrimeTailPositionProfile
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u h : ℝ) :
    HasDerivAt (xiMassPrimeTailPositionProfile a sigma u)
      (xiMassPrimeTailPositionProfileDeriv a sigma u h) h := by
  have hid : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 h := Complex.ofRealCLM.hasDerivAt
  have hF := hasDerivAt_xiMassSpectralCrossMoment ha hsigma u 0 h
  change HasDerivAt
    ((fun r : ℝ => (r : ℂ)) * xiMassSpectralCrossMoment a sigma u 0)
    (xiMassSpectralCrossMoment a sigma u 0 h +
      (h : ℂ) * xiMassSpectralCrossMoment a sigma u 1 h) h
  exact (hid.mul hF).congr_deriv (by ring)

theorem hasDerivAt_xiMassPrimeTailPositionProfileDeriv
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u h : ℝ) :
    HasDerivAt (xiMassPrimeTailPositionProfileDeriv a sigma u)
      (xiMassPrimeTailPositionProfileSecond a sigma u h) h := by
  have hF0 := hasDerivAt_xiMassSpectralCrossMoment ha hsigma u 0 h
  have hid : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 h := Complex.ofRealCLM.hasDerivAt
  have hF1 := hasDerivAt_xiMassSpectralCrossMoment ha hsigma u 1 h
  have hprod := hid.mul hF1
  change HasDerivAt
    (xiMassSpectralCrossMoment a sigma u 0 +
      (fun r : ℝ => (r : ℂ)) * xiMassSpectralCrossMoment a sigma u 1)
    (2 * xiMassSpectralCrossMoment a sigma u 1 h +
      (h : ℂ) * xiMassSpectralCrossMoment a sigma u 2 h) h
  exact (hF0.add hprod).congr_deriv (by ring)

/-- Constant absorbing the shifted polynomial moment. -/
def xiMassShiftedMomentConstant (sigma d : ℝ) (k : ℕ) : ℝ :=
  Real.exp (sigma * d) * (2 / sigma) ^ k * (k.factorial : ℝ)

theorem shifted_moment_absorption
    {sigma d : ℝ} (hsigma : 0 < sigma) (hd : 0 ≤ d) (k : ℕ) (x : ℝ) :
    (|x| + d) ^ k * Real.exp (-(sigma * |x|)) ≤
      xiMassShiftedMomentConstant sigma d k *
        Real.exp (-(sigma / 2 * |x|)) := by
  have hy : 0 ≤ |x| + d := add_nonneg (abs_nonneg x) hd
  have hbase := pow_abs_mul_exp_neg_le hsigma k (|x| + d)
  rw [abs_of_nonneg hy] at hbase
  have hexp : Real.exp (-(sigma * |x|)) =
      Real.exp (sigma * d) * Real.exp (-(sigma * (|x| + d))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, xiMassShiftedMomentConstant]
  calc
    (|x| + d) ^ k *
        (Real.exp (sigma * d) * Real.exp (-(sigma * (|x| + d)))) =
      Real.exp (sigma * d) *
        ((|x| + d) ^ k * Real.exp (-(sigma * (|x| + d)))) := by ring
    _ ≤ Real.exp (sigma * d) *
        ((2 / sigma) ^ k * (k.factorial : ℝ) *
          Real.exp (-(sigma / 2 * (|x| + d)))) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
    _ ≤ Real.exp (sigma * d) *
        ((2 / sigma) ^ k * (k.factorial : ℝ) *
          Real.exp (-(sigma / 2 * |x|))) := by
      have he : Real.exp (-(sigma / 2 * (|x| + d))) ≤
          Real.exp (-(sigma / 2 * |x|)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (by positivity)) (Real.exp_nonneg _)
    _ = Real.exp (sigma * d) * (2 / sigma) ^ k * (k.factorial : ℝ) *
        Real.exp (-(sigma / 2 * |x|)) := by ring

/-- Every frequency moment inherits the same one-sided interior-strip decay. -/
theorem norm_xiMassSpectralCrossMoment_deepShift_le
    {a sigma d : ℝ} (hd : 0 ≤ d) (hda : d < a) (hsigma : 0 < sigma)
    (u : ℝ) (k : ℕ) {h : ℝ} (_hh : 0 ≤ h) :
    ‖xiMassSpectralCrossMoment a sigma u k h‖ ≤
      Real.exp (|u| * d - h * d) * xiMassShiftedMomentConstant sigma d k *
        ∫ x : ℝ, Real.exp (-(sigma / 2 * |x|)) := by
  let tau : ℂ := (sigma : ℂ) + (u : ℂ) * I
  let Q : ℂ → ℂ := fun z =>
    xiMassAnalyticTest a tau z * (-(I * z)) ^ k *
      Complex.exp (-(I * (h : ℂ) * z))
  let C : ℝ := Real.exp ((|u| + |h|) * d) * xiMassShiftedMomentConstant sigma d k
  have ha : 0 < a := lt_of_le_of_lt hd hda
  have hdiff : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ Q z := by
    intro z hz
    have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hda
    exact ((hasDerivAt_xiMassAnalyticTest ha tau hmem).differentiableAt.mul (by fun_prop)).mul
      (by fun_prop)
  have hrough : ∀ z : ℂ, |z.im| ≤ d →
      ‖Q z‖ ≤ C * Real.exp (-(sigma / 2 * |z.re|)) := by
    intro z hz
    have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hda
    have htest := norm_xiMassAnalyticTest_le (τ := tau) ha (by
      dsimp only [tau]
      simpa using hsigma.le) hmem
    have htest' : ‖xiMassAnalyticTest a tau z‖ ≤
        Real.exp (-(sigma * |z.re|) + |u| * |z.im|) := by
      simpa [tau] using htest
    have hzNorm : ‖z‖ ≤ |z.re| + d := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ |z.re| + d := add_le_add_right hz _
    have hpow : ‖(-(I * z)) ^ k‖ ≤ (|z.re| + d) ^ k := by
      rw [norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul]
      exact pow_le_pow_left₀ (norm_nonneg z) hzNorm k
    have hphase : (-(I * (h : ℂ) * z)).re = h * z.im := by
      simp [Complex.mul_re, Complex.mul_im]
    have himTest : |u| * |z.im| ≤ |u| * d :=
      mul_le_mul_of_nonneg_left hz (abs_nonneg u)
    have himPhase : h * z.im ≤ |h| * d := by
      calc
        h * z.im ≤ |h * z.im| := le_abs_self _
        _ = |h| * |z.im| := abs_mul _ _
        _ ≤ |h| * d := mul_le_mul_of_nonneg_left hz (abs_nonneg h)
    have habsorb := shifted_moment_absorption hsigma hd k z.re
    dsimp only [Q]
    rw [norm_mul, norm_mul, Complex.norm_exp, hphase]
    calc
      ‖xiMassAnalyticTest a tau z‖ * ‖(-(I * z)) ^ k‖ * Real.exp (h * z.im) ≤
          Real.exp (-(sigma * |z.re|) + |u| * |z.im|) *
            (|z.re| + d) ^ k * Real.exp (h * z.im) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul htest' hpow (norm_nonneg _) (Real.exp_nonneg _))
          (Real.exp_nonneg _)
      _ ≤ Real.exp ((|u| + |h|) * d) *
          ((|z.re| + d) ^ k * Real.exp (-(sigma * |z.re|))) := by
        have he : Real.exp (-(sigma * |z.re|) + |u| * |z.im|) *
              Real.exp (h * z.im) ≤
            Real.exp ((|u| + |h|) * d) * Real.exp (-(sigma * |z.re|)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith
        nlinarith [pow_nonneg (add_nonneg (abs_nonneg z.re) hd) k]
      _ ≤ C * Real.exp (-(sigma / 2 * |z.re|)) := by
        dsimp only [C]
        calc
          Real.exp ((|u| + |h|) * d) *
              ((|z.re| + d) ^ k * Real.exp (-(sigma * |z.re|))) ≤
            Real.exp ((|u| + |h|) * d) *
              (xiMassShiftedMomentConstant sigma d k *
                Real.exp (-(sigma / 2 * |z.re|))) :=
            mul_le_mul_of_nonneg_left habsorb (Real.exp_nonneg _)
          _ = Real.exp ((|u| + |h|) * d) *
              xiMassShiftedMomentConstant sigma d k *
                Real.exp (-(sigma / 2 * |z.re|)) := by ring
  have hshift := integral_horizontal_shift_neg_of_decay hd (half_pos hsigma) hdiff hrough
  have hright : (∫ x : ℝ, Q (x : ℂ)) = xiMassSpectralCrossMoment a sigma u k h := by rfl
  rw [hright] at hshift
  rw [← hshift]
  have hmajor : Integrable (fun x : ℝ =>
      (Real.exp (|u| * d - h * d) * xiMassShiftedMomentConstant sigma d k) *
        Real.exp (-(sigma / 2 * |x|))) :=
    (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (half_pos hsigma)).const_mul _
  calc
    ‖∫ x : ℝ, Q ((x : ℂ) - (d : ℂ) * I)‖ ≤
        ∫ x : ℝ,
          (Real.exp (|u| * d - h * d) * xiMassShiftedMomentConstant sigma d k) *
            Real.exp (-(sigma / 2 * |x|)) := by
      apply norm_integral_le_of_norm_le hmajor
      refine ae_of_all _ fun x => ?_
      have hzmem : ((x : ℂ) - (d : ℂ) * I) ∈ xiMassStrip a := by
        change |(((x : ℂ) - (d : ℂ) * I).im)| < a
        simpa [abs_of_nonneg hd] using hda
      have htest := norm_xiMassAnalyticTest_le
        (τ := tau) ha (by simpa [tau] using hsigma.le) hzmem
      have hzNorm : ‖(x : ℂ) - (d : ℂ) * I‖ ≤ |x| + d := by
        calc
          ‖(x : ℂ) - (d : ℂ) * I‖ ≤
              |(((x : ℂ) - (d : ℂ) * I).re)| +
                |(((x : ℂ) - (d : ℂ) * I).im)| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = |x| + d := by simp [abs_of_nonneg hd]
      have hpow : ‖(-(I * ((x : ℂ) - (d : ℂ) * I))) ^ k‖ ≤ (|x| + d) ^ k := by
        rw [norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul]
        exact pow_le_pow_left₀ (norm_nonneg _) hzNorm k
      have hphase :
          (-(I * (h : ℂ) * ((x : ℂ) - (d : ℂ) * I))).re = -h * d := by
        simp [Complex.mul_re, Complex.mul_im]
      have habsorb := shifted_moment_absorption hsigma hd k x
      dsimp only [Q]
      rw [norm_mul, norm_mul, Complex.norm_exp, hphase]
      have htest' :
          ‖xiMassAnalyticTest a tau ((x : ℂ) - (d : ℂ) * I)‖ ≤
            Real.exp (-(sigma * |x|) + |u| * d) := by simpa [tau, abs_of_nonneg hd] using htest
      calc
        ‖xiMassAnalyticTest a tau ((x : ℂ) - (d : ℂ) * I)‖ *
              ‖(-(I * ((x : ℂ) - (d : ℂ) * I))) ^ k‖ * Real.exp (-h * d) ≤
            Real.exp (-(sigma * |x|) + |u| * d) *
              (|x| + d) ^ k * Real.exp (-h * d) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul htest' hpow (norm_nonneg _) (by positivity))
            (Real.exp_nonneg _)
        _ = Real.exp (|u| * d - h * d) *
            ((|x| + d) ^ k * Real.exp (-(sigma * |x|))) := by
          calc
            Real.exp (-(sigma * |x|) + |u| * d) * (|x| + d) ^ k *
                Real.exp (-h * d) =
              ((|x| + d) ^ k * Real.exp (-(sigma * |x|))) *
                (Real.exp (|u| * d) * Real.exp (-h * d)) := by
              rw [Real.exp_add]
              ring
            _ = ((|x| + d) ^ k * Real.exp (-(sigma * |x|))) *
                Real.exp (|u| * d - h * d) := by
              rw [← Real.exp_add]
              congr 2
              ring
            _ = Real.exp (|u| * d - h * d) *
                ((|x| + d) ^ k * Real.exp (-(sigma * |x|))) := by ring
        _ ≤ (Real.exp (|u| * d - h * d) *
              xiMassShiftedMomentConstant sigma d k) *
                Real.exp (-(sigma / 2 * |x|)) := by
          calc
            Real.exp (|u| * d - h * d) *
                ((|x| + d) ^ k * Real.exp (-(sigma * |x|))) ≤
              Real.exp (|u| * d - h * d) *
                (xiMassShiftedMomentConstant sigma d k *
                  Real.exp (-(sigma / 2 * |x|))) :=
              mul_le_mul_of_nonneg_left habsorb (Real.exp_nonneg _)
            _ = (Real.exp (|u| * d - h * d) *
                  xiMassShiftedMomentConstant sigma d k) *
                    Real.exp (-(sigma / 2 * |x|)) := by ring
    _ = Real.exp (|u| * d - h * d) * xiMassShiftedMomentConstant sigma d k *
        ∫ x : ℝ, Real.exp (-(sigma / 2 * |x|)) := by
      rw [MeasureTheory.integral_const_mul]

/-- Polynomial times a strictly decaying exponential is integrable on positive time. -/
theorem integrableOn_pow_mul_exp_neg_real_green (m : ℕ) {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun h : ℝ => h ^ m * Real.exp (-d * h)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (m : ℝ)) (p := (1 : ℝ)) (b := d)
    (by have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
    (by norm_num) hd
  apply h.congr_fun
  · intro x hx
    have hx0 : 0 < x := mem_Ioi.mp hx
    change x ^ (m : ℝ) * Real.exp (-d * x ^ (1 : ℝ)) =
      x ^ m * Real.exp (-d * x)
    rw [Real.rpow_natCast, Real.rpow_one]
  · exact measurableSet_Ioi

/-- Every polynomially weighted profile moment is integrable after any positive source time. -/
theorem integrableOn_pow_mul_xiMassSpectralCrossMoment
    {a sigma d : ℝ} (hd : 0 < d) (hda : d < a) (hsigma : 0 < sigma)
    (u : ℝ) (k m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun h : ℝ => (h : ℂ) ^ m * xiMassSpectralCrossMoment a sigma u k h)
      (Ioi t) := by
  let C : ℝ := Real.exp (|u| * d) * xiMassShiftedMomentConstant sigma d k *
    ∫ x : ℝ, Real.exp (-(sigma / 2 * |x|))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _)
      (by unfold xiMassShiftedMomentConstant; positivity))
      (integral_nonneg fun _ => Real.exp_nonneg _)
  have hbase : IntegrableOn (fun h : ℝ => C * (h ^ m * Real.exp (-d * h))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_real_green m hd).const_mul C
  have hbaseT := hbase.mono_set (fun x hx => lt_of_le_of_lt ht hx)
  have hmomentCont : Continuous (xiMassSpectralCrossMoment a sigma u k) := by
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassSpectralCrossMoment (lt_trans hd hda) hsigma u k h).continuousAt
  refine Integrable.mono' hbaseT ?_ ?_
  · have hc : Continuous (fun h : ℝ =>
        (h : ℂ) ^ m * xiMassSpectralCrossMoment a sigma u k h) :=
      (by fun_prop : Continuous fun h : ℝ => (h : ℂ) ^ m).mul hmomentCont
    exact hc.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : 0 ≤ h := le_trans ht (le_of_lt hh)
    have hmoment := norm_xiMassSpectralCrossMoment_deepShift_le
      hd.le hda hsigma u k hh0
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh0]
    have hpow0 : 0 ≤ h ^ m := by positivity
    calc
      h ^ m * ‖xiMassSpectralCrossMoment a sigma u k h‖ ≤
          h ^ m * (Real.exp (|u| * d - h * d) *
            xiMassShiftedMomentConstant sigma d k *
              ∫ x : ℝ, Real.exp (-(sigma / 2 * |x|))) :=
        mul_le_mul_of_nonneg_left hmoment hpow0
      _ = C * (h ^ m * Real.exp (-d * h)) := by
        dsimp only [C]
        rw [show Real.exp (|u| * d - h * d) =
          Real.exp (|u| * d) * Real.exp (-d * h) by
            rw [← Real.exp_add]; congr 1; ring]
        ring

/-- Every polynomially weighted profile moment vanishes at positive infinity. -/
theorem tendsto_pow_mul_xiMassSpectralCrossMoment_zero
    {a sigma d : ℝ} (hd : 0 < d) (hda : d < a) (hsigma : 0 < sigma)
    (u : ℝ) (k m : ℕ) :
    Tendsto (fun h : ℝ => (h : ℂ) ^ m * xiMassSpectralCrossMoment a sigma u k h)
      atTop (𝓝 0) := by
  let C : ℝ := Real.exp (|u| * d) * xiMassShiftedMomentConstant sigma d k *
    ∫ x : ℝ, Real.exp (-(sigma / 2 * |x|))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _)
      (by unfold xiMassShiftedMomentConstant; positivity))
      (integral_nonneg fun _ => Real.exp_nonneg _)
  have hraw := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) d hd
  have hnat : Tendsto (fun h : ℝ => h ^ m * Real.exp (-d * h)) atTop (𝓝 0) := by
    refine hraw.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with h hh
    rw [Real.rpow_natCast]
  have hupper : Tendsto (fun h : ℝ => C * (h ^ m * Real.exp (-d * h))) atTop (𝓝 0) := by
    simpa using hnat.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' ?_ ?_ hupper
  · exact Eventually.of_forall fun h => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
    have hmoment := norm_xiMassSpectralCrossMoment_deepShift_le
      hd.le hda hsigma u k hh
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
    calc
      h ^ m * ‖xiMassSpectralCrossMoment a sigma u k h‖ ≤
          h ^ m * (Real.exp (|u| * d - h * d) *
            xiMassShiftedMomentConstant sigma d k *
              ∫ x : ℝ, Real.exp (-(sigma / 2 * |x|))) :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = C * (h ^ m * Real.exp (-d * h)) := by
        dsimp only [C]
        rw [show Real.exp (|u| * d - h * d) =
          Real.exp (|u| * d) * Real.exp (-d * h) by
            rw [← Real.exp_add]; congr 1; ring]
        ring

/-- The position profile itself vanishes at the cofinal end. -/
theorem tendsto_xiMassPrimeTailPositionProfile_zero
    {a sigma d : ℝ} (hd : 0 < d) (hda : d < a) (hsigma : 0 < sigma) (u : ℝ) :
    Tendsto (xiMassPrimeTailPositionProfile a sigma u) atTop (𝓝 0) := by
  change Tendsto (fun h : ℝ => (h : ℂ) *
    xiMassSpectralCrossMoment a sigma u 0 h) atTop (𝓝 0)
  simpa only [pow_one] using
    tendsto_pow_mul_xiMassSpectralCrossMoment_zero hd hda hsigma u 0 1

/-- The boundary term `(h-t) g'(h)` also vanishes; this is the noncompact Green--Stokes gate. -/
theorem tendsto_sub_mul_xiMassPrimeTailPositionProfileDeriv_zero
    {a sigma d : ℝ} (hd : 0 < d) (hda : d < a) (hsigma : 0 < sigma)
    (u t : ℝ) :
    Tendsto (fun h : ℝ => ((h - t : ℝ) : ℂ) *
      xiMassPrimeTailPositionProfileDeriv a sigma u h) atTop (𝓝 0) := by
  have h00 := tendsto_pow_mul_xiMassSpectralCrossMoment_zero hd hda hsigma u 0 0
  have h01 := tendsto_pow_mul_xiMassSpectralCrossMoment_zero hd hda hsigma u 0 1
  have h11 := tendsto_pow_mul_xiMassSpectralCrossMoment_zero hd hda hsigma u 1 1
  have h12 := tendsto_pow_mul_xiMassSpectralCrossMoment_zero hd hda hsigma u 1 2
  have hsum := h01.sub (h00.const_mul (t : ℂ)) |>.add
    (h12.sub (h11.const_mul (t : ℂ)))
  have hsum' : Tendsto
      (fun h : ℝ =>
        (h : ℂ) * xiMassSpectralCrossMoment a sigma u 0 h -
          (t : ℂ) * xiMassSpectralCrossMoment a sigma u 0 h +
        ((h : ℂ) ^ 2 * xiMassSpectralCrossMoment a sigma u 1 h -
          (t : ℂ) * ((h : ℂ) * xiMassSpectralCrossMoment a sigma u 1 h)))
      atTop (𝓝 0) := by
    simpa only [pow_zero, pow_one, one_mul, sub_zero, mul_zero, add_zero] using hsum
  refine hsum'.congr' ?_
  filter_upwards with h
  simp only [xiMassPrimeTailPositionProfileDeriv]
  push_cast
  ring

/-- Source-fixed zero-rate second-order Green atom for one prime-tail forcing atom. -/
def criticalPrimeTailZeroGreenAtom (n : DeningerPrimePowerIndex) (L : ℝ) : ℂ :=
  if deningerPrimePowerTime n < L then
    -((criticalPrimeTailAtomWeight n : ℂ) *
      ((L - deningerPrimePowerTime n : ℝ) : ℂ))
  else 0

theorem criticalPrimeTailZeroGreenAtom_eq_indicator (n : DeningerPrimePowerIndex) :
    criticalPrimeTailZeroGreenAtom n =
      Set.indicator (Ioi (deningerPrimePowerTime n))
        (fun L : ℝ => -((criticalPrimeTailAtomWeight n : ℂ) *
          ((L - deningerPrimePowerTime n : ℝ) : ℂ))) := by
  funext L
  by_cases hL : deningerPrimePowerTime n < L <;>
    simp [criticalPrimeTailZeroGreenAtom, Set.indicator, hL]

/-- The position-profile derivative is integrable beyond every prime source time. -/
theorem integrableOn_xiMassPrimeTailPositionProfileDeriv
    {a sigma d : ℝ} (hd : 0 < d) (hda : d < a) (hsigma : 0 < sigma)
    (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (xiMassPrimeTailPositionProfileDeriv a sigma u) (Ioi t) := by
  have h0 := integrableOn_pow_mul_xiMassSpectralCrossMoment hd hda hsigma u 0 0 ht
  have h1 := integrableOn_pow_mul_xiMassSpectralCrossMoment hd hda hsigma u 1 1 ht
  change IntegrableOn (fun h : ℝ =>
    xiMassSpectralCrossMoment a sigma u 0 h +
      (h : ℂ) * xiMassSpectralCrossMoment a sigma u 1 h) (Ioi t)
  refine (h0.add h1).congr ?_
  filter_upwards with h
  simp only [Pi.add_apply, pow_zero, pow_one, one_mul]

/-- The linear Green weight times the profile's second derivative is integrable. -/
theorem integrableOn_sub_mul_xiMassPrimeTailPositionProfileSecond
    {a sigma d : ℝ} (hd : 0 < d) (hda : d < a) (hsigma : 0 < sigma)
    (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun h : ℝ => ((h - t : ℝ) : ℂ) *
      xiMassPrimeTailPositionProfileSecond a sigma u h) (Ioi t) := by
  have h10 := integrableOn_pow_mul_xiMassSpectralCrossMoment hd hda hsigma u 1 1 ht
  have h00 := integrableOn_pow_mul_xiMassSpectralCrossMoment hd hda hsigma u 1 0 ht
  have h21 := integrableOn_pow_mul_xiMassSpectralCrossMoment hd hda hsigma u 2 1 ht
  have h11 := integrableOn_pow_mul_xiMassSpectralCrossMoment hd hda hsigma u 2 2 ht
  have hcomb := (h10.const_mul 2).sub ((h00.const_mul 2).const_mul (t : ℂ)) |>.add
    (h11.sub (h21.const_mul (t : ℂ)))
  change IntegrableOn (fun h : ℝ => ((h - t : ℝ) : ℂ) *
    (2 * xiMassSpectralCrossMoment a sigma u 1 h +
      (h : ℂ) * xiMassSpectralCrossMoment a sigma u 2 h)) (Ioi t)
  refine hcomb.congr ?_
  filter_upwards with h
  simp only [Pi.add_apply, Pi.sub_apply,
    pow_zero, one_mul, pow_one]
  push_cast
  ring

/-- **C39 atom Green--Stokes law.**  The actual improper Green pairing recovers exactly the
negative position-weighted forcing atom. -/
theorem integral_xiMassPositionSecond_mul_zeroGreenAtom
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ)
    (n : DeningerPrimePowerIndex) :
    (∫ L : ℝ, xiMassPrimeTailPositionProfileSecond a sigma u L *
        criticalPrimeTailZeroGreenAtom n L) =
      -((criticalPrimeTailAtomWeight n : ℂ) *
        xiMassPrimeTailPositionProfile a sigma u (deningerPrimePowerTime n)) := by
  let d : ℝ := a / 2
  let t : ℝ := deningerPrimePowerTime n
  have hd : 0 < d := by dsimp only [d]; linarith
  have hda : d < a := by dsimp only [d]; linarith
  have ht : 0 ≤ t := (deningerPrimePowerTime_pos n).le
  have hfirst :
      (∫ L : ℝ in Ioi t, xiMassPrimeTailPositionProfileDeriv a sigma u L) =
        -xiMassPrimeTailPositionProfile a sigma u t := by
    simpa using (MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := t) (f := xiMassPrimeTailPositionProfile a sigma u)
      (f' := xiMassPrimeTailPositionProfileDeriv a sigma u)
      (fun L _ => hasDerivAt_xiMassPrimeTailPositionProfile ha hsigma u L)
      (integrableOn_xiMassPrimeTailPositionProfileDeriv hd hda hsigma u ht)
      (tendsto_xiMassPrimeTailPositionProfile_zero hd hda hsigma u))
  have hparts := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := t) (a' := (0 : ℂ)) (b' := (0 : ℂ))
    (u := fun L : ℝ => ((L - t : ℝ) : ℂ))
    (v := xiMassPrimeTailPositionProfileDeriv a sigma u)
    (u' := fun _ : ℝ => (1 : ℂ))
    (v' := xiMassPrimeTailPositionProfileSecond a sigma u)
    (fun L _ => by simpa using ((hasDerivAt_id L).sub_const t).ofReal_comp)
    (fun L _ => hasDerivAt_xiMassPrimeTailPositionProfileDeriv ha hsigma u L)
    (integrableOn_sub_mul_xiMassPrimeTailPositionProfileSecond hd hda hsigma u ht)
    (by
      refine (integrableOn_xiMassPrimeTailPositionProfileDeriv hd hda hsigma u ht).congr ?_
      filter_upwards with L
      simp only [Pi.mul_apply, one_mul])
    (by
      have hcont : ContinuousAt (fun L : ℝ => ((L - t : ℝ) : ℂ) *
          xiMassPrimeTailPositionProfileDeriv a sigma u L) t :=
        (((continuousAt_id.sub continuousAt_const).ofReal).mul
          (hasDerivAt_xiMassPrimeTailPositionProfileDeriv ha hsigma u t).continuousAt)
      have htend : Tendsto (fun L : ℝ => ((L - t : ℝ) : ℂ) *
          xiMassPrimeTailPositionProfileDeriv a sigma u L)
          (𝓝[>] t) (𝓝 (((t - t : ℝ) : ℂ) *
            xiMassPrimeTailPositionProfileDeriv a sigma u t)) :=
        hcont.continuousWithinAt
      rw [show ((fun L : ℝ => ((L - t : ℝ) : ℂ)) *
          xiMassPrimeTailPositionProfileDeriv a sigma u) =
        fun L : ℝ => ((L - t : ℝ) : ℂ) *
          xiMassPrimeTailPositionProfileDeriv a sigma u L by
            funext L
            rfl]
      simpa only [sub_self, ofReal_zero, zero_mul] using htend)
    (tendsto_sub_mul_xiMassPrimeTailPositionProfileDeriv_zero hd hda hsigma u t)
  have hgreen :
      (∫ L : ℝ in Ioi t, ((L - t : ℝ) : ℂ) *
        xiMassPrimeTailPositionProfileSecond a sigma u L) =
        xiMassPrimeTailPositionProfile a sigma u t := by
    simp only [one_mul] at hparts
    rw [hparts, hfirst]
    ring
  rw [criticalPrimeTailZeroGreenAtom_eq_indicator,
    show (fun L : ℝ => xiMassPrimeTailPositionProfileSecond a sigma u L *
      Set.indicator (Ioi t)
        (fun L : ℝ => -((criticalPrimeTailAtomWeight n : ℂ) * ((L - t : ℝ) : ℂ))) L) =
      Set.indicator (Ioi t)
        (fun L : ℝ => -(criticalPrimeTailAtomWeight n : ℂ) *
          (((L - t : ℝ) : ℂ) * xiMassPrimeTailPositionProfileSecond a sigma u L)) by
      funext L
      by_cases hL : L ∈ Ioi t <;> simp [Set.indicator, hL] <;> ring,
    integral_indicator measurableSet_Ioi, integral_const_mul, hgreen]
  simp only [t]
  ring

/-- One genuine improper Green--Stokes pairing at a prime-tail atom. -/
def xiMassCriticalPrimeTailGreenAtomPairing
    (a sigma u : ℝ) (n : DeningerPrimePowerIndex) : ℂ :=
  ∫ L : ℝ, xiMassPrimeTailPositionProfileSecond a sigma u L *
    criticalPrimeTailZeroGreenAtom n L

theorem xiMassCriticalPrimeTailGreenAtomPairing_eq_neg_crossAtom
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ)
    (n : DeningerPrimePowerIndex) :
    xiMassCriticalPrimeTailGreenAtomPairing a sigma u n =
      -xiMassCriticalHalfDensityCrossAtom a sigma u n := by
  rw [xiMassCriticalPrimeTailGreenAtomPairing,
    integral_xiMassPositionSecond_mul_zeroGreenAtom ha hsigma]
  rw [xiMassPrimeTailPositionProfile, xiMassSpectralCrossMoment_zero,
    xiMassCriticalHalfDensityCrossAtom]
  have hw : (criticalPrimeTailAtomWeight n : ℂ) *
      (deningerPrimePowerTime n : ℂ) =
        (criticalMellinAtomWeight (n : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, mul_comm,
      deningerPrimePowerTime_mul_criticalPrimeTailAtomWeight]
  calc
    -((criticalPrimeTailAtomWeight n : ℂ) *
        ((deningerPrimePowerTime n : ℂ) *
          xiMassSpectralCrossProfile a sigma u (deningerPrimePowerTime n))) =
      -(((criticalPrimeTailAtomWeight n : ℂ) * (deningerPrimePowerTime n : ℂ)) *
        xiMassSpectralCrossProfile a sigma u (deningerPrimePowerTime n)) := by ring
    _ = -((criticalMellinAtomWeight (n : ℕ) : ℂ) *
        xiMassSpectralCrossProfile a sigma u (deningerPrimePowerTime n)) := by rw [hw]

/-- Complete source-fixed zero-rate Green--Stokes current. -/
def xiMassCriticalPrimeTailGreenCurrent (a sigma u : ℝ) : ℂ :=
  ∑' n : DeningerPrimePowerIndex,
    xiMassCriticalPrimeTailGreenAtomPairing a sigma u n

/-- The Green current is exactly the negative complete half-density mass cross series. -/
theorem xiMassCriticalPrimeTailGreenCurrent_eq_neg_crossSeries
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    xiMassCriticalPrimeTailGreenCurrent a sigma u =
      -xiMassCriticalHalfDensityCrossSeries a sigma u := by
  rw [xiMassCriticalPrimeTailGreenCurrent, xiMassCriticalHalfDensityCrossSeries, ← tsum_neg]
  apply tsum_congr
  intro n
  exact xiMassCriticalPrimeTailGreenAtomPairing_eq_neg_crossAtom (lt_trans (by norm_num) ha)
    hsigma u n

/-- **C39 capstone.**  Fixed Weil pairing equals negative source-fixed prime-tail Green current.
This is the exact pre-divisor second-order dynamical realization of the C38 RH criterion. -/
theorem xiMassCriticalHalfDensityWeilPairing_eq_neg_primeTailGreenCurrent
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    xiMassCriticalHalfDensityWeilPairing a sigma u =
      -xiMassCriticalPrimeTailGreenCurrent a sigma u := by
  rw [xiMassCriticalHalfDensityWeilPairing_eq_crossSeries ha hsigma,
    xiMassCriticalPrimeTailGreenCurrent_eq_neg_crossSeries ha hsigma]
  simp

/-- RH is exactly uniform boundedness of the source-fixed zero-rate Green--Stokes current. -/
theorem riemannHypothesis_iff_xiMassCriticalPrimeTailGreenCurrentLineBound
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖xiMassCriticalPrimeTailGreenCurrent a sigma u‖ ≤ C := by
  let c : ℝ := (a + 1 / 2) / 2
  have hcHalf : 1 / 2 < c := by dsimp only [c]; linarith
  have hca : c < a := by dsimp only [c]; linarith
  rw [riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairingLineBound
    hcHalf hca hsigma hcHalf hca]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun u hu => ?_⟩
    rw [← norm_neg, ← xiMassCriticalHalfDensityWeilPairing_eq_neg_primeTailGreenCurrent
      ha hsigma u]
    exact hC u hu
  · rintro ⟨C, hC⟩
    refine ⟨C, fun u hu => ?_⟩
    rw [xiMassCriticalHalfDensityWeilPairing_eq_neg_primeTailGreenCurrent ha hsigma u,
      norm_neg]
    exact hC u hu

end

end RHTower
