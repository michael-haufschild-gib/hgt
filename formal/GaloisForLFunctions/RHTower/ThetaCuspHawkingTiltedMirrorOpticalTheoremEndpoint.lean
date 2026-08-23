import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzianOpticalTheoremEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace
import GaloisForLFunctions.RHTower.ThetaCuspTiltedSchwartz

/-!
# Modularly tilted theta-cusp Hawking optical theorem

For every real `a` with `|a| < 1`, the exponentially tilted source

`k_a(x) = exp(a*x) * thetaCuspFullSource(x)`

is real Schwartz data.  Hence `p_{a,lambda}(v) = v + lambda*k_a(v)` is a genuine timelike
moving-mirror family for an explicit open interval of couplings.  Its real-frequency Born
pair-production numerator is

`2*i*omega_out*omega_in*XiC(omega_out + omega_in + a*i)`.

Thus horizontal complex-frequency lines of centered Xi are not formal analytic probes: each is the
ordinary real-frequency spectrum of a real tilted mirror.  Exact pair-shell integration and
Plancherel then give the coefficient-correct optical theorem

`E_Hawking(a) = (1/(48*pi)) * integral |k_a''|^2`,

equal to the quadratic Davies--Fulling Schwarzian backreaction energy of that same mirror.

**[LOCAL-RESEARCH] [PAPER-PROVED] [LEAN-PROVED]** This realizes every point of the open Xi strip
as a real-frequency Hawking experiment and preserves the unsquared complex amplitude before the
energy calculation.

**[FALSIFIED]** Timelikeness plus this optical theorem cannot itself exclude tilted dark modes.
Generic positive Schwartz trajectories can have Fourier--Laplace zeros away from the real axis,
while obeying identical kinematics and energy balance.  Hawking emission is therefore backbone,
not a positivity slogan.

**[OPEN CORE]** Prove a theta-specific no-dark-mode law for the reflected physical mirror pair
`k_a, k_{-a}`.  Equivalently, show their de-embedded real-frequency pair carrier never vanishes for
`a != 0`.  Generic CCR, KMS, QEI, timelikeness, and optical-theorem identities do not imply it.
-/

open Complex Real MeasureTheory
open scoped FourierTransform SchwartzMap Interval

noncomputable section

namespace RHTower

/-! ## Real timelike mirror realizing a horizontal Xi line -/

/-- Tilted theta perturbation of the inertial null ray. -/
def thetaCuspHawkingTiltedTimelikeRay (a lambda v : ℝ) : ℝ :=
  v + lambda * thetaCuspTiltedSource a v

/-- Named null-ray derivative for the tilted family. -/
def thetaCuspHawkingTiltedTimelikeRayDerivative (a lambda v : ℝ) : ℝ :=
  1 + lambda * deriv (thetaCuspTiltedSource a) v

/-- Global first-derivative bound for tilt `a`. -/
def thetaCuspHawkingTiltedDerivativeBound (a : ℝ) : ℝ :=
  thetaCuspTiltedDerivativeConstant a 1

/-- Explicit coupling radius for a tilted physical mirror. -/
def thetaCuspHawkingTiltedCouplingRadius (a : ℝ) : ℝ :=
  (thetaCuspHawkingTiltedDerivativeBound a + 1)⁻¹

theorem thetaCuspHawkingTiltedDerivativeBound_nonneg (a : ℝ) :
    0 ≤ thetaCuspHawkingTiltedDerivativeBound a := by
  exact thetaCuspTiltedDerivativeConstant_nonneg a 1

theorem thetaCuspHawkingTiltedCouplingRadius_pos (a : ℝ) :
    0 < thetaCuspHawkingTiltedCouplingRadius a := by
  rw [thetaCuspHawkingTiltedCouplingRadius]
  exact inv_pos.mpr (by linarith [thetaCuspHawkingTiltedDerivativeBound_nonneg a])

theorem hasDerivAt_thetaCuspHawkingTiltedTimelikeRay
    (a lambda v : ℝ) :
    HasDerivAt (thetaCuspHawkingTiltedTimelikeRay a lambda)
      (thetaCuspHawkingTiltedTimelikeRayDerivative a lambda v) v := by
  unfold thetaCuspHawkingTiltedTimelikeRay thetaCuspHawkingTiltedTimelikeRayDerivative
  have hsource : HasDerivAt (thetaCuspTiltedSource a)
      (deriv (thetaCuspTiltedSource a) v) v :=
    ((contDiff_thetaCuspTiltedSource a).differentiable (by simp) v).hasDerivAt
  convert (hasDerivAt_id v).add (hsource.const_mul lambda) using 1 <;> rfl

theorem abs_thetaCuspTiltedSourceDeriv_le_bound
    {a : ℝ} (ha : |a| < 1) (v : ℝ) :
    |deriv (thetaCuspTiltedSource a) v| ≤
      thetaCuspHawkingTiltedDerivativeBound a := by
  have h := weighted_iteratedDeriv_thetaCuspTiltedSource_le ha 0 1 v
  simpa [iteratedDeriv_one, Real.norm_eq_abs,
    thetaCuspHawkingTiltedDerivativeBound] using h

theorem abs_mul_thetaCuspTiltedSourceDeriv_lt_one
    {a lambda : ℝ} (ha : |a| < 1)
    (hlambda : |lambda| < thetaCuspHawkingTiltedCouplingRadius a)
    (v : ℝ) :
    |lambda * deriv (thetaCuspTiltedSource a) v| < 1 := by
  let C := thetaCuspHawkingTiltedDerivativeBound a
  let r := thetaCuspHawkingTiltedCouplingRadius a
  have hC : 0 ≤ C := thetaCuspHawkingTiltedDerivativeBound_nonneg a
  have hr : 0 < r := thetaCuspHawkingTiltedCouplingRadius_pos a
  have hsource : |deriv (thetaCuspTiltedSource a) v| ≤ C :=
    abs_thetaCuspTiltedSourceDeriv_le_bound ha v
  have hden : 0 < C + 1 := by linarith
  have hrden : r * (C + 1) = 1 := by
    dsimp only [r, C]
    rw [thetaCuspHawkingTiltedCouplingRadius]
    exact inv_mul_cancel₀ hden.ne'
  rw [abs_mul]
  calc
    |lambda| * |deriv (thetaCuspTiltedSource a) v| ≤ |lambda| * C := by
      exact mul_le_mul_of_nonneg_left hsource (abs_nonneg lambda)
    _ ≤ r * C := mul_le_mul_of_nonneg_right hlambda.le hC
    _ < r * (C + 1) := mul_lt_mul_of_pos_left (by linarith) hr
    _ = 1 := hrden

theorem thetaCuspHawkingTiltedTimelikeRayDerivative_pos
    {a lambda : ℝ} (ha : |a| < 1)
    (hlambda : |lambda| < thetaCuspHawkingTiltedCouplingRadius a)
    (v : ℝ) :
    0 < thetaCuspHawkingTiltedTimelikeRayDerivative a lambda v := by
  have hsmall := abs_mul_thetaCuspTiltedSourceDeriv_lt_one ha hlambda v
  have hlower := (abs_lt.mp hsmall).1
  rw [thetaCuspHawkingTiltedTimelikeRayDerivative]
  linarith

/-- Every admissibly tilted source generates an open family of genuine timelike mirrors. -/
theorem strictMono_thetaCuspHawkingTiltedTimelikeRay
    {a lambda : ℝ} (ha : |a| < 1)
    (hlambda : |lambda| < thetaCuspHawkingTiltedCouplingRadius a) :
    StrictMono (thetaCuspHawkingTiltedTimelikeRay a lambda) := by
  apply strictMono_of_hasDerivAt_pos
    (hasDerivAt_thetaCuspHawkingTiltedTimelikeRay a lambda)
  exact thetaCuspHawkingTiltedTimelikeRayDerivative_pos ha hlambda

/-! ## Unsquared tilted Hawking amplitude -/

/-- First variation of the moving-mirror numerator for the real tilted trajectory. -/
def thetaCuspTiltedMovingMirrorBornRaw
    (a : ℝ) (ha : |a| < 1)
    (outgoingFrequency incomingFrequency : ℝ) : ℂ :=
  let totalFrequency := outgoingFrequency + incomingFrequency
  let fourierFrequency := totalFrequency / (2 * Real.pi)
  (outgoingFrequency : ℂ) *
      FourierTransform.fourier
        (SchwartzMap.derivCLM ℂ ℂ (thetaCuspTiltedSchwartz a ha) : ℝ → ℂ)
        fourierFrequency -
    Complex.I * (outgoingFrequency : ℂ) *
      ((outgoingFrequency - incomingFrequency : ℝ) : ℂ) *
      FourierTransform.fourier (thetaCuspTiltedSchwartz a ha : ℝ → ℂ)
        fourierFrequency

/-- Real-frequency tilted-mirror pair production reads centered Xi on a horizontal line. -/
theorem thetaCuspTiltedMovingMirrorBornRaw_eq_XiC
    {a : ℝ} (ha : |a| < 1)
    (outgoingFrequency incomingFrequency : ℝ) :
    thetaCuspTiltedMovingMirrorBornRaw a ha outgoingFrequency incomingFrequency =
      2 * Complex.I * (outgoingFrequency : ℂ) *
        (incomingFrequency : ℂ) *
        XiC ((outgoingFrequency + incomingFrequency : ℝ) + (a : ℂ) * I) := by
  let xiFrequency : ℝ :=
    (outgoingFrequency + incomingFrequency) / (2 * Real.pi)
  let source : 𝓢(ℝ, ℂ) := thetaCuspTiltedSchwartz a ha
  have hfourierDeriv := congrFun
    (Real.fourier_deriv
      (f := (source : ℝ → ℂ))
      source.integrable source.differentiable
      (SchwartzMap.derivCLM ℂ ℂ source).integrable) xiFrequency
  have hderivfun : deriv (source : ℝ → ℂ) =
      (SchwartzMap.derivCLM ℂ ℂ source : ℝ → ℂ) := by
    funext x
    rfl
  rw [hderivfun] at hfourierDeriv
  have hsource :
      FourierTransform.fourier (source : ℝ → ℂ) xiFrequency =
        XiC ((outgoingFrequency + incomingFrequency : ℝ) + (a : ℂ) * I) := by
    simpa only [source, SchwartzMap.fourier_coe, xiFrequency] using
      fourier_thetaCuspTiltedSchwartz_scaled ha
        (outgoingFrequency + incomingFrequency)
  rw [thetaCuspTiltedMovingMirrorBornRaw]
  change (outgoingFrequency : ℂ) *
      FourierTransform.fourier
        (SchwartzMap.derivCLM ℂ ℂ source : ℝ → ℂ) xiFrequency -
    Complex.I * (outgoingFrequency : ℂ) *
      ((outgoingFrequency - incomingFrequency : ℝ) : ℂ) *
      FourierTransform.fourier (source : ℝ → ℂ) xiFrequency = _
  rw [hfourierDeriv]
  simp only [smul_eq_mul]
  rw [hsource]
  dsimp [xiFrequency]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- Entire pair carrier for tilt `a`; physical frequencies are its real argument. -/
def thetaCuspHawkingTiltedBornPairKernel
    (a : ℝ) (outgoing incoming : ℂ) : ℂ :=
  2 * Complex.I * outgoing * incoming *
    XiC (outgoing + incoming + (a : ℂ) * I)

theorem thetaCuspHawkingTiltedBornPairKernel_real_eq_raw
    {a : ℝ} (ha : |a| < 1)
    (outgoing incoming : ℝ) :
    thetaCuspHawkingTiltedBornPairKernel a (outgoing : ℂ) (incoming : ℂ) =
      thetaCuspTiltedMovingMirrorBornRaw a ha outgoing incoming := by
  rw [thetaCuspTiltedMovingMirrorBornRaw_eq_XiC ha]
  rw [thetaCuspHawkingTiltedBornPairKernel]
  push_cast
  ring_nf

/-! ## Exact normalized Hawking shell -/

theorem thetaCuspHawkingTiltedBornPairKernel_normSq_totalSplit
    (a w u : ℝ) :
    Complex.normSq
        (thetaCuspHawkingTiltedBornPairKernel a
          (u : ℂ) ((w - u : ℝ) : ℂ)) =
      4 * u ^ 2 * (w - u) ^ 2 *
        Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) := by
  rw [thetaCuspHawkingTiltedBornPairKernel]
  push_cast
  rw [show (u : ℂ) + ((w : ℂ) - (u : ℂ)) + (a : ℂ) * I =
      (w : ℂ) + (a : ℂ) * I by ring]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  have htwo : Complex.normSq (2 : ℂ) = 4 := by
    norm_num [Complex.normSq_apply]
  have hI : Complex.normSq I = 1 := by
    norm_num [Complex.normSq_apply]
  have hsub : Complex.normSq ((w : ℂ) - (u : ℂ)) = (w - u) ^ 2 := by
    rw [← ofReal_sub, Complex.normSq_ofReal]
    ring
  rw [htwo, hI, hsub]
  ring

/-- Right-channel Hawking energy at fixed total real frequency for tilt `a`. -/
def thetaCuspHawkingTiltedBornRightEnergyShellDensity (a w : ℝ) : ℝ :=
  ∫ u in 0..w,
    Complex.normSq
        (thetaCuspHawkingTiltedBornPairKernel a
          (u : ℂ) ((w - u : ℝ) : ℂ)) /
      (16 * Real.pi ^ 2 * (w - u))

theorem thetaCuspHawkingTiltedBornRightEnergyShellIntegrand_eq
    (a w u : ℝ) :
    Complex.normSq
          (thetaCuspHawkingTiltedBornPairKernel a
            (u : ℂ) ((w - u : ℝ) : ℂ)) /
        (16 * Real.pi ^ 2 * (w - u)) =
      u ^ 2 * (w - u) *
        Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
          (4 * Real.pi ^ 2) := by
  rw [thetaCuspHawkingTiltedBornPairKernel_normSq_totalSplit]
  by_cases hv : w - u = 0
  · simp [hv]
  · field_simp [hv, Real.pi_ne_zero]
    ring

/-- Exact tilted Hawking shell energy, retaining the horizontal-line Xi modulus. -/
theorem thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq
    (a w : ℝ) :
    thetaCuspHawkingTiltedBornRightEnergyShellDensity a w =
      w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
        (48 * Real.pi ^ 2) := by
  have h2 := integral_pow (a := (0 : ℝ)) (b := w) (n := 2)
  have h3 := integral_pow (a := (0 : ℝ)) (b := w) (n := 3)
  rw [thetaCuspHawkingTiltedBornRightEnergyShellDensity]
  calc
    (∫ u in 0..w,
        Complex.normSq
            (thetaCuspHawkingTiltedBornPairKernel a
              (u : ℂ) ((w - u : ℝ) : ℂ)) /
          (16 * Real.pi ^ 2 * (w - u))) =
        ∫ u in 0..w,
          u ^ 2 * (w - u) *
            Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
              (4 * Real.pi ^ 2) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      exact thetaCuspHawkingTiltedBornRightEnergyShellIntegrand_eq a w u
    _ = _ := by
      rw [show (fun u : ℝ =>
          u ^ 2 * (w - u) *
            Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
              (4 * Real.pi ^ 2)) =
          fun u : ℝ =>
            (w * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
              (4 * Real.pi ^ 2)) * u ^ 2 +
            (-Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
              (4 * Real.pi ^ 2)) * u ^ 3 by
        funext u
        ring]
      rw [intervalIntegral.integral_add,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, h2, h3]
      · field_simp [Real.pi_ne_zero]
        ring
      · exact (by fun_prop : Continuous
          (fun u : ℝ =>
            (w * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
              (4 * Real.pi ^ 2)) * u ^ 2)).intervalIntegrable _ _
      · exact (by fun_prop : Continuous
          (fun u : ℝ =>
            (-Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
              (4 * Real.pi ^ 2)) * u ^ 3)).intervalIntegrable _ _

theorem thetaCuspHawkingTiltedBornRightEnergyShellDensity_nonneg
    (a w : ℝ) :
    0 ≤ thetaCuspHawkingTiltedBornRightEnergyShellDensity a w := by
  rw [thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq]
  have hw4 : 0 ≤ w ^ 4 := by positivity
  exact div_nonneg
    (mul_nonneg hw4
      (Complex.normSq_nonneg (XiC ((w : ℂ) + (a : ℂ) * I))))
    (by positivity)

theorem thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq_zero_iff
    {a w : ℝ} (hw : 0 < w) :
    thetaCuspHawkingTiltedBornRightEnergyShellDensity a w = 0 ↔
      XiC ((w : ℂ) + (a : ℂ) * I) = 0 := by
  rw [thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq]
  have hfactor : w ^ 4 / (48 * Real.pi ^ 2) ≠ 0 := by positivity
  rw [show w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
      (48 * Real.pi ^ 2) =
      (w ^ 4 / (48 * Real.pi ^ 2)) *
        Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) by ring,
    mul_eq_zero]
  simp [hfactor]

/-! ## Acceleration spectrum and tilted optical theorem -/

/-- Complex Schwartz carrier of the tilted mirror's second null-time derivative. -/
def thetaCuspHawkingTiltedSourceSecondDerivative
    (a : ℝ) (ha : |a| < 1) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.derivCLM ℂ ℂ
    (SchwartzMap.derivCLM ℂ ℂ (thetaCuspTiltedSchwartz a ha))

theorem fourier_thetaCuspHawkingTiltedSourceSecondDerivative_scaled
    {a : ℝ} (ha : |a| < 1) (w : ℝ) :
    FourierTransform.fourier
        (thetaCuspHawkingTiltedSourceSecondDerivative a ha : ℝ → ℂ)
        (w / (2 * Real.pi)) =
      -(w : ℂ) ^ 2 * XiC ((w : ℂ) + (a : ℂ) * I) := by
  let source : 𝓢(ℝ, ℂ) := thetaCuspTiltedSchwartz a ha
  let d1 : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ source
  have hderiv0 : deriv (source : ℝ → ℂ) = (d1 : ℝ → ℂ) := by
    funext x
    rfl
  have hderiv1 : deriv (d1 : ℝ → ℂ) =
      (thetaCuspHawkingTiltedSourceSecondDerivative a ha : ℝ → ℂ) := by
    funext x
    rfl
  have hfirst := congrFun
    (Real.fourier_deriv
      (f := (source : ℝ → ℂ)) source.integrable source.differentiable
      d1.integrable) (w / (2 * Real.pi))
  have hsecond := congrFun
    (Real.fourier_deriv
      (f := (d1 : ℝ → ℂ)) d1.integrable d1.differentiable
      (thetaCuspHawkingTiltedSourceSecondDerivative a ha).integrable)
      (w / (2 * Real.pi))
  rw [hderiv0] at hfirst
  rw [hderiv1] at hsecond
  have hsource :
      FourierTransform.fourier (source : ℝ → ℂ)
          (w / (2 * Real.pi)) =
        XiC ((w : ℂ) + (a : ℂ) * I) := by
    simpa only [source, SchwartzMap.fourier_coe] using
      fourier_thetaCuspTiltedSchwartz_scaled ha w
  rw [hsecond, hfirst, hsource]
  simp only [smul_eq_mul]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_sq_fourier_thetaCuspHawkingTiltedSourceSecondDerivative_scaled
    {a : ℝ} (ha : |a| < 1) (w : ℝ) :
    ‖FourierTransform.fourier
        (thetaCuspHawkingTiltedSourceSecondDerivative a ha : ℝ → ℂ)
        (w / (2 * Real.pi))‖ ^ 2 =
      w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) := by
  rw [fourier_thetaCuspHawkingTiltedSourceSecondDerivative_scaled ha]
  rw [← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_mul, Complex.normSq_neg]
  have hw : Complex.normSq ((w : ℂ) ^ 2) = w ^ 4 := by
    rw [← ofReal_pow, Complex.normSq_ofReal]
    ring
  rw [hw]

theorem integrable_pow_four_mul_normSq_XiC_tilt
    {a : ℝ} (ha : |a| < 1) :
    Integrable (fun w : ℝ =>
      w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I))) := by
  let H : ℝ → ℝ := fun xi =>
    ‖FourierTransform.fourier
      (thetaCuspHawkingTiltedSourceSecondDerivative a ha : ℝ → ℂ) xi‖ ^ 2
  have hH : Integrable H :=
    GaloisForLFunctions.RHTower.integrable_norm_sq_fourier
      (thetaCuspHawkingTiltedSourceSecondDerivative a ha).integrable
      (SchwartzMap.memLp (thetaCuspHawkingTiltedSourceSecondDerivative a ha) 2
        (volume : Measure ℝ))
  have hscaled : Integrable (fun w : ℝ => H (w / (2 * Real.pi))) :=
    hH.comp_div (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  apply hscaled.congr
  filter_upwards with w
  exact norm_sq_fourier_thetaCuspHawkingTiltedSourceSecondDerivative_scaled ha w

theorem integral_pow_four_mul_normSq_XiC_tilt
    {a : ℝ} (ha : |a| < 1) :
    (∫ w : ℝ,
      w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I))) =
      2 * Real.pi *
        ∫ x : ℝ,
          ‖(thetaCuspHawkingTiltedSourceSecondDerivative a ha : ℝ → ℂ) x‖ ^ 2 := by
  let H : ℝ → ℝ := fun xi =>
    ‖FourierTransform.fourier
      (thetaCuspHawkingTiltedSourceSecondDerivative a ha : ℝ → ℂ) xi‖ ^ 2
  have hpoint : (fun w : ℝ => H (w / (2 * Real.pi))) =
      fun w : ℝ =>
        w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) := by
    funext w
    exact norm_sq_fourier_thetaCuspHawkingTiltedSourceSecondDerivative_scaled ha w
  have hscale := MeasureTheory.Measure.integral_comp_div H (2 * Real.pi)
  rw [hpoint, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at hscale
  simp only [smul_eq_mul] at hscale
  rw [GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
    (thetaCuspHawkingTiltedSourceSecondDerivative a ha).integrable
    (SchwartzMap.memLp (thetaCuspHawkingTiltedSourceSecondDerivative a ha) 2
      (volume : Measure ℝ))] at hscale
  exact hscale

theorem normSq_XiC_neg_frequency_tilt (a w : ℝ) :
    Complex.normSq (XiC (((-w : ℝ) : ℂ) + (a : ℂ) * I)) =
      Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) := by
  have harg : (((-w : ℝ) : ℂ) + (a : ℂ) * I) =
      -((starRingEnd ℂ) ((w : ℂ) + (a : ℂ) * I)) := by
    apply Complex.ext <;> simp
  rw [harg, XiC_even, XiC_conj, Complex.normSq_conj]

private theorem integral_even_real_tilted
    (f : ℝ → ℝ) (heven : ∀ x, f (-x) = f x) (hint : Integrable f) :
    (∫ x : ℝ, f x) = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have h := deningerEven_integral (fun x : ℝ => (f x : ℂ))
    (fun x => by rw [heven]) hint.ofReal
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact Complex.ofReal_inj.mp (by simpa using h)

theorem integral_Ioi_pow_four_mul_normSq_XiC_tilt
    {a : ℝ} (ha : |a| < 1) :
    (∫ w : ℝ in Set.Ioi 0,
      w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I))) =
      Real.pi *
        ∫ x : ℝ,
          ‖(thetaCuspHawkingTiltedSourceSecondDerivative a ha : ℝ → ℂ) x‖ ^ 2 := by
  have heven : ∀ w : ℝ,
      (-w) ^ 4 * Complex.normSq
          (XiC (((-w : ℝ) : ℂ) + (a : ℂ) * I)) =
        w ^ 4 * Complex.normSq
          (XiC ((w : ℂ) + (a : ℂ) * I)) := by
    intro w
    rw [normSq_XiC_neg_frequency_tilt]
    ring
  have hsplit := integral_even_real_tilted
    (fun w : ℝ =>
      w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)))
    heven (integrable_pow_four_mul_normSq_XiC_tilt ha)
  rw [integral_pow_four_mul_normSq_XiC_tilt ha] at hsplit
  linarith [Real.pi_pos]

/-- Total right-channel Born energy for the real mirror with modular tilt `a`. -/
def thetaCuspHawkingTiltedBornRightQuadraticEnergy (a : ℝ) : ℝ :=
  ∫ w : ℝ in Set.Ioi 0,
    thetaCuspHawkingTiltedBornRightEnergyShellDensity a w

/-- Quadratic Davies--Fulling Schwarzian energy of the same tilted trajectory. -/
def thetaCuspHawkingTiltedSchwarzianQuadraticEnergy
    (a : ℝ) (ha : |a| < 1) : ℝ :=
  (1 / (48 * Real.pi)) *
    ∫ x : ℝ,
      ‖(thetaCuspHawkingTiltedSourceSecondDerivative a ha : ℝ → ℂ) x‖ ^ 2

/-- Exact tilted Hawking emission/backreaction optical theorem. -/
theorem thetaCuspHawkingTiltedBornSchwarzianOpticalTheorem
    {a : ℝ} (ha : |a| < 1) :
    thetaCuspHawkingTiltedBornRightQuadraticEnergy a =
      thetaCuspHawkingTiltedSchwarzianQuadraticEnergy a ha := by
  rw [thetaCuspHawkingTiltedBornRightQuadraticEnergy,
    thetaCuspHawkingTiltedSchwarzianQuadraticEnergy]
  calc
    (∫ w : ℝ in Set.Ioi 0,
        thetaCuspHawkingTiltedBornRightEnergyShellDensity a w) =
        ∫ w : ℝ in Set.Ioi 0,
          w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) /
            (48 * Real.pi ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _hw
      exact thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq a w
    _ = (1 / (48 * Real.pi ^ 2)) *
        ∫ w : ℝ in Set.Ioi 0,
          w ^ 4 * Complex.normSq (XiC ((w : ℂ) + (a : ℂ) * I)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _hw
      ring
    _ = _ := by
      rw [integral_Ioi_pow_four_mul_normSq_XiC_tilt ha]
      field_simp [Real.pi_ne_zero]

/-! ## Exact RH-strength open core -/

/-- De-embedded pair carrier measured at real frequency by the physical mirror of tilt `a`. -/
def thetaCuspHawkingTiltedDeembeddedPairCarrier (a w : ℝ) : ℂ :=
  XiC ((w : ℂ) + (a : ℂ) * I)

/-- No nonzero modular tilt has a real dark frequency. -/
def ThetaCuspHawkingTiltedMirrorsDarkFree : Prop :=
  ∀ (a w : ℝ), |a| < 1 → a ≠ 0 →
    thetaCuspHawkingTiltedDeembeddedPairCarrier a w ≠ 0

/-- RH is exactly the missing no-dark-mode law for the real tilted-mirror family. -/
theorem riemannHypothesis_iff_thetaCuspHawkingTiltedMirrorsDarkFree :
    RiemannHypothesis ↔ ThetaCuspHawkingTiltedMirrorsDarkFree := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro h a w _ha hane hzero
    have him := h ((w : ℂ) + (a : ℂ) * I) hzero
    exact hane (by simpa using him)
  · intro h z hz
    by_contra hzim
    obtain ⟨hlower, hupper⟩ := xiC_zero_im_mem_openHalf hz
    have ha : |z.im| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have harg : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
      apply Complex.ext <;> simp
    exact (h z.im z.re ha hzim) (by
      rw [thetaCuspHawkingTiltedDeembeddedPairCarrier, harg]
      exact hz)

end RHTower
