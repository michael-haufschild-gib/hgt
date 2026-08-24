import GaloisForLFunctions.RHTower.ThetaCuspHawkingBackreactionCubicCompletionEndpoint
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.DeningerDivisorThreePointDetection
import GaloisForLFunctions.HTGeometry.KleinGordonSynthesis

/-!
# Horizon-redshift and canonical-energy passivity for the theta Hawking sector

This endpoint replaces fixed-mass mirror dilation by the exponential redshift of an actual
Fulling--Davies horizon.  At surface gravity `kappa > 0`, the null ray

`p_kappa(v) = -kappa⁻¹ exp(-kappa v)`

is increasing and tends to a finite future horizon.  Its outgoing eikonal phase is
`exp(i eta exp(-kappa v))`.  Differentiating the theta-source scattering amplitude in `eta` at
zero inserts the genuine horizon weight `exp(-kappa v)`, hence moves the centered Xi frequency by
`-i kappa`:

`d/deta A_kappa(0, omega) = i XiC(omega - i kappa)`.

The two functional-equation partners enter the Euler zero-free half-plane at surface-gravity
thresholds `1/2 + Im(omega)` and `1/2 - Im(omega)`.  Equality of those two evaporation thresholds
at every theta resonance is exactly RH.  This is a horizon-redshift statement, not reciprocal-mass
dimensional analysis.

The second part isolates the requested dynamical-horizon passivity law.  A negative selectively
stimulated theta cubic has an explicit adjugate three-shell perturbation whose canonical quadratic
energy equals

`(positive two-shell minor) * (negative three-shell determinant)`.

It therefore has strictly negative energy.  Any source-faithful identification of this shell form
with nonnegative modified canonical-energy flux excludes the negative cubic chamber and forces RH.
Wall (arXiv:1105.3445) proves the generalized second law on arbitrary horizon slices under horizon
algebra hypotheses.  Hollands--Wald--Zhang (arXiv:2402.00818) identify the perturbative dynamical
black-hole second law with positivity of modified canonical-energy flux in general relativity.

**[PAPER-PROVED] [LEAN-PROVED]** The horizon ray, exact first redshift derivative, shifted-Xi
coefficient, threshold classification, explicit negative-energy witness, and passivity implication
are unconditional.

**[OPEN PHYSICAL WELD]** General relativity must identify the source-reconstructed theta shell
quadratic form below with its modified canonical-energy flux, or derive an equally strong
source-specific storage/port law.  Generic KMS, CCR, group, inverse, Krein, and unitary-dilation
identities do not make that identification and therefore do not supply the RH conclusion.
-/

open Complex Real MeasureTheory Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource

/-! ## A genuine exponential-horizon ray -/

/-- Fulling--Davies exponential ray with future horizon at null coordinate zero. -/
def thetaCuspHawkingExponentialHorizonRay (kappa v : ℝ) : ℝ :=
  -kappa⁻¹ * Real.exp (-kappa * v)

/-- The exponential-horizon ray has positive null slope. -/
theorem hasDerivAt_thetaCuspHawkingExponentialHorizonRay
    {kappa : ℝ} (hkappa : kappa ≠ 0) (v : ℝ) :
    HasDerivAt (thetaCuspHawkingExponentialHorizonRay kappa)
      (Real.exp (-kappa * v)) v := by
  have hinner : HasDerivAt (fun x : ℝ => -kappa * x) (-kappa) v := by
    simpa using (hasDerivAt_id v).const_mul (-kappa)
  have hexp := hinner.exp
  unfold thetaCuspHawkingExponentialHorizonRay
  have hscaled : HasDerivAt
      (fun x : ℝ => -kappa⁻¹ * Real.exp (-kappa * x))
      (-kappa⁻¹ * (Real.exp (-kappa * v) * -kappa)) v :=
    hexp.const_mul (-kappa⁻¹)
  convert hscaled using 1
  field_simp

/-- Positive surface gravity makes the ray future directed and orientation preserving. -/
theorem strictMono_thetaCuspHawkingExponentialHorizonRay
    {kappa : ℝ} (hkappa : 0 < kappa) :
    StrictMono (thetaCuspHawkingExponentialHorizonRay kappa) := by
  apply strictMono_of_hasDerivAt_pos
    (hasDerivAt_thetaCuspHawkingExponentialHorizonRay hkappa.ne')
  exact fun v => Real.exp_pos _

/-- The exponential ray reaches a finite future horizon. -/
theorem tendsto_thetaCuspHawkingExponentialHorizonRay_atTop
    {kappa : ℝ} (hkappa : 0 < kappa) :
    Tendsto (thetaCuspHawkingExponentialHorizonRay kappa) atTop (nhds 0) := by
  have hscale : Tendsto (fun v : ℝ => kappa * v) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hkappa tendsto_id
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  unfold thetaCuspHawkingExponentialHorizonRay
  convert hexp.const_mul (-kappa⁻¹) using 1 <;> simp

/-! ## Exact first horizon-redshift scattering coefficient -/

/-- Eikonal phase produced by the exponential horizon ray.  Physically `eta = omega_out/kappa`. -/
def thetaCuspHawkingHorizonRedshiftPhase (kappa eta v : ℝ) : ℂ :=
  Complex.exp
    (Complex.I * (((eta * Real.exp (-kappa * v) : ℝ) : ℂ)))

/-- Theta-source tangent amplitude on the exponential-horizon background. -/
def thetaCuspHawkingHorizonRedshiftAmplitude
    (kappa eta : ℝ) (omega : ℂ) : ℂ :=
  ∫ v : ℝ, thetaCuspHawkingHorizonRedshiftPhase kappa eta v *
    thetaCuspFourierLaplaceIntegrand omega v

theorem norm_thetaCuspHawkingHorizonRedshiftPhase
    (kappa eta v : ℝ) :
    ‖thetaCuspHawkingHorizonRedshiftPhase kappa eta v‖ = 1 := by
  rw [thetaCuspHawkingHorizonRedshiftPhase, Complex.norm_exp]
  rw [show (Complex.I * (((eta * Real.exp (-kappa * v) : ℝ) : ℂ))).re = 0 by
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self]]
  exact Real.exp_zero

theorem hasDerivAt_thetaCuspHawkingHorizonRedshiftPhase
    (kappa eta v : ℝ) :
    HasDerivAt (fun t : ℝ => thetaCuspHawkingHorizonRedshiftPhase kappa t v)
      (thetaCuspHawkingHorizonRedshiftPhase kappa eta v *
        (Complex.I * ((Real.exp (-kappa * v) : ℝ) : ℂ))) eta := by
  have hreal : HasDerivAt
      (fun t : ℝ => ((t * Real.exp (-kappa * v) : ℝ) : ℂ))
      ((Real.exp (-kappa * v) : ℝ) : ℂ) eta := by
    simpa using ((hasDerivAt_id eta).mul_const
      (Real.exp (-kappa * v))).ofReal_comp
  simpa [thetaCuspHawkingHorizonRedshiftPhase] using
    (hreal.const_mul Complex.I).cexp

private theorem integrable_horizonRedshiftDerivativeMajorant
    (kappa : ℝ) (omega : ℂ) :
    Integrable (fun v : ℝ =>
      Real.exp (-kappa * v) *
        ‖thetaCuspFourierLaplaceIntegrand omega v‖) := by
  have h := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource
    (omega.im - kappa)
  convert h using 1
  funext v
  rw [thetaCuspFourierLaplaceIntegrand, norm_mul, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs]
  have hsource : 0 ≤ thetaCuspFullSource v :=
    (thetaCuspFullSource_pos_all v).le
  rw [abs_of_nonneg hsource]
  have hre : (-Complex.I * omega * (v : ℂ)).re = omega.im * v := by
    simp [Complex.mul_re]
  rw [hre, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem horizonRedshiftFirstWindingIntegral_eq
    (kappa : ℝ) (omega : ℂ) :
    (∫ v : ℝ,
      (Complex.I * ((Real.exp (-kappa * v) : ℝ) : ℂ)) *
        thetaCuspFourierLaplaceIntegrand omega v) =
      Complex.I * XiC (omega - (kappa : ℂ) * Complex.I) := by
  rw [← thetaCuspFourierLaplace_eq_XiC_all,
    thetaCuspFourierLaplace, ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  rw [thetaCuspFourierLaplaceIntegrand,
    thetaCuspFourierLaplaceIntegrand]
  push_cast
  calc
    Complex.I * Complex.exp (-(kappa : ℂ) * (v : ℂ)) *
          (Complex.exp (-Complex.I * omega * (v : ℂ)) *
            (thetaCuspFullSource v : ℂ)) =
        Complex.I *
          (Complex.exp (-(kappa : ℂ) * (v : ℂ)) *
            Complex.exp (-Complex.I * omega * (v : ℂ))) *
          (thetaCuspFullSource v : ℂ) := by ring
    _ = Complex.I *
          Complex.exp (-(kappa : ℂ) * (v : ℂ) +
            (-Complex.I * omega * (v : ℂ))) *
          (thetaCuspFullSource v : ℂ) := by rw [Complex.exp_add]
    _ = Complex.I *
          (Complex.exp (-Complex.I *
            (omega - (kappa : ℂ) * Complex.I) * (v : ℂ)) *
            (thetaCuspFullSource v : ℂ)) := by
      have hexponent :
          -(kappa : ℂ) * (v : ℂ) + (-Complex.I * omega * (v : ℂ)) =
            -Complex.I * (omega - (kappa : ℂ) * Complex.I) * (v : ℂ) := by
        ring_nf
        simp only [Complex.I_sq]
        ring
      rw [hexponent]
      ring

/-- At zero outgoing eikonal parameter the horizon-background tangent is the ordinary theta/Xi
channel. -/
theorem thetaCuspHawkingHorizonRedshiftAmplitude_zero
    (kappa : ℝ) (omega : ℂ) :
    thetaCuspHawkingHorizonRedshiftAmplitude kappa 0 omega = XiC omega := by
  rw [← thetaCuspFourierLaplace_eq_XiC_all]
  simp [thetaCuspHawkingHorizonRedshiftAmplitude,
    thetaCuspHawkingHorizonRedshiftPhase, thetaCuspFourierLaplace]

/-- **Exact horizon-redshift law.**  The first outgoing eikonal derivative of the actual
exponential-horizon theta amplitude is the centered Xi value shifted by `-i kappa`. -/
theorem hasDerivAt_thetaCuspHawkingHorizonRedshiftAmplitude_zero
    (kappa : ℝ) (omega : ℂ) :
    HasDerivAt (fun eta : ℝ =>
      thetaCuspHawkingHorizonRedshiftAmplitude kappa eta omega)
      (Complex.I * XiC (omega - (kappa : ℂ) * Complex.I)) 0 := by
  let m : ℝ → ℝ → ℂ := thetaCuspHawkingHorizonRedshiftPhase kappa
  let m' : ℝ → ℝ → ℂ := fun eta v =>
    thetaCuspHawkingHorizonRedshiftPhase kappa eta v *
      (Complex.I * ((Real.exp (-kappa * v) : ℝ) : ℂ))
  let h : ℝ → ℂ := thetaCuspFourierLaplaceIntegrand omega
  let g : ℝ → ℝ := fun v => Real.exp (-kappa * v)
  have hmcont (eta : ℝ) : Continuous (fun v => m eta v) := by
    dsimp only [m]
    unfold thetaCuspHawkingHorizonRedshiftPhase
    fun_prop
  have hm_meas (eta : ℝ) :
      AEStronglyMeasurable (fun v => m eta v * h v) :=
    (hmcont eta).aestronglyMeasurable.mul
      (integrable_thetaCuspFourierLaplaceIntegrand_all omega).aestronglyMeasurable
  have hm_int : Integrable (fun v => m 0 v * h v) := by
    apply (integrable_thetaCuspFourierLaplaceIntegrand_all omega).bdd_mul
      ((hmcont 0).aestronglyMeasurable)
    filter_upwards with v
    dsimp only [m]
    rw [norm_thetaCuspHawkingHorizonRedshiftPhase]
  have hm'_meas : AEStronglyMeasurable (fun v => m' 0 v * h v) := by
    have hm'cont : Continuous (fun v => m' 0 v) := by
      dsimp only [m']
      unfold thetaCuspHawkingHorizonRedshiftPhase
      fun_prop
    exact hm'cont.aestronglyMeasurable.mul
      (integrable_thetaCuspFourierLaplaceIntegrand_all omega).aestronglyMeasurable
  have hderiv (eta v : ℝ) : HasDerivAt (fun t : ℝ => m t v) (m' eta v) eta := by
    exact hasDerivAt_thetaCuspHawkingHorizonRedshiftPhase kappa eta v
  have hbound (eta v : ℝ) : ‖m' eta v‖ ≤ g v := by
    dsimp only [m', g]
    rw [norm_mul, norm_thetaCuspHawkingHorizonRedshiftPhase, one_mul,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hg : Integrable (fun v => g v * ‖h v‖) := by
    exact integrable_horizonRedshiftDerivativeMajorant kappa omega
  have hmain := hasDerivAt_integral_symbol (μ := volume) (m := m) (m' := m')
    (h := h) (g := g) 0 hm_meas hm_int hm'_meas hderiv hbound hg
  have hcoeff : (∫ v : ℝ, m' 0 v * h v) =
      Complex.I * XiC (omega - (kappa : ℂ) * Complex.I) := by
    rw [← horizonRedshiftFirstWindingIntegral_eq kappa omega]
    apply integral_congr_ae
    filter_upwards with v
    dsimp only [m', h]
    simp only [thetaCuspHawkingHorizonRedshiftPhase, zero_mul,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  change HasDerivAt (fun eta : ℝ => ∫ v : ℝ, m eta v * h v) _ 0
  rw [← hcoeff]
  exact hmain

/-! ## Evaporation threshold synchronization -/

/-- Surface gravity at which the `omega - i kappa` first winding enters the Euler half-plane. -/
def thetaCuspHawkingFutureEulerEscapeSurfaceGravity (omega : ℂ) : ℝ :=
  1 / 2 + omega.im

/-- Corresponding threshold for the functional-equation partner `-omega`. -/
def thetaCuspHawkingPartnerEulerEscapeSurfaceGravity (omega : ℂ) : ℝ :=
  1 / 2 - omega.im

theorem thetaCuspHawkingEulerEscapeSurfaceGravities_pos_of_XiC_eq_zero
    {omega : ℂ} (homega : XiC omega = 0) :
    0 < thetaCuspHawkingFutureEulerEscapeSurfaceGravity omega ∧
      0 < thetaCuspHawkingPartnerEulerEscapeSurfaceGravity omega := by
  have hstrip := abs_im_lt_half_of_XiC_eq_zero homega
  rw [abs_lt] at hstrip
  constructor <;>
    simp only [thetaCuspHawkingFutureEulerEscapeSurfaceGravity,
      thetaCuspHawkingPartnerEulerEscapeSurfaceGravity] <;> linarith

/-- Above its exact Euler-entry threshold, the first horizon-redshift winding is certainly bright. -/
theorem XiC_horizonRedshift_future_ne_zero
    (omega : ℂ) {kappa : ℝ}
    (hkappa : thetaCuspHawkingFutureEulerEscapeSurfaceGravity omega < kappa) :
    XiC (omega - (kappa : ℂ) * Complex.I) ≠ 0 := by
  apply XiC_ne_zero_of_one_lt_re
  dsimp only [thetaCuspHawkingFutureEulerEscapeSurfaceGravity] at hkappa
  norm_num [Complex.mul_re]
  linarith

/-- Above the reflected threshold, the partner first winding is certainly bright. -/
theorem XiC_horizonRedshift_partner_ne_zero
    (omega : ℂ) {kappa : ℝ}
    (hkappa : thetaCuspHawkingPartnerEulerEscapeSurfaceGravity omega < kappa) :
    XiC (-omega - (kappa : ℂ) * Complex.I) ≠ 0 := by
  apply XiC_ne_zero_of_one_lt_re
  dsimp only [thetaCuspHawkingPartnerEulerEscapeSurfaceGravity] at hkappa
  norm_num [Complex.mul_re]
  linarith

/-- Above the future Euler-entry threshold, the measurable first horizon-redshift response is
nonzero. -/
theorem deriv_thetaCuspHawkingHorizonRedshiftAmplitude_future_ne_zero
    (omega : ℂ) {kappa : ℝ}
    (hkappa : thetaCuspHawkingFutureEulerEscapeSurfaceGravity omega < kappa) :
    deriv (fun eta : ℝ =>
      thetaCuspHawkingHorizonRedshiftAmplitude kappa eta omega) 0 ≠ 0 := by
  rw [(hasDerivAt_thetaCuspHawkingHorizonRedshiftAmplitude_zero kappa omega).deriv]
  exact mul_ne_zero Complex.I_ne_zero
    (XiC_horizonRedshift_future_ne_zero omega hkappa)

/-- Above the reflected Euler-entry threshold, the partner first horizon-redshift response is
nonzero. -/
theorem deriv_thetaCuspHawkingHorizonRedshiftAmplitude_partner_ne_zero
    (omega : ℂ) {kappa : ℝ}
    (hkappa : thetaCuspHawkingPartnerEulerEscapeSurfaceGravity omega < kappa) :
    deriv (fun eta : ℝ =>
      thetaCuspHawkingHorizonRedshiftAmplitude kappa eta (-omega)) 0 ≠ 0 := by
  rw [(hasDerivAt_thetaCuspHawkingHorizonRedshiftAmplitude_zero kappa (-omega)).deriv]
  exact mul_ne_zero Complex.I_ne_zero
    (XiC_horizonRedshift_partner_ne_zero omega hkappa)

/-- Every theta resonance and its reflected partner enter the Euler zero-free region at the same
surface gravity during Schwarzschild evaporation. -/
def ThetaCuspHawkingHorizonRedshiftThresholdSynchronized : Prop :=
  ∀ omega : ℂ, XiC omega = 0 →
    thetaCuspHawkingFutureEulerEscapeSurfaceGravity omega =
      thetaCuspHawkingPartnerEulerEscapeSurfaceGravity omega

/-- **Horizon-redshift RH endpoint.**  First-winding Euler-entry synchronization of every
functional-equation pair is exactly the Riemann hypothesis. -/
theorem thetaCuspHawkingHorizonRedshiftThresholdSynchronized_iff_riemannHypothesis :
    ThetaCuspHawkingHorizonRedshiftThresholdSynchronized ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hsync omega homega
    have h := hsync omega homega
    dsimp only [thetaCuspHawkingFutureEulerEscapeSurfaceGravity,
      thetaCuspHawkingPartnerEulerEscapeSurfaceGravity] at h
    linarith
  · intro hreal omega homega
    have him := hreal omega homega
    simp [thetaCuspHawkingFutureEulerEscapeSurfaceGravity,
      thetaCuspHawkingPartnerEulerEscapeSurfaceGravity, him]

/-! ## Explicit negative canonical-energy witness -/

/-- First coefficient of the adjugate probe for a symmetric three-shell response. -/
def threePointCanonicalEnergyProbeLeft
    (K : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  K y y * K x z - K x y * K y z

/-- Middle coefficient of the adjugate probe. -/
def threePointCanonicalEnergyProbeMiddle
    (K : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  K x x * K y z - K x y * K x z

/-- Last coefficient of the adjugate probe. -/
def threePointCanonicalEnergyProbeRight
    (K : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  K x y ^ 2 - K x x * K y y

/-- Adjugate identity: the canonical probe turns quadratic energy into leading minor times cubic
determinant. -/
theorem symmetricThreePointLongEdgeEnergy_canonicalProbe_eq
    (K : ℝ → ℝ → ℝ) (x y z : ℝ) :
    symmetricThreePointLongEdgeEnergy K x y z (K x z)
        (threePointCanonicalEnergyProbeLeft K x y z)
        (threePointCanonicalEnergyProbeMiddle K x y z)
        (threePointCanonicalEnergyProbeRight K x y) =
      (K x x * K y y - K x y ^ 2) *
        symmetricThreePointDet K x y z := by
  unfold symmetricThreePointLongEdgeEnergy
    threePointCanonicalEnergyProbeLeft
    threePointCanonicalEnergyProbeMiddle
    threePointCanonicalEnergyProbeRight
    symmetricThreePointDet
  ring

/-- A negative selectively stimulated theta cubic produces an explicit negative-energy
three-shell perturbation. -/
theorem thetaCuspHawking_negativeCubic_forces_negativeCanonicalEnergy
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (_hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0) :
    let K := thetaCuspHawkingSelectiveModularGainKernel q rapidity
    symmetricThreePointLongEdgeEnergy K x y z (K x z)
        (threePointCanonicalEnergyProbeLeft K x y z)
      (threePointCanonicalEnergyProbeMiddle K x y z)
        (threePointCanonicalEnergyProbeRight K x y) < 0 := by
  let K := thetaCuspHawkingSelectiveModularGainKernel q rapidity
  have hminor : 0 < K x x * K y y - K x y ^ 2 :=
    thetaCuspHawkingSelectiveModularGainKernel_twoPoint_det_pos
      q rapidity hx hxy
  dsimp only
  rw [symmetricThreePointLongEdgeEnergy_canonicalProbe_eq]
  exact mul_neg_of_pos_of_neg hminor hnegative

/-- Source-specific dynamical-horizon passivity: every real three-shell theta perturbation has
nonnegative modified canonical energy. -/
def ThetaCuspHawkingSelectiveCanonicalEnergyPassive : Prop :=
  ∀ (q : XiZeroCopy) (rapidity x y z : ℝ),
    0 < x → x < y → y < z →
      ∀ a b c : ℝ,
        0 ≤ symmetricThreePointLongEdgeEnergy
          (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z
          (thetaCuspHawkingSelectiveModularGainKernel q rapidity x z) a b c

/-- **Theta-specific backreaction exclusion.**  Canonical-energy passivity excludes every
negative stimulated cubic chamber. -/
theorem thetaCuspHawkingSelectiveCanonicalEnergyPassive_excludes_negativeCubic
    (hpassive : ThetaCuspHawkingSelectiveCanonicalEnergyPassive) :
    ThetaCuspHawkingSelectiveModularCubicStable := by
  intro q x y z rapidity hx hxy hyz
  by_contra hnonneg
  have hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0 :=
    lt_of_not_ge hnonneg
  let K := thetaCuspHawkingSelectiveModularGainKernel q rapidity
  have henergy := thetaCuspHawking_negativeCubic_forces_negativeCanonicalEnergy
    q rapidity hx hxy hyz hnegative
  have hpass := hpassive q rapidity x y z hx hxy hyz
    (threePointCanonicalEnergyProbeLeft K x y z)
    (threePointCanonicalEnergyProbeMiddle K x y z)
    (threePointCanonicalEnergyProbeRight K x y)
  exact (not_lt_of_ge hpass) henergy

/-- If general-relativistic modified canonical-energy positivity welds to the theta shell form,
every Xi orbit is critical. -/
theorem riemannHypothesis_of_thetaCuspHawkingSelectiveCanonicalEnergyPassive
    (hpassive : ThetaCuspHawkingSelectiveCanonicalEnergyPassive) :
    RiemannHypothesis :=
  riemannHypothesis_of_thetaCuspHawkingSelectiveModularCubicStable
    (thetaCuspHawkingSelectiveCanonicalEnergyPassive_excludes_negativeCubic hpassive)

/-- Actual causal-Hardy scattering specialization of the explicit negative-energy witness. -/
theorem thetaCuspHawkingCausalHardy_negativeCubic_forces_negativeCanonicalEnergy
    (q : XiZeroCopy)
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im)
    (horient : mode = thetaCuspHawkingXiOrbitResonantMode q ∨
      mode = thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q))
    (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity) x y z < 0) :
    let K := thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity
    symmetricThreePointLongEdgeEnergy K x y z (K x z)
        (threePointCanonicalEnergyProbeLeft K x y z)
        (threePointCanonicalEnergyProbeMiddle K x y z)
        (threePointCanonicalEnergyProbeRight K x y) < 0 := by
  dsimp only
  rw [thetaCuspHawkingCausalHardyStimulatedKernel_eq_selectiveModularGainKernel
    q mode hmode horient rapidity] at hnegative ⊢
  exact thetaCuspHawking_negativeCubic_forces_negativeCanonicalEnergy
    q rapidity hx hxy hyz hnegative

end RHTower
