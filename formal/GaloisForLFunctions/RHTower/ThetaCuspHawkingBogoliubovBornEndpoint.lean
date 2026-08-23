import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect

/-!
# Theta-cusp moving-mirror Bogoliubov endpoint

For a moving mirror with ray-tracing map `f`, the pair-production coefficient has numerator

`∫ exp (-i * incoming * v - i * outgoing * f v) * (outgoing * f' v - incoming) dv`.

Perturb the inertial ray by the literal theta-cusp profile,
`f_lambda(v) = v + lambda * thetaCuspFullSource(v)`.  Differentiation at `lambda = 0`
produces the unsquared complex Born numerator formalized below.  Fourier integration by parts gives

`BornRaw(outgoing, incoming) = 2 i outgoing incoming XiC(outgoing + incoming)`.

Thus the balanced physical coefficient has entire continuation

`B_theta(z) = -i z XiC(z) / (4 pi)`.

Its zero at the origin is kinematic.  Every other zero is a theta/Xi zero, so RH is exactly the
statement that every complex dark frequency of this Hawking pair-production amplitude lies on the
real physical-frequency sheet.  Unlike a particle-number spectrum, this endpoint retains the
complex Bogoliubov amplitude before taking its norm square.

The same theta source independently indexes every nonkinematic dark frequency by a nonzero mode
of its fixed compact inverse.  The singular-metric Green identity gives that source mode an exact
two-port gain/loss law: boundary current equals imaginary frequency times metric energy, sharpened
to `2 * mass * Im(z) * rootEnergy`.  This source identity does not by itself identify a zero of the
prescribed-trajectory Born coefficient with a dynamical normal mode of the moving-mirror QFT.  The
final section isolates that missing Born/partner Ward identification as the physical open core.
-/

open Complex Real MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- First variation of the moving-mirror Bogoliubov numerator at the inertial trajectory. -/
def thetaCuspMovingMirrorBornRaw
    (outgoingFrequency incomingFrequency : ℝ) : ℂ :=
  let totalFrequency := outgoingFrequency + incomingFrequency
  let fourierFrequency := totalFrequency / (2 * Real.pi)
  (outgoingFrequency : ℂ) *
      FourierTransform.fourier
        (SchwartzMap.derivCLM ℂ ℂ thetaCuspSchwartz : ℝ → ℂ)
        fourierFrequency -
    Complex.I * (outgoingFrequency : ℂ) *
      ((outgoingFrequency - incomingFrequency : ℝ) : ℂ) *
      FourierTransform.fourier (thetaCuspSchwartz : ℝ → ℂ)
        fourierFrequency

/-- Moving-mirror first variation factorizes into universal kinematics and the completed source. -/
theorem thetaCuspMovingMirrorBornRaw_eq_XiC
    (outgoingFrequency incomingFrequency : ℝ) :
    thetaCuspMovingMirrorBornRaw outgoingFrequency incomingFrequency =
      2 * Complex.I * (outgoingFrequency : ℂ) *
        (incomingFrequency : ℂ) *
        XiC ((outgoingFrequency + incomingFrequency : ℝ) : ℂ) := by
  let xiFrequency : ℝ :=
    (outgoingFrequency + incomingFrequency) / (2 * Real.pi)
  have hfourierDeriv := congrFun
    (Real.fourier_deriv
      (f := (thetaCuspSchwartz : ℝ → ℂ))
      thetaCuspSchwartz.integrable
      thetaCuspSchwartz.differentiable
      (SchwartzMap.derivCLM ℂ ℂ thetaCuspSchwartz).integrable) xiFrequency
  have hderivfun : deriv (thetaCuspSchwartz : ℝ → ℂ) =
      (SchwartzMap.derivCLM ℂ ℂ thetaCuspSchwartz : ℝ → ℂ) := by
    funext x
    rfl
  rw [hderivfun] at hfourierDeriv
  have hsource :
      FourierTransform.fourier (thetaCuspSchwartz : ℝ → ℂ) xiFrequency =
        XiC ((outgoingFrequency + incomingFrequency : ℝ) : ℂ) := by
    simpa only [SchwartzMap.fourier_coe, xiFrequency] using
      fourier_thetaCuspSchwartz_scaled (outgoingFrequency + incomingFrequency)
  rw [thetaCuspMovingMirrorBornRaw]
  change (outgoingFrequency : ℂ) *
      FourierTransform.fourier
        (SchwartzMap.derivCLM ℂ ℂ thetaCuspSchwartz : ℝ → ℂ) xiFrequency -
    Complex.I * (outgoingFrequency : ℂ) *
      ((outgoingFrequency - incomingFrequency : ℝ) : ℂ) *
      FourierTransform.fourier (thetaCuspSchwartz : ℝ → ℂ) xiFrequency = _
  rw [hfourierDeriv]
  simp only [smul_eq_mul]
  rw [hsource]
  dsimp [xiFrequency]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- Entire balanced-frequency Hawking pair-production amplitude of the theta-cusp trajectory. -/
def thetaCuspBalancedHawkingBornAmplitude (z : ℂ) : ℂ :=
  (-Complex.I / (4 * (Real.pi : ℂ))) * z * thetaCuspFourierLaplace z

/-- The balanced coefficient is the kinematic linear factor times the completed Xi amplitude. -/
theorem thetaCuspBalancedHawkingBornAmplitude_eq_XiC (z : ℂ) :
    thetaCuspBalancedHawkingBornAmplitude z =
      (-Complex.I / (4 * (Real.pi : ℂ))) * z * XiC z := by
  rw [thetaCuspBalancedHawkingBornAmplitude,
    HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all]

/-- For positive total frequency, the left side is the standard balanced Bogoliubov prefactor
times the first-variation numerator.  The identity extends algebraically through zero. -/
theorem thetaCuspMovingMirrorBornRaw_balanced (totalFrequency : ℝ) :
    (-1 / (2 * Real.pi * totalFrequency : ℝ) : ℂ) *
        thetaCuspMovingMirrorBornRaw (totalFrequency / 2) (totalFrequency / 2) =
      thetaCuspBalancedHawkingBornAmplitude (totalFrequency : ℂ) := by
  rw [thetaCuspMovingMirrorBornRaw_eq_XiC,
    thetaCuspBalancedHawkingBornAmplitude_eq_XiC]
  push_cast
  by_cases hzero : totalFrequency = 0
  · simp [hzero]
  · field_simp [hzero, Real.pi_ne_zero]
    ring_nf

/-- Every complex dark frequency of the theta-cusp Hawking Born amplitude is physical. -/
def ThetaCuspHawkingBornDarkFrequenciesPhysical : Prop :=
  ∀ z : ℂ, thetaCuspBalancedHawkingBornAmplitude z = 0 → z.im = 0

/-- **Hawking Bogoliubov endpoint.**  RH is exactly physical-sheet confinement of all dark
frequencies of the source-defined balanced pair-production amplitude. -/
theorem riemannHypothesis_iff_thetaCuspHawkingBornDarkFrequenciesPhysical :
    RiemannHypothesis ↔ ThetaCuspHawkingBornDarkFrequenciesPhysical := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro h z hz
    rw [thetaCuspBalancedHawkingBornAmplitude_eq_XiC] at hz
    rcases mul_eq_zero.mp hz with hkin | hXi
    · rcases mul_eq_zero.mp hkin with hconst | hz0
      · exfalso
        exact (div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
          (mul_ne_zero (by norm_num)
            (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) hconst
      · rw [hz0]
        simp
    · exact h z hXi
  · intro h z hz
    exact h z (by rw [thetaCuspBalancedHawkingBornAmplitude_eq_XiC, hz, mul_zero])

/-! ## Theta source modes indexed by Born-dark frequencies -/

open HedenmalmQuantile HedenmalmThetaSource HedenmalmHilbertSchmidt

private abbrev ThetaHawkingKreinH := Lp ℂ 2 unitIntervalMeasure

/-- Universal source-horizon balance law.  For every eigenmode of the fixed theta inverse, its
oriented rank-two boundary current is twice eigenfrequency growth rate times singular-metric
energy. -/
theorem thetaMetric_hawkingKrein_balance
    {mu : ℂ} {g : ThetaHawkingKreinH}
    (heigen : thetaKernelOperator g = mu • g) :
    (inner ℂ (pinnedBoundaryCLM g) g : ℂ) =
      2 * (mu.im : ℂ) *
        (inner ℂ (thetaMetricOperator g) g : ℂ) := by
  have hcomm := congrArg
    (fun A : ThetaHawkingKreinH →L[ℂ] ThetaHawkingKreinH => A g)
    thetaMetric_commutator_thetaKernelOperator
  simp only [sub_apply, mul_apply_eq_comp, smul_apply] at hcomm
  have hinner := congrArg (fun u : ThetaHawkingKreinH => inner ℂ u g) hcomm
  rw [heigen, map_smul, inner_sub_left, inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, heigen, inner_smul_right,
    inner_smul_left] at hinner
  have hconj : starRingEnd ℂ mu - mu = -2 * Complex.I * (mu.im : ℂ) := by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [← sub_mul, hconj, Complex.conj_I] at hinner
  have hI : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  apply mul_left_cancel₀ hI
  calc
    -Complex.I * (inner ℂ (pinnedBoundaryCLM g) g : ℂ) =
        (-2 * Complex.I * (mu.im : ℂ)) *
          (inner ℂ (thetaMetricOperator g) g : ℂ) := hinner.symm
    _ = -Complex.I *
        (2 * (mu.im : ℂ) *
          (inner ℂ (thetaMetricOperator g) g : ℂ)) := by ring

/-- Nonkinematic complex dark frequencies of the actual theta-cusp Born amplitude. -/
def ThetaCuspHawkingDarkFrequency :=
  {z : ℂ // thetaCuspBalancedHawkingBornAmplitude z = 0 ∧ z ≠ 0}

theorem thetaCuspHawkingDarkFrequency_XiC_eq_zero
    (d : ThetaCuspHawkingDarkFrequency) : XiC d.1 = 0 := by
  have hdark := d.2.1
  rw [thetaCuspBalancedHawkingBornAmplitude_eq_XiC] at hdark
  rcases mul_eq_zero.mp hdark with hkin | hXi
  · rcases mul_eq_zero.mp hkin with hconst | hz
    · exfalso
      exact (div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
        (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) hconst
    · exact (d.2.2 hz).elim
  · exact hXi

theorem thetaCuspHawkingDarkFrequency_mem_sourceStrip
    (d : ThetaCuspHawkingDarkFrequency) : |d.1.im| < 1 :=
  abs_im_lt_one_of_XiC_eq_zero (thetaCuspHawkingDarkFrequency_XiC_eq_zero d)

theorem thetaCuspHawkingDarkFrequency_source_zero
    (d : ThetaCuspHawkingDarkFrequency) : xiC thetaSource d.1 = 0 := by
  rw [xiC_thetaSource_all, thetaCuspHawkingDarkFrequency_XiC_eq_zero]

/-- Compact theta-source mode indexed by one nonkinematic dark Born frequency. -/
def thetaCuspHawkingKreinMode
    (d : ThetaCuspHawkingDarkFrequency) : ThetaHawkingKreinH :=
  thetaDivisorEigenvector d.1
    (thetaCuspHawkingDarkFrequency_mem_sourceStrip d)
    (thetaCuspHawkingDarkFrequency_source_zero d)

/-- Strictly positive root energy carried by the trapped theta mode. -/
def thetaCuspHawkingKreinEnergy (d : ThetaCuspHawkingDarkFrequency) : ℝ :=
  thetaRootEnergy d.1

/-- Oriented rank-two gain/loss current through the source horizon. -/
def thetaCuspHawkingKreinFlux (d : ThetaCuspHawkingDarkFrequency) : ℝ :=
  (inner ℂ (pinnedBoundaryCLM (thetaCuspHawkingKreinMode d))
    (thetaCuspHawkingKreinMode d)).re

theorem thetaCuspHawkingKreinMode_ne_zero
    (d : ThetaCuspHawkingDarkFrequency) : thetaCuspHawkingKreinMode d ≠ 0 := by
  exact thetaDivisorEigenvector_ne_zero d.1
    (thetaCuspHawkingDarkFrequency_mem_sourceStrip d)
    (thetaCuspHawkingDarkFrequency_source_zero d)

theorem thetaKernelOperator_thetaCuspHawkingKreinMode
    (d : ThetaCuspHawkingDarkFrequency) :
    thetaKernelOperator (thetaCuspHawkingKreinMode d) =
      (-d.1⁻¹) • thetaCuspHawkingKreinMode d := by
  rw [thetaKernelOperator_eq_thetaCompactSourceInverse]
  exact thetaCompactSourceInverse_eigen d.1
    (thetaCuspHawkingDarkFrequency_mem_sourceStrip d)
    (thetaCuspHawkingDarkFrequency_source_zero d)

theorem thetaCuspHawkingKreinEnergy_pos
    (d : ThetaCuspHawkingDarkFrequency) : 0 < thetaCuspHawkingKreinEnergy d := by
  exact thetaRootEnergy_pos
    (thetaCuspHawkingDarkFrequency_mem_sourceStrip d)
    (thetaCuspHawkingDarkFrequency_source_zero d)

/-- Explicit Hawking gain/loss law in the physical frequency coordinate. -/
theorem thetaCuspHawkingKreinFlux_eq
    (d : ThetaCuspHawkingDarkFrequency) :
    thetaCuspHawkingKreinFlux d =
      2 * thetaSource.mass * d.1.im * thetaCuspHawkingKreinEnergy d := by
  rw [thetaCuspHawkingKreinFlux, thetaCuspHawkingKreinMode,
    inner_pinnedBoundaryCLM_thetaDivisorEigenvector]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, thetaCuspHawkingKreinEnergy]
  ring

/-- A dark trapped mode is flux-neutral exactly when its Born frequency is physical. -/
theorem thetaCuspHawkingKreinFlux_eq_zero_iff
    (d : ThetaCuspHawkingDarkFrequency) :
    thetaCuspHawkingKreinFlux d = 0 ↔ d.1.im = 0 := by
  rw [thetaCuspHawkingKreinFlux_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | henergy
    · rcases mul_eq_zero.mp hleft with hleft | him
      · rcases mul_eq_zero.mp hleft with htwo | hmass
        · norm_num at htwo
        · exact (ne_of_gt thetaSource.mass_pos hmass).elim
      · exact him
    · exact (ne_of_gt (thetaCuspHawkingKreinEnergy_pos d) henergy).elim
  · intro him
    rw [him, mul_zero, zero_mul]

/-! ## Hawking partner ports and the Born/Green consistency wall -/

/-- Incoming positive-norm boundary port of the theta mode indexed by a Born-dark frequency. -/
def thetaCuspHawkingInPortAmplitude
    (d : ThetaCuspHawkingDarkFrequency) : ℂ :=
  pinnedInAmplitude (thetaCuspHawkingKreinMode d)

/-- Outgoing partner boundary port of the theta mode indexed by a Born-dark frequency. -/
def thetaCuspHawkingOutPortAmplitude
    (d : ThetaCuspHawkingDarkFrequency) : ℂ :=
  pinnedOutAmplitude (thetaCuspHawkingKreinMode d)

/-- **Partner-port Ward law.** The difference of positive and partner intensities is exactly the
oriented Green flux. This is the source-side analogue of the signed norm law for a two-channel
Bogoliubov transformation. -/
theorem thetaCuspHawkingPortIntensityDifference_eq_flux
    (d : ThetaCuspHawkingDarkFrequency) :
    (‖thetaCuspHawkingInPortAmplitude d‖ : ℂ) ^ 2 -
        (‖thetaCuspHawkingOutPortAmplitude d‖ : ℂ) ^ 2 =
      Complex.ofReal (thetaCuspHawkingKreinFlux d) := by
  rw [thetaCuspHawkingInPortAmplitude, thetaCuspHawkingOutPortAmplitude,
    ← inner_pinnedBoundaryCLM_eq_amplitudes]
  rw [thetaCuspHawkingKreinMode,
    inner_pinnedBoundaryCLM_thetaDivisorEigenvector,
    thetaCuspHawkingKreinFlux_eq]
  simp only [thetaCuspHawkingKreinEnergy]
  push_cast
  ring

/-- Partner intensities balance exactly on the physical frequency sheet. -/
theorem thetaCuspHawkingPortIntensities_eq_iff
    (d : ThetaCuspHawkingDarkFrequency) :
    ‖thetaCuspHawkingInPortAmplitude d‖ =
        ‖thetaCuspHawkingOutPortAmplitude d‖ ↔
      d.1.im = 0 := by
  constructor
  · intro hports
    have hflux := thetaCuspHawkingPortIntensityDifference_eq_flux d
    rw [hports] at hflux
    have hzero : thetaCuspHawkingKreinFlux d = 0 := by
      exact Complex.ofReal_eq_zero.mp (by simpa using hflux.symm)
    exact (thetaCuspHawkingKreinFlux_eq_zero_iff d).mp hzero
  · intro him
    have hflux : thetaCuspHawkingKreinFlux d = 0 :=
      (thetaCuspHawkingKreinFlux_eq_zero_iff d).mpr him
    have hsq := thetaCuspHawkingPortIntensityDifference_eq_flux d
    rw [hflux, Complex.ofReal_zero, sub_eq_zero] at hsq
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
      exact_mod_cast hsq)

/-- **Born/port mismatch no-go.** At a hypothetical nonreal Xi zero, the prescribed-trajectory
Born coefficient is dark while the source Green partner ports are provably imbalanced. Thus the
Born zero and the trapped source mode cannot be identified as one canonically unitary Hawking
channel without an additional source-derived Ward or backreaction law. -/
theorem thetaCuspHawkingBornDark_port_imbalance_of_nonreal
    (d : ThetaCuspHawkingDarkFrequency) (him : d.1.im ≠ 0) :
    thetaCuspBalancedHawkingBornAmplitude d.1 = 0 ∧
      ‖thetaCuspHawkingInPortAmplitude d‖ ≠
        ‖thetaCuspHawkingOutPortAmplitude d‖ := by
  exact ⟨d.2.1, fun hports =>
    him ((thetaCuspHawkingPortIntensities_eq_iff d).mp hports)⟩

/-- Operator form of the Hawking--Krein balance on every actual dark trapped mode. -/
theorem thetaCuspHawkingKreinMode_balance
    (d : ThetaCuspHawkingDarkFrequency) :
    (inner ℂ (pinnedBoundaryCLM (thetaCuspHawkingKreinMode d))
      (thetaCuspHawkingKreinMode d) : ℂ) =
      2 * ((-d.1⁻¹).im : ℂ) *
        (inner ℂ (thetaMetricOperator (thetaCuspHawkingKreinMode d))
          (thetaCuspHawkingKreinMode d) : ℂ) :=
  thetaMetric_hawkingKrein_balance
    (thetaKernelOperator_thetaCuspHawkingKreinMode d)

/-- No nonkinematic dark theta-Hawking mode carries a gain/loss current. -/
def ThetaCuspHawkingKreinStable : Prop :=
  ∀ d : ThetaCuspHawkingDarkFrequency, thetaCuspHawkingKreinFlux d = 0

/-- Source Green endpoint: RH is exactly absence of gain/loss current on every compact theta mode
indexed by a nonkinematic dark frequency of the theta-cusp moving-mirror Born amplitude. -/
theorem riemannHypothesis_iff_thetaCuspHawkingKreinStable :
    RiemannHypothesis ↔ ThetaCuspHawkingKreinStable := by
  rw [riemannHypothesis_iff_thetaCuspHawkingBornDarkFrequenciesPhysical]
  constructor
  · intro h d
    exact (thetaCuspHawkingKreinFlux_eq_zero_iff d).2 (h d.1 d.2.1)
  · intro h z hz
    by_cases hz0 : z = 0
    · rw [hz0]
      simp
    · let d : ThetaCuspHawkingDarkFrequency := ⟨z, hz, hz0⟩
      exact (thetaCuspHawkingKreinFlux_eq_zero_iff d).1 (h d)

/-- Source-specific Born/partner Ward consistency: every nonkinematic Born-dark frequency also has
balanced positive/partner Green ports. Unlike scalar KMS passivity, this condition retains the
signed two-channel Bogoliubov datum. Proving it from a backreacted theta-cusp horizon dynamics is
the route's open producer, not part of this definition. -/
def ThetaCuspHawkingBornPortConsistent : Prop :=
  ∀ d : ThetaCuspHawkingDarkFrequency,
    ‖thetaCuspHawkingInPortAmplitude d‖ =
      ‖thetaCuspHawkingOutPortAmplitude d‖

/-- **Born/partner-port endpoint.** RH is exactly source-wide consistency between darkness of the
theta-cusp pair-production amplitude and neutrality of the associated two-channel Green ports. -/
theorem riemannHypothesis_iff_thetaCuspHawkingBornPortConsistent :
    RiemannHypothesis ↔ ThetaCuspHawkingBornPortConsistent := by
  rw [riemannHypothesis_iff_thetaCuspHawkingKreinStable]
  constructor
  · intro h d
    exact (thetaCuspHawkingPortIntensities_eq_iff d).mpr
      ((thetaCuspHawkingKreinFlux_eq_zero_iff d).mp (h d))
  · intro h d
    exact (thetaCuspHawkingKreinFlux_eq_zero_iff d).mpr
      ((thetaCuspHawkingPortIntensities_eq_iff d).mp (h d))

end RHTower
