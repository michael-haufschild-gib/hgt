import GaloisForLFunctions.HTGeometry.HorizonThermalSpectrumClockSeparationUniversalityLaw
import GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA
import Mathlib.Analysis.Real.Cardinality

/-!
# Exponential-collapse history-clock universality

In the exponential-peeling approximation to a spherically symmetric collapse, the positive
normalization `historyScale` of the affine null map enters the Bogoliubov carrier only through

`exp (-i * (omega / kappa) * log (incomingFrequency * historyScale))`.

This file proves that every positive history scale has exactly the same intensity, while one
phase-slope value recovers that scale exactly.  Thus a continuum of distinct collapse clocks shares
one intensity.  It also specializes the universal one-turn Gamma law to the physical product
`incomingFrequency * historyScale`.

The mathematical result is an exact statement about the exponential-peeling channel.  It makes no
claim that a particular matter equation of state forces horizon formation or exact exponential
peeling.
-/

open Filter Set Topology Function Complex
open scoped Cardinal Differential UnivMeroFieldInstances

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

/-- Dimensionless positive scale in the exponential-collapse Bogoliubov phase. -/
def exponentialCollapseHistoryRatio
    (incomingFrequency historyScale : ℝ) : ℝ :=
  incomingFrequency * historyScale

/-- The dimensionless history coordinate is invariant under reciprocal rescaling of the affine
null coordinate and its conjugate frequency. -/
theorem exponentialCollapseHistoryRatio_rescale
    {incomingFrequency historyScale affineScale : ℝ}
    (haffine : affineScale ≠ 0) :
    exponentialCollapseHistoryRatio
        (incomingFrequency / affineScale) (affineScale * historyScale) =
      exponentialCollapseHistoryRatio incomingFrequency historyScale := by
  unfold exponentialCollapseHistoryRatio
  field_simp [haffine]

/-- Phase-carrying part of the exponential-collapse Bogoliubov coefficient. -/
def exponentialCollapseHistoryCarrier
    (incomingFrequency historyScale x : ℝ) : ℂ :=
  horizonBogoliubovPhaseCarrier
    (exponentialCollapseHistoryRatio incomingFrequency historyScale) x

/-- Dimensionless phase slope of the exponential-collapse channel. -/
def exponentialCollapseHistoryClock
    (incomingFrequency historyScale x : ℝ) : ℝ :=
  horizonBogoliubovChannelPhaseSlope
    (exponentialCollapseHistoryRatio incomingFrequency historyScale) x

/-- The complete phase carrier is invariant under reciprocal affine-frequency rescaling. -/
theorem exponentialCollapseHistoryCarrier_rescale
    {incomingFrequency historyScale affineScale x : ℝ}
    (haffine : affineScale ≠ 0) :
    exponentialCollapseHistoryCarrier
        (incomingFrequency / affineScale) (affineScale * historyScale) x =
      exponentialCollapseHistoryCarrier incomingFrequency historyScale x := by
  unfold exponentialCollapseHistoryCarrier
  rw [exponentialCollapseHistoryRatio_rescale haffine]

/-- The phase clock is invariant under reciprocal affine-frequency rescaling. -/
theorem exponentialCollapseHistoryClock_rescale
    {incomingFrequency historyScale affineScale x : ℝ}
    (haffine : affineScale ≠ 0) :
    exponentialCollapseHistoryClock
        (incomingFrequency / affineScale) (affineScale * historyScale) x =
      exponentialCollapseHistoryClock incomingFrequency historyScale x := by
  unfold exponentialCollapseHistoryClock
  rw [exponentialCollapseHistoryRatio_rescale haffine]

/-- The named collapse clock is exactly the imaginary logarithmic derivative of the
phase-carrying coefficient. -/
theorem exponentialCollapseHistoryCarrier_logDeriv_im
    {incomingFrequency historyScale x : ℝ} (hx : x ≠ 0) :
    ((deriv
        (exponentialCollapseHistoryCarrier incomingFrequency historyScale) x) /
      exponentialCollapseHistoryCarrier incomingFrequency historyScale x).im =
      exponentialCollapseHistoryClock incomingFrequency historyScale x := by
  exact horizonBogoliubovPhaseCarrier_logDeriv_im hx

/-- Exact Gamma evaluation of the ideal exponential-peeling Bogoliubov coefficient, up to one
constant unit-modulus convention. -/
def exponentialPeelingBogoliubovCoefficient
    (kappa historyScale outgoingFrequency incomingFrequency : ℝ) : ℂ :=
  ((Real.sqrt (outgoingFrequency / incomingFrequency) /
      (2 * Real.pi * kappa) *
      Real.exp (-Real.pi * outgoingFrequency / (2 * kappa)) : ℝ) : ℂ) *
    exponentialCollapseHistoryCarrier incomingFrequency historyScale
      (outgoingFrequency / kappa)

/-- Exact squared modulus of the imaginary-axis Gamma carrier. -/
theorem normSq_Gamma_I_mul
    {x : ℝ} (hx : x ≠ 0) :
    Complex.normSq (Complex.Gamma (Complex.I * (x : ℂ))) =
      Real.pi / (x * Real.sinh (Real.pi * x)) := by
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  change star (Complex.Gamma (Complex.I * (x : ℂ))) *
      Complex.Gamma (Complex.I * (x : ℂ)) =
    (Real.pi / (x * Real.sinh (Real.pi * x)) : ℝ)
  rw [← gamma_imaginary_conjugate_frequency x, mul_comm,
    gamma_imaginary_reflection_planck x hx]
  norm_cast

/-- The affine history factor is invisible to intensity for every scale and every frequency. -/
theorem norm_exponentialCollapseHistoryCarrier
    (incomingFrequency historyScale x : ℝ) :
    ‖exponentialCollapseHistoryCarrier incomingFrequency historyScale x‖ =
      ‖Complex.Gamma (Complex.I * (x : ℂ))‖ := by
  unfold exponentialCollapseHistoryCarrier horizonBogoliubovPhaseCarrier
  rw [norm_mul, Complex.norm_exp]
  simp

/-- Any two positive history scales have identical carrier intensity at every frequency. -/
theorem normSq_exponentialCollapseHistoryCarrier_eq
    {incomingFrequency historyScale₁ historyScale₂ : ℝ}
    (x : ℝ) :
    Complex.normSq
        (exponentialCollapseHistoryCarrier incomingFrequency historyScale₁ x) =
      Complex.normSq
        (exponentialCollapseHistoryCarrier incomingFrequency historyScale₂ x) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    norm_exponentialCollapseHistoryCarrier,
    norm_exponentialCollapseHistoryCarrier]

/-- Any two history scales give the same full ideal exponential-peeling intensity. -/
theorem normSq_exponentialPeelingBogoliubovCoefficient_historyScale_eq
    (kappa historyScale₁ historyScale₂ outgoingFrequency incomingFrequency : ℝ) :
    Complex.normSq
        (exponentialPeelingBogoliubovCoefficient
          kappa historyScale₁ outgoingFrequency incomingFrequency) =
      Complex.normSq
        (exponentialPeelingBogoliubovCoefficient
          kappa historyScale₂ outgoingFrequency incomingFrequency) := by
  unfold exponentialPeelingBogoliubovCoefficient
  rw [Complex.normSq_mul, Complex.normSq_mul,
    normSq_exponentialCollapseHistoryCarrier_eq]

/-- **Exact perfect thermality.**  The ideal exponential-peeling coefficient has Planck intensity
for every positive affine history scale; the history scale is absent from the result. -/
theorem normSq_exponentialPeelingBogoliubovCoefficient_eq_planck
    {kappa historyScale outgoingFrequency incomingFrequency : ℝ}
    (hkappa : 0 < kappa)
    (_hhistory : 0 < historyScale)
    (houtgoing : 0 < outgoingFrequency)
    (hincoming : 0 < incomingFrequency) :
    Complex.normSq
        (exponentialPeelingBogoliubovCoefficient
          kappa historyScale outgoingFrequency incomingFrequency) =
      1 / (2 * Real.pi * kappa * incomingFrequency) /
        (Real.exp (2 * Real.pi * outgoingFrequency / kappa) - 1) := by
  have hx : outgoingFrequency / kappa ≠ 0 :=
    (div_pos houtgoing hkappa).ne'
  have hsqrt :
      Real.sqrt (outgoingFrequency / incomingFrequency) ^ (2 : ℕ) =
        outgoingFrequency / incomingFrequency := by
    rw [Real.sq_sqrt (div_nonneg houtgoing.le hincoming.le)]
  have hcarrier :
      Complex.normSq
          (exponentialCollapseHistoryCarrier incomingFrequency historyScale
            (outgoingFrequency / kappa)) =
        Real.pi /
          ((outgoingFrequency / kappa) *
            Real.sinh (Real.pi * (outgoingFrequency / kappa))) := by
    rw [Complex.normSq_eq_norm_sq,
      norm_exponentialCollapseHistoryCarrier,
      ← Complex.normSq_eq_norm_sq]
    exact normSq_Gamma_I_mul hx
  unfold exponentialPeelingBogoliubovCoefficient
  rw [Complex.normSq_mul, Complex.normSq_ofReal, hcarrier]
  rw [show
      Real.sqrt (outgoingFrequency / incomingFrequency) /
            (2 * Real.pi * kappa) *
            Real.exp (-Real.pi * outgoingFrequency / (2 * kappa)) *
          (Real.sqrt (outgoingFrequency / incomingFrequency) /
            (2 * Real.pi * kappa) *
            Real.exp (-Real.pi * outgoingFrequency / (2 * kappa))) =
        (outgoingFrequency / incomingFrequency) /
            (2 * Real.pi * kappa) ^ (2 : ℕ) *
          Real.exp (-Real.pi * outgoingFrequency / kappa) by
      rw [← pow_two, mul_pow, div_pow, hsqrt,
        pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring]
  have hkappaNe : kappa ≠ 0 := hkappa.ne'
  have hincomingNe : incomingFrequency ≠ 0 := hincoming.ne'
  have houtgoingNe : outgoingFrequency ≠ 0 := houtgoing.ne'
  have hpiNe : Real.pi ≠ 0 := Real.pi_ne_zero
  have ha :
      0 < Real.pi * (outgoingFrequency / kappa) := by
    positivity
  have hsinhNe :
      Real.sinh (Real.pi * (outgoingFrequency / kappa)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr ha).ne'
  have hexpNe :
      Real.exp (2 * Real.pi * outgoingFrequency / kappa) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by
      exact ne_of_gt ((Real.one_lt_exp_iff).2 (by positivity)))
  field_simp [hkappaNe, hincomingNe, houtgoingNe, hpiNe, hexpNe, hsinhNe]
  rw [Real.sinh_eq, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring_nf
  rw [pow_two (Real.exp _), ← Real.exp_add]
  have harg :
      outgoingFrequency * Real.pi * kappa⁻¹ +
          outgoingFrequency * Real.pi * kappa⁻¹ =
        outgoingFrequency * Real.pi * kappa⁻¹ * 2 := by
    ring
  rw [harg]
  have hdenom :
      -1 + Real.exp (outgoingFrequency * Real.pi * kappa⁻¹ * 2) ≠ 0 := by
    intro hzero
    apply hexpNe
    have hargs :
        2 * Real.pi * outgoingFrequency / kappa =
          outgoingFrequency * Real.pi * kappa⁻¹ * 2 := by
      field_simp [hkappaNe]
    rw [hargs]
    linarith
  field_simp [hdenom]
  have hnormalize :
      outgoingFrequency * Real.pi * 2 / kappa =
        outgoingFrequency * Real.pi * kappa⁻¹ * 2 := by
    field_simp [hkappaNe]
  rw [hnormalize]
  convert (div_self hdenom).symm using 1
  ring

/-- Changing collapse history translates the phase clock by the logarithm of the scale ratio. -/
theorem exponentialCollapseHistoryClock_sub
    {incomingFrequency historyScale₁ historyScale₂ x : ℝ}
    (hincoming : 0 < incomingFrequency)
    (hhistory₁ : 0 < historyScale₁)
    (hhistory₂ : 0 < historyScale₂) :
    exponentialCollapseHistoryClock incomingFrequency historyScale₁ x -
        exponentialCollapseHistoryClock incomingFrequency historyScale₂ x =
      Real.log (historyScale₂ / historyScale₁) := by
  unfold exponentialCollapseHistoryClock exponentialCollapseHistoryRatio
    horizonBogoliubovChannelPhaseSlope
  rw [Real.log_mul hincoming.ne' hhistory₁.ne',
    Real.log_mul hincoming.ne' hhistory₂.ne',
    Real.log_div hhistory₂.ne' hhistory₁.ne']
  ring

/-- At any fixed frequency, distinct positive affine history scales give distinct phase clocks. -/
theorem exponentialCollapseHistoryClock_injective
    {incomingFrequency x : ℝ} (hincoming : 0 < incomingFrequency) :
    Function.Injective
      (fun historyScale : Set.Ioi (0 : ℝ) =>
        exponentialCollapseHistoryClock incomingFrequency historyScale x) := by
  intro historyScale₁ historyScale₂ hclock
  apply Subtype.ext
  change
    exponentialCollapseHistoryClock incomingFrequency (historyScale₁ : ℝ) x =
      exponentialCollapseHistoryClock incomingFrequency (historyScale₂ : ℝ) x at hclock
  have hlog :
      Real.log ((historyScale₂ : ℝ) / (historyScale₁ : ℝ)) = 0 := by
    have hsub := exponentialCollapseHistoryClock_sub hincoming
      historyScale₁.property historyScale₂.property (x := x)
    linarith
  have hratio :
      (historyScale₂ : ℝ) / (historyScale₁ : ℝ) = 1 := by
    exact Real.log_injOn_pos
      (Set.mem_Ioi.mpr (div_pos historyScale₂.property historyScale₁.property))
      (Set.mem_Ioi.mpr zero_lt_one) (by simpa using hlog)
  exact (div_eq_one_iff_eq historyScale₁.property.ne').mp hratio |>.symm

/-- **Continuum clock degeneracy.**  At one frequency, the set of phase-clock values compatible
with the common intensity has cardinality continuum. -/
theorem cardinal_range_exponentialCollapseHistoryClock_eq_continuum
    {incomingFrequency x : ℝ} (hincoming : 0 < incomingFrequency) :
    #(Set.range
        (fun historyScale : Set.Ioi (0 : ℝ) =>
          exponentialCollapseHistoryClock incomingFrequency historyScale x)) =
      Cardinal.continuum := by
  rw [Cardinal.mk_range_eq _
    (exponentialCollapseHistoryClock_injective hincoming),
    Cardinal.mk_Ioi_real]

/-- Exact inverse map from one phase-slope datum to the affine history scale. -/
def exponentialCollapseHistoryScaleFromClock
    (incomingFrequency x clockValue : ℝ) : ℝ :=
  Real.exp (intrinsicHorizonGammaPhaseSlope x - clockValue) /
    incomingFrequency

/-- Exact inverse map from one phase-slope datum to the affine-invariant dimensionless history
coordinate. -/
def exponentialCollapseHistoryRatioFromClock
    (x clockValue : ℝ) : ℝ :=
  Real.exp (intrinsicHorizonGammaPhaseSlope x - clockValue)

/-- One exact phase-slope datum reconstructs the affine-invariant product
`incomingFrequency * historyScale`. -/
theorem exponentialCollapseHistoryRatioFromClock_reconstructs
    {incomingFrequency historyScale : ℝ}
    (hincoming : 0 < incomingFrequency)
    (hhistory : 0 < historyScale)
    (x : ℝ) :
    exponentialCollapseHistoryRatioFromClock x
        (exponentialCollapseHistoryClock incomingFrequency historyScale x) =
      exponentialCollapseHistoryRatio incomingFrequency historyScale := by
  unfold exponentialCollapseHistoryRatioFromClock exponentialCollapseHistoryClock
    horizonBogoliubovChannelPhaseSlope
  have hpositive :
      0 < exponentialCollapseHistoryRatio incomingFrequency historyScale := by
    exact mul_pos hincoming hhistory
  rw [show
      intrinsicHorizonGammaPhaseSlope x -
          (intrinsicHorizonGammaPhaseSlope x -
            Real.log
              (exponentialCollapseHistoryRatio incomingFrequency historyScale)) =
        Real.log
          (exponentialCollapseHistoryRatio incomingFrequency historyScale) by
      ring,
    Real.exp_log hpositive]

/-- **One-point history reconstruction.**  One exact phase-slope value recovers the positive
affine history scale, although the complete intensity is independent of that scale. -/
theorem exponentialCollapseHistoryScaleFromClock_reconstructs
    {incomingFrequency historyScale : ℝ}
    (hincoming : 0 < incomingFrequency)
    (hhistory : 0 < historyScale)
    (x : ℝ) :
    exponentialCollapseHistoryScaleFromClock incomingFrequency x
        (exponentialCollapseHistoryClock incomingFrequency historyScale x) =
      historyScale := by
  unfold exponentialCollapseHistoryScaleFromClock exponentialCollapseHistoryClock
    exponentialCollapseHistoryRatio horizonBogoliubovChannelPhaseSlope
  have hcancel :
      intrinsicHorizonGammaPhaseSlope x -
          (intrinsicHorizonGammaPhaseSlope x -
            Real.log (incomingFrequency * historyScale)) =
        Real.log (incomingFrequency * historyScale) := by
    ring
  rw [hcancel, Real.exp_log (mul_pos hincoming hhistory)]
  field_simp [hincoming.ne']

/-- The history-resolved phase clock is strictly increasing on every positive-frequency ray. -/
theorem strictMonoOn_exponentialCollapseHistoryClock
    (incomingFrequency historyScale : ℝ) :
    StrictMonoOn
      (exponentialCollapseHistoryClock incomingFrequency historyScale)
      (Set.Ici 0) := by
  exact strictMonoOn_horizonBogoliubovChannelPhaseSlope
    (exponentialCollapseHistoryRatio incomingFrequency historyScale)

/-- **Exact history-dependent one-turn law.**  A positive stationary frequency exists uniquely
exactly when the dimensionless product of incoming frequency and affine history scale exceeds
`exp(-EulerGamma)`. -/
theorem existsUnique_pos_exponentialCollapseHistoryClock_eq_zero_iff
    {incomingFrequency historyScale : ℝ}
    (hincoming : 0 < incomingFrequency)
    (hhistory : 0 < historyScale) :
    (∃! x : ℝ, 0 < x ∧
        exponentialCollapseHistoryClock incomingFrequency historyScale x = 0) ↔
      Real.exp (-Real.eulerMascheroniConstant) <
        incomingFrequency * historyScale := by
  exact existsUnique_pos_horizonBogoliubovChannelPhaseSlope_eq_zero_iff
    (mul_pos hincoming hhistory)

/-! ## Complete intensity atlas and exact algebraic state obstruction -/

/-- Global meromorphic realization of the affine history phase
`exp(-z * log(incomingFrequency * historyScale))`. -/
def exponentialCollapseHistoryGauge
    (incomingFrequency historyScale : ℝ) : meroField Set.univ :=
  physicalExponentialMero
    (-(Real.log
      (exponentialCollapseHistoryRatio incomingFrequency historyScale) : ℂ))

/-- Opposite-orientation history gauge. -/
def exponentialCollapseReflectedHistoryGauge
    (incomingFrequency historyScale : ℝ) : meroField Set.univ :=
  (exponentialCollapseHistoryGauge incomingFrequency historyScale)⁻¹

theorem exponentialCollapseHistoryGauge_ne_zero
    (incomingFrequency historyScale : ℝ) :
    exponentialCollapseHistoryGauge incomingFrequency historyScale ≠ 0 := by
  exact physicalExponentialMero_ne_zero _

theorem exponentialCollapseReflectedHistoryGauge_ne_zero
    (incomingFrequency historyScale : ℝ) :
    exponentialCollapseReflectedHistoryGauge
      incomingFrequency historyScale ≠ 0 := by
  exact inv_ne_zero
    (exponentialCollapseHistoryGauge_ne_zero incomingFrequency historyScale)

theorem differentialAlgebraicOver_exponentialCollapseHistoryGauge
    (incomingFrequency historyScale : ℝ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (exponentialCollapseHistoryGauge incomingFrequency historyScale) := by
  exact differentialAlgebraicOver_physicalExponentialMero _

theorem differentialAlgebraicOver_exponentialCollapseReflectedHistoryGauge
    (incomingFrequency historyScale : ℝ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (exponentialCollapseReflectedHistoryGauge
        incomingFrequency historyScale) := by
  exact HTGeometry.differentialAlgebraicOver_inv
    (differentialAlgebraicOver_exponentialCollapseHistoryGauge
      incomingFrequency historyScale)

/-- The complete meromorphic intensity channel is independent of the affine history scale. -/
theorem normalizedHorizonBogoliubovIntensityAtlas_historyGauge_eq
    (incomingFrequency historyScale : ℝ) :
    normalizedHorizonBogoliubovIntensityAtlas
        (fun _ : Unit =>
          exponentialCollapseHistoryGauge incomingFrequency historyScale)
        (fun _ : Unit =>
          exponentialCollapseReflectedHistoryGauge
            incomingFrequency historyScale) () =
      horizonBogoliubovGammaIntensityCoreMero := by
  rw [normalizedHorizonBogoliubovIntensityAtlas_eq]
  simp [exponentialCollapseReflectedHistoryGauge,
    exponentialCollapseHistoryGauge_ne_zero]

/-- **Arbitrary-family collapse-history separation.**  For every index type and every family of
affine history scales, all history gauges satisfy the complete thermal spectrum/clock separation
certificate. -/
theorem exponentialCollapseHistory_fieldSeparationUniversality
    {ι : Type*} (incomingFrequency historyScale : ι → ℝ) :
    HorizonThermalSpectrumClockSeparationCertificate
      (fun i =>
        exponentialCollapseHistoryGauge
          (incomingFrequency i) (historyScale i))
      (fun i =>
        exponentialCollapseReflectedHistoryGauge
          (incomingFrequency i) (historyScale i)) := by
  exact horizonThermalSpectrumClock_fieldSeparationUniversality _ _
    (fun i =>
      differentialAlgebraicOver_exponentialCollapseHistoryGauge
        (incomingFrequency i) (historyScale i))
    (fun i =>
      differentialAlgebraicOver_exponentialCollapseReflectedHistoryGauge
        (incomingFrequency i) (historyScale i))
    (fun i =>
      exponentialCollapseHistoryGauge_ne_zero
        (incomingFrequency i) (historyScale i))
    (fun i =>
      exponentialCollapseReflectedHistoryGauge_ne_zero
        (incomingFrequency i) (historyScale i))

/-- No history-resolved logarithmic phase current can be generated by a finite algebraic
differential state model over the complete, possibly infinite, intensity atlas. -/
theorem
    not_finiteAlgebraicStateObservable_exponentialCollapseHistoryClock_intensityField
    {ι : Type*} (incomingFrequency historyScale : ι → ℝ) (j : ι) :
    ¬ HTGeometry.FiniteAlgebraicStateObservable
      (differentialAdjoin (RatFunc ℂ)
        (Set.range
          (normalizedHorizonBogoliubovIntensityAtlas
            (fun i =>
              exponentialCollapseHistoryGauge
                (incomingFrequency i) (historyScale i))
            (fun i =>
              exponentialCollapseReflectedHistoryGauge
                (incomingFrequency i) (historyScale i)))))
      (normalizedHorizonBogoliubovWignerSmithAtlas
        (fun i =>
          exponentialCollapseHistoryGauge
            (incomingFrequency i) (historyScale i)) j) := by
  exact
    not_finiteAlgebraicStateObservable_normalizedHorizonBogoliubovWignerSmithAtlas_intensityField
      _ _
      (fun i =>
        differentialAlgebraicOver_exponentialCollapseHistoryGauge
          (incomingFrequency i) (historyScale i))
      (fun i =>
        differentialAlgebraicOver_exponentialCollapseReflectedHistoryGauge
          (incomingFrequency i) (historyScale i))
      (fun i =>
        exponentialCollapseHistoryGauge_ne_zero
          (incomingFrequency i) (historyScale i))
      j

/-- **Infinite history-clock state law.**  Every derivation-closed state field containing one
history-resolved logarithmic phase current has at least countably infinite transcendence degree
over the complete, possibly infinite, intensity atlas. -/
theorem
    aleph0_le_trdeg_exponentialCollapseHistoryClock_intensityField
    {ι : Type*} (incomingFrequency historyScale : ι → ℝ) (j : ι)
    (S : IntermediateField
      (differentialAdjoin (RatFunc ℂ)
        (Set.range
          (normalizedHorizonBogoliubovIntensityAtlas
            (fun i =>
              exponentialCollapseHistoryGauge
                (incomingFrequency i) (historyScale i))
            (fun i =>
              exponentialCollapseReflectedHistoryGauge
                (incomingFrequency i) (historyScale i)))))
      (meroField Set.univ))
    (hSclosed : DerivationClosed S)
    (hclock :
      normalizedHorizonBogoliubovWignerSmithAtlas
        (fun i =>
          exponentialCollapseHistoryGauge
            (incomingFrequency i) (historyScale i)) j ∈ S) :
    Cardinal.aleph0 ≤
      Algebra.trdeg
        (differentialAdjoin (RatFunc ℂ)
          (Set.range
            (normalizedHorizonBogoliubovIntensityAtlas
              (fun i =>
                exponentialCollapseHistoryGauge
                  (incomingFrequency i) (historyScale i))
              (fun i =>
                exponentialCollapseReflectedHistoryGauge
                  (incomingFrequency i) (historyScale i)))))
        S := by
  exact
    aleph0_le_trdeg_normalizedHorizonBogoliubovWignerSmithAtlas_intensityField
      _ _
      (fun i =>
        differentialAlgebraicOver_exponentialCollapseHistoryGauge
          (incomingFrequency i) (historyScale i))
      (fun i =>
        differentialAlgebraicOver_exponentialCollapseReflectedHistoryGauge
          (incomingFrequency i) (historyScale i))
      (fun i =>
        exponentialCollapseHistoryGauge_ne_zero
          (incomingFrequency i) (historyScale i))
      j S hSclosed hclock

end

end GaloisForLFunctions
