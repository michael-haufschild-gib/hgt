import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBackreactionGeneratorEndpoint

/-!
# Theta-cusp Hawking backreaction passivity endpoint

The conformal-anomaly endpoint constructs a two-ended rapidity response at every theta/Xi
resonance.  The compact-source endpoint independently constructs a divisor eigenvector.  Here the
two objects are identified exactly: after full-density dressing and quantile transport, the
physical response is `(i alpha)⁻¹` times the compact divisor mode.

Consequently its incoming-minus-outgoing port dissipation is

`2 * thetaSource.mass * Im(alpha) * physicalEnergy(alpha)`,

with strictly positive physical energy.  Source passivity on every two-ended anomaly resonance
therefore forces `Im(alpha) >= 0`.  The functional-equation partner at `-alpha` forces the opposite
inequality.  Thus RH is equivalent to passivity of every bifurcate Hawking-backreaction resonance.

This does not assume that a perfect mirror is passive.  Moving-mirror radiation reaction has
runaway solutions in that idealization.  The remaining producer is a causal, high-frequency
transparent mirror/material dilation whose physical impedance proves the restricted port
passivity formalized here.
-/

open Complex Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmThetaSource HedenmalmHilbertSchmidt
  HedenmalmPrimeTranslation

private abbrev ThetaHawkingBackreactionH := Lp ℂ 2 unitIntervalMeasure

/-- A literal two-ended resonance of the theta conformal-anomaly backreaction equation. -/
def ThetaCuspHawkingBackreactionResonantMode :=
  {alpha : ℂ // ThetaCuspHawkingBackreactionResonance alpha}

theorem thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) : XiC r.1 = 0 :=
  (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance r.1).mpr r.2

theorem thetaCuspHawkingBackreactionResonantMode_ne_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) : r.1 ≠ 0 := by
  intro hr
  apply XiC_zero_ne
  simpa only [hr] using thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r

theorem thetaCuspHawkingBackreactionResonantMode_mem_sourceStrip
    (r : ThetaCuspHawkingBackreactionResonantMode) : |r.1.im| < 1 :=
  abs_im_lt_one_of_XiC_eq_zero
    (thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r)

theorem thetaCuspHawkingBackreactionResonantMode_source_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) : xiC thetaSource r.1 = 0 := by
  rw [xiC_thetaSource_all,
    thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero]

/-- Compact divisor mode at a physical anomaly resonance. -/
def thetaCuspHawkingBackreactionDivisorMode
    (r : ThetaCuspHawkingBackreactionResonantMode) : ThetaHawkingBackreactionH :=
  thetaDivisorEigenvector r.1
    (thetaCuspHawkingBackreactionResonantMode_mem_sourceStrip r)
    (thetaCuspHawkingBackreactionResonantMode_source_zero r)

/-- Closed physical response, normalized to the literal density-dressed rapidity solution. -/
def thetaCuspHawkingBackreactionClosedState
    (r : ThetaCuspHawkingBackreactionResonantMode) : ThetaHawkingBackreactionH :=
  (Complex.I * r.1)⁻¹ • thetaCuspHawkingBackreactionDivisorMode r

theorem thetaCuspHawkingBackreactionClosedState_ne_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionClosedState r ≠ 0 := by
  apply smul_ne_zero
  · exact inv_ne_zero (mul_ne_zero Complex.I_ne_zero
      (thetaCuspHawkingBackreactionResonantMode_ne_zero r))
  · exact thetaDivisorEigenvector_ne_zero r.1
      (thetaCuspHawkingBackreactionResonantMode_mem_sourceStrip r)
      (thetaCuspHawkingBackreactionResonantMode_source_zero r)

/-- **[PROVED] Physical/compact identification.**  Pulling the normalized compact divisor state
back through the theta quantile gives the literal full-density-dressed anomaly response. -/
theorem thetaCuspHawkingBackreactionClosedState_source_representation
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    let w : SourceSpace thetaSource :=
      (quantileUnitary thetaSource).symm
        (thetaCuspHawkingBackreactionClosedState r)
    (fun x => w x) =ᵐ[(volume : Measure ℝ)]
      thetaCuspHawkingDensityDress
        (thetaCuspHawkingBackreactionRapidityMode r.1) := by
  rw [thetaCuspHawkingDensityDress_rapidityMode]
  let v : SourceSpace thetaSource := thetaDivisorSourceVector r.1
    (thetaCuspHawkingBackreactionResonantMode_mem_sourceStrip r)
    (thetaCuspHawkingBackreactionResonantMode_source_zero r)
  let c : ℂ := (Complex.I * r.1)⁻¹
  have hstate :
      (quantileUnitary thetaSource).symm
          (thetaCuspHawkingBackreactionClosedState r) = c • v := by
    rw [thetaCuspHawkingBackreactionClosedState, map_smul,
      thetaCuspHawkingBackreactionDivisorMode, thetaDivisorEigenvector,
      (quantileUnitary thetaSource).symm_apply_apply]
  rw [hstate]
  have hv : (v : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      sourceModeF thetaSource r.1 :=
    thetaDivisorSourceVector_ae r.1
      (thetaCuspHawkingBackreactionResonantMode_mem_sourceStrip r)
      (thetaCuspHawkingBackreactionResonantMode_source_zero r)
  have hcWeighted := Lp.coeFn_smul c v
  have hc : ((c • v : SourceSpace thetaSource) : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      fun x => c * v x :=
    (withDensity_realDensity_ae_eq
      (measurable_sourceWeight thetaSource) (sourceWeight_pos thetaSource)).mp hcWeighted
  have hden : Complex.I * r.1 ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero
      (thetaCuspHawkingBackreactionResonantMode_ne_zero r)
  have hneg : -r.1 = (Complex.I * r.1) * Complex.I := by
    calc
      -r.1 = (Complex.I * Complex.I) * r.1 := by rw [Complex.I_mul_I]; ring
      _ = (Complex.I * r.1) * Complex.I := by ring
  have hscalar : c * (-r.1) = Complex.I := by
    rw [hneg, ← mul_assoc]
    dsimp only [c]
    rw [inv_mul_cancel₀ hden, one_mul]
  filter_upwards [hc, hv] with x hcx hvx
  rw [hcx, hvx, sourceModeF, thetaTwoEndedSourceSolution]
  rw [← mul_assoc, hscalar]

/-- The same physical response is an eigenmode of the fixed theta Green operator. -/
theorem thetaCompactSourceInverse_thetaCuspHawkingBackreactionClosedState
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCompactSourceInverse (thetaCuspHawkingBackreactionClosedState r) =
      (-r.1⁻¹) • thetaCuspHawkingBackreactionClosedState r := by
  rw [thetaCuspHawkingBackreactionClosedState, map_smul,
    thetaCuspHawkingBackreactionDivisorMode,
    thetaCompactSourceInverse_eigen]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- Positive metric energy of the normalized physical response. -/
def thetaCuspHawkingBackreactionPhysicalEnergy
    (r : ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  Complex.normSq ((Complex.I * r.1)⁻¹) * thetaRootEnergy r.1

theorem thetaCuspHawkingBackreactionPhysicalEnergy_pos
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    0 < thetaCuspHawkingBackreactionPhysicalEnergy r := by
  apply mul_pos
  · exact Complex.normSq_pos.mpr
      (inv_ne_zero (mul_ne_zero Complex.I_ne_zero
        (thetaCuspHawkingBackreactionResonantMode_ne_zero r)))
  · exact thetaRootEnergy_pos
      (thetaCuspHawkingBackreactionResonantMode_mem_sourceStrip r)
      (thetaCuspHawkingBackreactionResonantMode_source_zero r)

/-- Incoming-minus-outgoing physical boundary power. -/
def thetaCuspHawkingBackreactionPortDissipation
    (r : ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  (inner ℂ
    (pinnedBoundaryCLM (thetaCuspHawkingBackreactionClosedState r))
    (thetaCuspHawkingBackreactionClosedState r) : ℂ).re

/-- Port dissipation is exactly incoming intensity minus partner intensity. -/
theorem thetaCuspHawkingBackreactionPortDissipation_eq_intensityDifference
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionPortDissipation r =
      ‖pinnedInAmplitude (thetaCuspHawkingBackreactionClosedState r)‖ ^ 2 -
        ‖pinnedOutAmplitude (thetaCuspHawkingBackreactionClosedState r)‖ ^ 2 := by
  rw [thetaCuspHawkingBackreactionPortDissipation,
    inner_pinnedBoundaryCLM_eq_amplitudes]
  norm_cast

/-- **[PROVED] Hawking anomaly dissipation law.**  Imaginary resonance frequency is exactly
physical port dissipation divided by a strictly positive theta-source energy. -/
theorem thetaCuspHawkingBackreactionPortDissipation_eq
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionPortDissipation r =
      2 * thetaSource.mass * r.1.im *
        thetaCuspHawkingBackreactionPhysicalEnergy r := by
  rw [thetaCuspHawkingBackreactionPortDissipation,
    thetaCuspHawkingBackreactionClosedState, map_smul,
    inner_smul_left, inner_smul_right,
    thetaCuspHawkingBackreactionDivisorMode,
    inner_pinnedBoundaryCLM_thetaDivisorEigenvector]
  let c : ℂ := (Complex.I * r.1)⁻¹
  change (star c * (c *
      ((thetaSource.mass : ℂ) *
        Complex.ofReal (2 * r.1.im * thetaRootEnergy r.1)))).re = _
  rw [← mul_assoc, show star c = (starRingEnd ℂ) c by rfl,
    ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, thetaCuspHawkingBackreactionPhysicalEnergy]
  ring

/-- A resonance is passive exactly when its imaginary frequency is nonnegative. -/
theorem thetaCuspHawkingBackreactionPortDissipation_nonneg_iff
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    0 ≤ thetaCuspHawkingBackreactionPortDissipation r ↔ 0 ≤ r.1.im := by
  rw [thetaCuspHawkingBackreactionPortDissipation_eq]
  have hfactor : 0 <
      2 * thetaSource.mass * thetaCuspHawkingBackreactionPhysicalEnergy r :=
    mul_pos (mul_pos (by norm_num) thetaSource.mass_pos)
      (thetaCuspHawkingBackreactionPhysicalEnergy_pos r)
  have hrewrite :
      2 * thetaSource.mass * r.1.im * thetaCuspHawkingBackreactionPhysicalEnergy r =
        (2 * thetaSource.mass * thetaCuspHawkingBackreactionPhysicalEnergy r) * r.1.im := by
    ring
  rw [hrewrite]
  exact mul_nonneg_iff_of_pos_left hfactor

/-- Port passivity is the literal no-amplification inequality. -/
theorem thetaCuspHawkingBackreactionPortDissipation_nonneg_iff_noAmplification
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    0 ≤ thetaCuspHawkingBackreactionPortDissipation r ↔
      ‖pinnedOutAmplitude (thetaCuspHawkingBackreactionClosedState r)‖ ≤
        ‖pinnedInAmplitude (thetaCuspHawkingBackreactionClosedState r)‖ := by
  rw [thetaCuspHawkingBackreactionPortDissipation_eq_intensityDifference]
  constructor <;> intro h
  · nlinarith [norm_nonneg
      (pinnedInAmplitude (thetaCuspHawkingBackreactionClosedState r)),
      norm_nonneg
        (pinnedOutAmplitude (thetaCuspHawkingBackreactionClosedState r))]
  · nlinarith [norm_nonneg
      (pinnedInAmplitude (thetaCuspHawkingBackreactionClosedState r)),
      norm_nonneg
        (pinnedOutAmplitude (thetaCuspHawkingBackreactionClosedState r))]

/-- Functional-equation partner of a two-ended backreaction resonance. -/
def thetaCuspHawkingBackreactionReflectedResonantMode
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    ThetaCuspHawkingBackreactionResonantMode := by
  refine ⟨-r.1, ?_⟩
  apply (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance (-r.1)).mp
  rw [XiC_even, thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero]

theorem thetaCuspHawkingBackreactionReflectedResonantMode_im
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    (thetaCuspHawkingBackreactionReflectedResonantMode r).1.im = -r.1.im := by
  rfl

/-- Restricted physical passivity: no two-ended anomaly resonance emits more partner power than
it receives through the theta boundary ports. -/
def ThetaCuspHawkingBackreactionResonancePassive : Prop :=
  ∀ r : ThetaCuspHawkingBackreactionResonantMode,
    0 ≤ thetaCuspHawkingBackreactionPortDissipation r

/-- **[BRIDGE] Hawking passivity endpoint.**  RH is exactly passivity of every literal two-ended
theta anomaly response.  The hard producer remains derivation of this passivity from a causal,
high-frequency-transparent mirror/material dilation. -/
theorem riemannHypothesis_iff_thetaCuspHawkingBackreactionResonancePassive :
    RiemannHypothesis ↔ ThetaCuspHawkingBackreactionResonancePassive := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal r
    apply (thetaCuspHawkingBackreactionPortDissipation_nonneg_iff r).mpr
    rw [hreal r.1
      (thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r)]
  · intro hpass alpha hXi
    let r : ThetaCuspHawkingBackreactionResonantMode :=
      ⟨alpha,
        (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance alpha).mp hXi⟩
    have hright : 0 ≤ r.1.im :=
      (thetaCuspHawkingBackreactionPortDissipation_nonneg_iff r).mp (hpass r)
    have hleft :
        0 ≤ (thetaCuspHawkingBackreactionReflectedResonantMode r).1.im :=
      (thetaCuspHawkingBackreactionPortDissipation_nonneg_iff
        (thetaCuspHawkingBackreactionReflectedResonantMode r)).mp
          (hpass (thetaCuspHawkingBackreactionReflectedResonantMode r))
    rw [thetaCuspHawkingBackreactionReflectedResonantMode_im] at hleft
    change alpha.im = 0
    dsimp only [r] at hright hleft
    linarith

end RHTower
