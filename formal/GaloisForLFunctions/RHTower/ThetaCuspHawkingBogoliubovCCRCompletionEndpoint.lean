import GaloisForLFunctions.RHTower.ThetaCuspHawkingBogoliubovBornEndpoint

/-!
# Theta-cusp Hawking Born kernel and its exact pointwise CCR completion

The moving-mirror Born coefficient is not merely a scalar spectrum.  Before diagonal frequency
balancing, its entire continuation is a symmetric two-frequency kernel.  This is exactly the
exchange symmetry required of the pair-creation block in the tangent space of a bosonic
Bogoliubov transformation.

The second half gives the kernel's strongest unconditional CCR consequence.  At every continued
frequency and every real coupling, its balanced pair amplitude has a canonical minimal two-mode
squeeze completion.  The gain absorbs the pair number and the anomalous covariance saturates the
pure Gaussian relation.  Therefore even exact pointwise CCR and covariance purity coexist with an
arbitrary dark-frequency location.  A zero becomes an unsqueezed vacuum fibre; CCR alone does not
force that fibre onto the physical real-frequency sheet.  The missing producer must couple
different frequencies through a source-causal analytic colligation, not complete each frequency
independently.
-/

open Complex Real
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Symmetric pair-creation tangent -/

/-- Entire two-frequency continuation of the theta-cusp moving-mirror Born numerator. -/
def thetaCuspHawkingBornPairKernel (outgoing incoming : ℂ) : ℂ :=
  2 * Complex.I * outgoing * incoming * XiC (outgoing + incoming)

/-- On real frequencies, the continued pair kernel is the literal moving-mirror first
variation. -/
theorem thetaCuspHawkingBornPairKernel_real_eq_raw
    (outgoing incoming : ℝ) :
    thetaCuspHawkingBornPairKernel (outgoing : ℂ) (incoming : ℂ) =
      thetaCuspMovingMirrorBornRaw outgoing incoming := by
  rw [thetaCuspMovingMirrorBornRaw_eq_XiC]
  simp only [thetaCuspHawkingBornPairKernel, ofReal_add]

/-- Bosonic exchange law: the theta pair-creation tangent is symmetric in its two modes. -/
theorem thetaCuspHawkingBornPairKernel_comm
    (outgoing incoming : ℂ) :
    thetaCuspHawkingBornPairKernel outgoing incoming =
      thetaCuspHawkingBornPairKernel incoming outgoing := by
  rw [thetaCuspHawkingBornPairKernel, thetaCuspHawkingBornPairKernel, add_comm]
  ring

/-- Zero outgoing frequency is a kinematic dark edge. -/
theorem thetaCuspHawkingBornPairKernel_zero_left (incoming : ℂ) :
    thetaCuspHawkingBornPairKernel 0 incoming = 0 := by
  simp [thetaCuspHawkingBornPairKernel]

/-- Zero incoming frequency is a kinematic dark edge. -/
theorem thetaCuspHawkingBornPairKernel_zero_right (outgoing : ℂ) :
    thetaCuspHawkingBornPairKernel outgoing 0 = 0 := by
  simp [thetaCuspHawkingBornPairKernel]

/-! ## Exact pointwise two-mode squeeze completion -/

/-- Pair-production block at coupling `lambda` on one balanced continuation fibre. -/
def thetaCuspHawkingSqueezeBeta (lambda : ℝ) (z : ℂ) : ℂ :=
  (lambda : ℂ) * thetaCuspBalancedHawkingBornAmplitude z

/-- Produced particle number of the balanced pair block. -/
def thetaCuspHawkingSqueezeNumber (lambda : ℝ) (z : ℂ) : ℝ :=
  ‖thetaCuspHawkingSqueezeBeta lambda z‖ ^ 2

/-- Minimal positive gain completing the pair block to a two-mode bosonic CCR fibre. -/
def thetaCuspHawkingSqueezeGain (lambda : ℝ) (z : ℂ) : ℝ :=
  Real.sqrt (1 + thetaCuspHawkingSqueezeNumber lambda z)

/-- Scalar signed-norm law for a two-mode bosonic Bogoliubov fibre. -/
def IsTwoModeBosonicCCR (gain : ℝ) (pair : ℂ) : Prop :=
  gain ^ 2 - ‖pair‖ ^ 2 = 1

/-- The produced number is nonnegative. -/
theorem thetaCuspHawkingSqueezeNumber_nonneg (lambda : ℝ) (z : ℂ) :
    0 ≤ thetaCuspHawkingSqueezeNumber lambda z := by
  exact sq_nonneg _

/-- Exact squared gain law. -/
theorem thetaCuspHawkingSqueezeGain_sq (lambda : ℝ) (z : ℂ) :
    thetaCuspHawkingSqueezeGain lambda z ^ 2 =
      1 + thetaCuspHawkingSqueezeNumber lambda z := by
  rw [thetaCuspHawkingSqueezeGain, Real.sq_sqrt]
  exact add_nonneg zero_le_one (thetaCuspHawkingSqueezeNumber_nonneg lambda z)

/-- Minimal gain is positive. -/
theorem thetaCuspHawkingSqueezeGain_pos (lambda : ℝ) (z : ℂ) :
    0 < thetaCuspHawkingSqueezeGain lambda z := by
  rw [thetaCuspHawkingSqueezeGain]
  exact Real.sqrt_pos.2 <| lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right (thetaCuspHawkingSqueezeNumber_nonneg lambda z))

/-- **Exact pointwise CCR completion.**  Every continued theta Born fibre, on or off the physical
sheet, admits the minimal two-mode bosonic squeeze completion. -/
theorem thetaCuspHawkingSqueeze_isTwoModeBosonicCCR
    (lambda : ℝ) (z : ℂ) :
    IsTwoModeBosonicCCR (thetaCuspHawkingSqueezeGain lambda z)
      (thetaCuspHawkingSqueezeBeta lambda z) := by
  rw [IsTwoModeBosonicCCR, thetaCuspHawkingSqueezeGain_sq,
    thetaCuspHawkingSqueezeNumber]
  ring

/-- Positive-norm Nambu output of the completed two-mode fibre. -/
def thetaCuspHawkingSqueezePositiveOutput
    (lambda : ℝ) (z x y : ℂ) : ℂ :=
  (thetaCuspHawkingSqueezeGain lambda z : ℂ) * x +
    thetaCuspHawkingSqueezeBeta lambda z * y

/-- Partner Nambu output of the completed two-mode fibre. -/
def thetaCuspHawkingSqueezePartnerOutput
    (lambda : ℝ) (z x y : ℂ) : ℂ :=
  conj (thetaCuspHawkingSqueezeBeta lambda z) * x +
    (thetaCuspHawkingSqueezeGain lambda z : ℂ) * y

/-- **Full two-mode CCR law.**  The theta squeeze completion preserves the Nambu signed Hermitian
form, not only its basis-vector normalization. -/
theorem thetaCuspHawkingSqueeze_preserves_signedHermitian
    (lambda : ℝ) (z x y : ℂ) :
    conj (thetaCuspHawkingSqueezePositiveOutput lambda z x y) *
          thetaCuspHawkingSqueezePositiveOutput lambda z x y -
        conj (thetaCuspHawkingSqueezePartnerOutput lambda z x y) *
          thetaCuspHawkingSqueezePartnerOutput lambda z x y =
      conj x * x - conj y * y := by
  let a : ℝ := thetaCuspHawkingSqueezeGain lambda z
  let b : ℂ := thetaCuspHawkingSqueezeBeta lambda z
  have hgain := thetaCuspHawkingSqueezeGain_sq lambda z
  rw [thetaCuspHawkingSqueezeNumber] at hgain
  have hgainC := congrArg (fun r : ℝ => (r : ℂ)) hgain
  push_cast at hgainC
  change (a : ℂ) ^ 2 = 1 + (‖b‖ : ℂ) ^ 2 at hgainC
  have hnormC : (‖b‖ : ℂ) ^ 2 = conj b * b := by
    rw [show (‖b‖ : ℂ) ^ 2 = ((‖b‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [hnormC] at hgainC
  change conj ((a : ℂ) * x + b * y) * ((a : ℂ) * x + b * y) -
      conj (conj b * x + (a : ℂ) * y) *
        (conj b * x + (a : ℂ) * y) = conj x * x - conj y * y
  simp only [map_add, map_mul, conj_ofReal, conj_conj]
  linear_combination (conj x * x - conj y * y) * hgainC

/-- Coupling reversal fixes gain and reverses the pair block. -/
theorem thetaCuspHawkingSqueeze_neg_coupling (lambda : ℝ) (z : ℂ) :
    thetaCuspHawkingSqueezeGain (-lambda) z =
        thetaCuspHawkingSqueezeGain lambda z ∧
      thetaCuspHawkingSqueezeBeta (-lambda) z =
        -thetaCuspHawkingSqueezeBeta lambda z := by
  have hnumber : thetaCuspHawkingSqueezeNumber (-lambda) z =
      thetaCuspHawkingSqueezeNumber lambda z := by
    rw [thetaCuspHawkingSqueezeNumber, thetaCuspHawkingSqueezeNumber,
      thetaCuspHawkingSqueezeBeta, thetaCuspHawkingSqueezeBeta,
      show ((-lambda : ℝ) : ℂ) = -(lambda : ℂ) by norm_num, neg_mul, norm_neg]
  constructor
  · rw [thetaCuspHawkingSqueezeGain, thetaCuspHawkingSqueezeGain, hnumber]
  · simp [thetaCuspHawkingSqueezeBeta]

/-- Zero coupling is the identity Bogoliubov fibre. -/
theorem thetaCuspHawkingSqueeze_zero_coupling (z : ℂ) :
    thetaCuspHawkingSqueezeGain 0 z = 1 ∧
      thetaCuspHawkingSqueezeBeta 0 z = 0 := by
  simp [thetaCuspHawkingSqueezeGain, thetaCuspHawkingSqueezeNumber,
    thetaCuspHawkingSqueezeBeta]

/-- A Born-dark frequency is an unsqueezed vacuum fibre at every coupling. -/
theorem thetaCuspHawkingSqueeze_eq_identity_of_dark
    {z : ℂ} (hz : thetaCuspBalancedHawkingBornAmplitude z = 0)
    (lambda : ℝ) :
    thetaCuspHawkingSqueezeGain lambda z = 1 ∧
      thetaCuspHawkingSqueezeBeta lambda z = 0 := by
  simp [thetaCuspHawkingSqueezeGain, thetaCuspHawkingSqueezeNumber,
    thetaCuspHawkingSqueezeBeta, hz]

/-- At unit coupling, the minimal CCR fibre is the identity exactly at a Born-dark frequency. -/
theorem thetaCuspHawkingSqueezeGain_one_iff_dark (z : ℂ) :
    thetaCuspHawkingSqueezeGain 1 z = 1 ↔
      thetaCuspBalancedHawkingBornAmplitude z = 0 := by
  constructor
  · intro hgain
    have hsq := thetaCuspHawkingSqueezeGain_sq 1 z
    rw [hgain] at hsq
    have hnumber : thetaCuspHawkingSqueezeNumber 1 z = 0 := by
      nlinarith
    rw [thetaCuspHawkingSqueezeNumber, thetaCuspHawkingSqueezeBeta] at hnumber
    simp only [ofReal_one, one_mul] at hnumber
    have hnorm : ‖thetaCuspBalancedHawkingBornAmplitude z‖ = 0 := by
      nlinarith [norm_nonneg (thetaCuspBalancedHawkingBornAmplitude z)]
    exact norm_eq_zero.mp hnorm
  · intro hz
    exact (thetaCuspHawkingSqueeze_eq_identity_of_dark hz 1).1

/-- Pure two-mode anomalous covariance of the minimal squeeze fibre. -/
def thetaCuspHawkingSqueezeAnomalousCovariance (lambda : ℝ) (z : ℂ) : ℂ :=
  (thetaCuspHawkingSqueezeGain lambda z : ℂ) *
    thetaCuspHawkingSqueezeBeta lambda z

/-- **Pure Gaussian saturation.**  The anomalous pair covariance has the exact square
`N(N+1)` for every continued frequency. -/
theorem norm_thetaCuspHawkingSqueezeAnomalousCovariance_sq
    (lambda : ℝ) (z : ℂ) :
    ‖thetaCuspHawkingSqueezeAnomalousCovariance lambda z‖ ^ 2 =
      thetaCuspHawkingSqueezeNumber lambda z *
        (thetaCuspHawkingSqueezeNumber lambda z + 1) := by
  rw [thetaCuspHawkingSqueezeAnomalousCovariance, norm_mul,
    norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaCuspHawkingSqueezeGain_pos lambda z), mul_pow,
    thetaCuspHawkingSqueezeGain_sq, thetaCuspHawkingSqueezeNumber]
  ring

/-- **Vacuum-fibre endpoint.**  RH is exactly physical-sheet confinement of identity fibres of
the canonical pointwise CCR completion.  Since the completion itself exists unconditionally at
every complex frequency, this criterion isolates the additional analytic/causal producer still
needed by the Hawking route. -/
theorem riemannHypothesis_iff_thetaCuspHawkingCCRIdentityFibresPhysical :
    RiemannHypothesis ↔
      ∀ z : ℂ, thetaCuspHawkingSqueezeGain 1 z = 1 → z.im = 0 := by
  rw [riemannHypothesis_iff_thetaCuspHawkingBornDarkFrequenciesPhysical]
  constructor
  · intro h z hgain
    exact h z ((thetaCuspHawkingSqueezeGain_one_iff_dark z).mp hgain)
  · intro h z hdark
    exact h z ((thetaCuspHawkingSqueezeGain_one_iff_dark z).mpr hdark)

end RHTower
