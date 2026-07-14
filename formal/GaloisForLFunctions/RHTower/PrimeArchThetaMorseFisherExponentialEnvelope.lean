import GaloisForLFunctions.RHTower.PrimeArchThetaQuadraticVirialMorseReduction

/-!
# Exponentially sharpened Morse--Fisher envelope

The endpoint estimate for the Fisher residual discards the exact decay of the Morse quotient.
For the first theta atom that quotient is bounded by its endpoint excess times `exp (-2x)`.
The global quadratic Taylor majorant for this exponential gives a polynomial-moment upper value
that is strictly sharper than the endpoint value on the source-dominant region.

This file proves the analytic estimate and its integral transport.  It does not assert the final
finite numerical moment certificate.
-/

open Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The endpoint excess in the first-atom Morse quotient. -/
def thetaCuspFirstAtomMorseFisherDecayFactor : ℝ :=
  (3 / 2 : ℝ) / (Real.pi - 3 / 2)

/-- The exact decaying envelope extracted from the first-atom Morse quotient. -/
def thetaCuspFirstAtomMorseFisherExponentialEnvelope (x : ℝ) : ℝ :=
  1 + thetaCuspFirstAtomMorseFisherDecayFactor * Real.exp (-2 * x)

/-- The quadratic upper Taylor section used after the exact exponential decay extraction. -/
def thetaCuspFirstAtomMorseFisherQuadraticEnvelope (x : ℝ) : ℝ :=
  1 + thetaCuspFirstAtomMorseFisherDecayFactor * (1 - 2 * x + 2 * x ^ 2)

/-- Global second-order upper Taylor bound for a negative exponential. -/
theorem exp_neg_le_quadratic {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  have hsum := Real.sum_le_exp_of_nonneg hu 3
  have hpoly : 1 + u + u ^ 2 / 2 ≤ Real.exp u := by
    norm_num [Finset.sum_range_succ] at hsum ⊢
    nlinarith
  have hden : 0 < 1 + u + u ^ 2 / 2 := by
    nlinarith [sq_nonneg u]
  have hinv : (Real.exp u)⁻¹ ≤ (1 + u + u ^ 2 / 2)⁻¹ :=
    inv_anti₀ hden hpoly
  rw [← Real.exp_neg] at hinv
  calc
    Real.exp (-u) ≤ (1 + u + u ^ 2 / 2)⁻¹ := hinv
    _ ≤ 1 - u + u ^ 2 / 2 := by
      rw [inv_le_iff_one_le_mul₀ hden]
      nlinarith [sq_nonneg (u ^ 2)]

/-- The first Morse weight retains the full `exp (2x)` growth of its endpoint gap. -/
theorem thetaCuspFirstAtom_morseWeight_exponential_floor
    {x : ℝ} (hx : 0 ≤ x) :
    (Real.pi - 3 / 2) * Real.exp (2 * x) ≤
      thetaCuspMorseScale 1 x - 3 / 2 := by
  have hexp : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  have heq : thetaCuspMorseScale 1 x = Real.pi * Real.exp (2 * x) := by
    rw [thetaCuspMorseScale]
    norm_num
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  nlinarith

/-- Exact source-specific decay of the Fisher quotient away from the half-line endpoint. -/
theorem thetaCuspFirstAtom_morseScale_div_weight_le_exponential
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x ≤
      1 + thetaCuspFirstAtomMorseFisherDecayFactor * Real.exp (-2 * x) := by
  let t := thetaCuspMorseScale 1 x
  let a := Real.pi - 3 / 2
  let e := Real.exp (2 * x)
  have ha : 0 < a := by
    dsimp [a]
    nlinarith [Real.pi_gt_three]
  have he : 0 < e := by
    dsimp [e]
    positivity
  have hfloor : a * e ≤ t - 3 / 2 := by
    simpa only [a, e, t] using
      thetaCuspFirstAtom_morseWeight_exponential_floor hx
  have hq : 0 < t - 3 / 2 := lt_of_lt_of_le (mul_pos ha he) hfloor
  have hfrac : (3 / 2 : ℝ) / (t - 3 / 2) ≤ (3 / 2 : ℝ) / (a * e) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos ha he) hfloor
  have hexpneg : Real.exp (-2 * x) = e⁻¹ := by
    dsimp [e]
    rw [← Real.exp_neg]
    congr 1
    ring
  have hrewrite : (3 / 2 : ℝ) / (a * e) =
      ((3 / 2 : ℝ) / a) * Real.exp (-2 * x) := by
    rw [hexpneg]
    field_simp
  rw [thetaCuspBornWittenWeight_eq]
  dsimp [t] at hq hfrac ⊢
  rw [show thetaCuspMorseScale 1 x /
        (thetaCuspMorseScale 1 x - 3 / 2) =
      1 + (3 / 2 : ℝ) / (thetaCuspMorseScale 1 x - 3 / 2) by
    conv_lhs =>
      congr
      · rw [show thetaCuspMorseScale 1 x =
          (thetaCuspMorseScale 1 x - 3 / 2) + 3 / 2 by ring]
    rw [add_div, div_self hq.ne']]
  rw [hrewrite] at hfrac
  simpa only [thetaCuspFirstAtomMorseFisherDecayFactor, a, add_comm] using
    add_le_add_left hfrac 1

theorem thetaCuspFirstAtomMorseFisherDecayFactor_pos :
    0 < thetaCuspFirstAtomMorseFisherDecayFactor := by
  rw [thetaCuspFirstAtomMorseFisherDecayFactor]
  exact div_pos (by norm_num) (by nlinarith [Real.pi_gt_three])

theorem thetaCuspFirstAtomMorseFisherEndpointFactor_eq_one_add_decayFactor :
    thetaCuspFirstAtomMorseFisherEndpointFactor =
      1 + thetaCuspFirstAtomMorseFisherDecayFactor := by
  rw [thetaCuspFirstAtomMorseFisherEndpointFactor,
    thetaCuspFirstAtomMorseFisherDecayFactor]
  have hpi : Real.pi - 3 / 2 ≠ 0 := by
    nlinarith [Real.pi_gt_three]
  conv_lhs =>
    congr
    · rw [show Real.pi = (Real.pi - 3 / 2) + 3 / 2 by ring]
  rw [add_div, div_self hpi]

theorem thetaCuspFirstAtomMorseFisherExponentialEnvelope_nonneg (x : ℝ) :
    0 ≤ thetaCuspFirstAtomMorseFisherExponentialEnvelope x := by
  unfold thetaCuspFirstAtomMorseFisherExponentialEnvelope
  exact add_nonneg zero_le_one
    (mul_nonneg thetaCuspFirstAtomMorseFisherDecayFactor_pos.le
      (Real.exp_pos _).le)

theorem thetaCuspFirstAtomMorseFisherExponentialEnvelope_le_endpoint
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFirstAtomMorseFisherExponentialEnvelope x ≤
      thetaCuspFirstAtomMorseFisherEndpointFactor := by
  have hexp : Real.exp (-2 * x) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -2 * x ≤ 0)
  have hmul := mul_le_mul_of_nonneg_left hexp
    thetaCuspFirstAtomMorseFisherDecayFactor_pos.le
  rw [thetaCuspFirstAtomMorseFisherEndpointFactor_eq_one_add_decayFactor]
  unfold thetaCuspFirstAtomMorseFisherExponentialEnvelope
  linarith

theorem thetaCuspFirstAtomMorseFisherExponentialEnvelope_lt_endpoint
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstAtomMorseFisherExponentialEnvelope x <
      thetaCuspFirstAtomMorseFisherEndpointFactor := by
  have hexp : Real.exp (-2 * x) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by linarith : -2 * x < 0)
  have hmul := mul_lt_mul_of_pos_left hexp
    thetaCuspFirstAtomMorseFisherDecayFactor_pos
  rw [thetaCuspFirstAtomMorseFisherEndpointFactor_eq_one_add_decayFactor]
  unfold thetaCuspFirstAtomMorseFisherExponentialEnvelope
  linarith

/-- Polynomial form of the exponentially sharpened quotient estimate. -/
theorem thetaCuspFirstAtom_morseScale_div_weight_le_quadratic
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x ≤
      thetaCuspFirstAtomMorseFisherQuadraticEnvelope x := by
  have hdecay := thetaCuspFirstAtom_morseScale_div_weight_le_exponential hx
  have hTaylor := exp_neg_le_quadratic (u := 2 * x) (by positivity)
  have hfactor := mul_le_mul_of_nonneg_left hTaylor
    thetaCuspFirstAtomMorseFisherDecayFactor_pos.le
  calc
    thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x ≤
        1 + thetaCuspFirstAtomMorseFisherDecayFactor * Real.exp (-2 * x) := hdecay
    _ ≤ 1 + thetaCuspFirstAtomMorseFisherDecayFactor *
        (1 - 2 * x + (2 * x) ^ 2 / 2) := by
          convert add_le_add_left hfactor 1 using 1 <;> ring
    _ = thetaCuspFirstAtomMorseFisherQuadraticEnvelope x := by
      unfold thetaCuspFirstAtomMorseFisherQuadraticEnvelope
      ring

theorem thetaCuspFirstAtomMorseFisherQuadraticEnvelope_nonneg (x : ℝ) :
    0 ≤ thetaCuspFirstAtomMorseFisherQuadraticEnvelope x := by
  have hpoly : 0 ≤ 1 - 2 * x + 2 * x ^ 2 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  unfold thetaCuspFirstAtomMorseFisherQuadraticEnvelope
  exact add_nonneg zero_le_one
    (mul_nonneg thetaCuspFirstAtomMorseFisherDecayFactor_pos.le hpoly)

/-- The polynomial-envelope Fisher density is integrable. -/
theorem integrableOn_thetaCuspFirstRadialQuadraticMorseFisherQuadraticEnvelope :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspFirstAtomMorseFisherQuadraticEnvelope x *
          thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  let A := thetaCuspFirstAtomMorseFisherDecayFactor
  let b : ℕ → ℝ → ℝ := fun m x =>
    x ^ m * thetaCuspLiouvilleGibbsAtom 1 x
  have hb (m : ℕ) : IntegrableOn (b m) (Ioi 0) := by
    simpa only [b, thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        m (X ^ 2) (by norm_num : 0 < (1 : ℕ))
  have h := (((((hb 4).const_mul (1 + A)).add
      ((hb 5).const_mul (-1 - 3 * A))).add
        ((hb 6).const_mul (1 / 4 + (17 / 4) * A))).add
          ((hb 7).const_mul (-5 / 2 * A))).add
            ((hb 8).const_mul (1 / 2 * A))
  apply h.congr
  filter_upwards [] with x
  simp only [Pi.add_apply]
  dsimp [A, b]
  rw [thetaCuspFirstRadialQuadraticMorseField_eq]
  unfold thetaCuspFirstAtomMorseFisherQuadraticEnvelope
  ring

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseFisherExponentialEnvelope :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspFirstAtomMorseFisherExponentialEnvelope x *
          thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have hmajor :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_gibbs.const_mul
      thetaCuspFirstAtomMorseFisherEndpointFactor
  apply Integrable.mono' hmajor
  · exact (by
      unfold thetaCuspFirstRadialQuadraticMorseField thetaCuspQuadraticSteinField
        thetaCuspFirstAtomMorseFisherExponentialEnvelope
        thetaCuspLiouvilleGibbsAtom thetaCuspPolynomialAtom
      fun_prop : Continuous (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspFirstAtomMorseFisherExponentialEnvelope x *
          thetaCuspLiouvilleGibbsAtom 1 x)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hF : 0 ≤ thetaCuspFirstRadialQuadraticMorseField x := by
      unfold thetaCuspFirstRadialQuadraticMorseField thetaCuspQuadraticSteinField
      positivity
    have hb : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
      rw [← thetaCuspMorseGroundState_sq]
      positivity
    have henv := thetaCuspFirstAtomMorseFisherExponentialEnvelope_le_endpoint hx.le
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (mul_nonneg hF (thetaCuspFirstAtomMorseFisherExponentialEnvelope_nonneg x)) hb)]
    nlinarith [mul_nonneg hF hb,
      mul_le_mul_of_nonneg_right henv (mul_nonneg hF hb)]

/-- The exact residual first passes through a pointwise decaying envelope. -/
theorem thetaCuspFirstRadialQuadraticMorseFisherResidual_le_exponentialEnvelope :
    thetaCuspFirstRadialQuadraticMorseFisherResidual ≤
      ∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseField x *
          thetaCuspFirstAtomMorseFisherExponentialEnvelope x *
            thetaCuspLiouvilleGibbsAtom 1 x := by
  rw [thetaCuspFirstRadialQuadraticMorseFisherResidual]
  apply integral_mono_ae
    integrableOn_thetaCuspFirstRadialQuadraticMorseFisherResidual
    integrableOn_thetaCuspFirstRadialQuadraticMorseFisherExponentialEnvelope
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hratio := thetaCuspFirstAtom_morseScale_div_weight_le_exponential hx.le
  have hF : 0 ≤ thetaCuspFirstRadialQuadraticMorseField x := by
    unfold thetaCuspFirstRadialQuadraticMorseField thetaCuspQuadraticSteinField
    positivity
  have hb : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [← thetaCuspMorseGroundState_sq]
    positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio hF) hb

/-- The decaying envelope is unconditionally no larger than the old endpoint envelope. -/
theorem integral_morseFisherExponentialEnvelope_le_endpoint :
    (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialQuadraticMorseField x *
        thetaCuspFirstAtomMorseFisherExponentialEnvelope x *
          thetaCuspLiouvilleGibbsAtom 1 x) ≤
      thetaCuspFirstAtomMorseFisherEndpointFactor *
        ∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspLiouvilleGibbsAtom 1 x := by
  rw [← integral_const_mul]
  apply integral_mono_ae
    integrableOn_thetaCuspFirstRadialQuadraticMorseFisherExponentialEnvelope
    (integrableOn_thetaCuspFirstRadialQuadraticMorseField_mul_gibbs.const_mul
      thetaCuspFirstAtomMorseFisherEndpointFactor)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hF : 0 ≤ thetaCuspFirstRadialQuadraticMorseField x := by
    unfold thetaCuspFirstRadialQuadraticMorseField thetaCuspQuadraticSteinField
    positivity
  have hb : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [← thetaCuspMorseGroundState_sq]
    positivity
  have henv := thetaCuspFirstAtomMorseFisherExponentialEnvelope_le_endpoint hx.le
  nlinarith [mul_nonneg hF hb,
    mul_le_mul_of_nonneg_right henv (mul_nonneg hF hb)]

/-- The exact Fisher residual is bounded by a finite polynomial Gibbs value, retaining the
source-specific exponential decay that the endpoint estimate discards. -/
theorem thetaCuspFirstRadialQuadraticMorseFisherResidual_le_quadraticEnvelope :
    thetaCuspFirstRadialQuadraticMorseFisherResidual ≤
      ∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseField x *
          thetaCuspFirstAtomMorseFisherQuadraticEnvelope x *
            thetaCuspLiouvilleGibbsAtom 1 x := by
  rw [thetaCuspFirstRadialQuadraticMorseFisherResidual]
  apply integral_mono_ae
    integrableOn_thetaCuspFirstRadialQuadraticMorseFisherResidual
    integrableOn_thetaCuspFirstRadialQuadraticMorseFisherQuadraticEnvelope
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hratio := thetaCuspFirstAtom_morseScale_div_weight_le_quadratic hx.le
  have hF : 0 ≤ thetaCuspFirstRadialQuadraticMorseField x := by
    unfold thetaCuspFirstRadialQuadraticMorseField thetaCuspQuadraticSteinField
    positivity
  have hb : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [← thetaCuspMorseGroundState_sq]
    positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio hF) hb

/-- The sharpened Morse upper energy.  Its only integrals are polynomial moments of the radial
source and of the positive first-atom Gibbs density. -/
def thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy : ℝ :=
  (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialQuadraticMorseSourceField x *
        thetaCuspBornWittenWeight 1 x * thetaCuspLiouvilleGibbsAtom 1 x) +
    ∫ x : ℝ in Ioi 0,
      (thetaCuspFirstRadialQuadraticMorseGibbsField x +
          6 * thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspFirstAtomMorseFisherQuadraticEnvelope x) *
        thetaCuspLiouvilleGibbsAtom 1 x

theorem integrableOn_thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperGibbs :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspFirstRadialQuadraticMorseGibbsField x +
          6 * thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspFirstAtomMorseFisherQuadraticEnvelope x) *
        thetaCuspLiouvilleGibbsAtom 1 x) (Ioi 0) := by
  have hK :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseGibbsField_mul_gibbs
  have hE :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseFisherQuadraticEnvelope.const_mul 6
  apply (hK.add hE).congr
  filter_upwards [] with x
  simp only [Pi.add_apply]
  ring

/-- The quadratic envelope is a genuine upper bound for the exact virial energy. -/
theorem thetaCuspFirstRadialQuadraticVirialEnergy_le_morseQuadraticEnvelopeUpperEnergy :
    thetaCuspFirstRadialQuadraticVirialEnergy ≤
      thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy := by
  rw [thetaCuspFirstRadialQuadraticVirialEnergy_eq_morseReducedEnergy,
    thetaCuspFirstRadialQuadraticMorseReducedEnergy,
    thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy]
  have hres :=
    thetaCuspFirstRadialQuadraticMorseFisherResidual_le_quadraticEnvelope
  have hres6 := mul_le_mul_of_nonneg_left hres (by norm_num : (0 : ℝ) ≤ 6)
  have hK :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseGibbsField_mul_gibbs
  have hE :=
    integrableOn_thetaCuspFirstRadialQuadraticMorseFisherQuadraticEnvelope
  have hsplit :
      (∫ x : ℝ in Ioi 0,
        (thetaCuspFirstRadialQuadraticMorseGibbsField x +
            6 * thetaCuspFirstRadialQuadraticMorseField x *
              thetaCuspFirstAtomMorseFisherQuadraticEnvelope x) *
          thetaCuspLiouvilleGibbsAtom 1 x) =
        (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseGibbsField x *
            thetaCuspLiouvilleGibbsAtom 1 x) +
        6 * (∫ x : ℝ in Ioi 0,
          thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspFirstAtomMorseFisherQuadraticEnvelope x *
              thetaCuspLiouvilleGibbsAtom 1 x) := by
    rw [show (fun x : ℝ =>
        (thetaCuspFirstRadialQuadraticMorseGibbsField x +
            6 * thetaCuspFirstRadialQuadraticMorseField x *
              thetaCuspFirstAtomMorseFisherQuadraticEnvelope x) *
          thetaCuspLiouvilleGibbsAtom 1 x) =
      fun x =>
        thetaCuspFirstRadialQuadraticMorseGibbsField x *
            thetaCuspLiouvilleGibbsAtom 1 x +
          6 * (thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspFirstAtomMorseFisherQuadraticEnvelope x *
              thetaCuspLiouvilleGibbsAtom 1 x) by
        funext x
        ring,
      integral_add hK (hE.const_mul 6), integral_const_mul]
  rw [hsplit]
  linarith

/-- Literal finite-moment value of the exponentially sharpened Morse upper energy. -/
def thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeFiniteMomentUpperValue : ℝ :=
  (3 / 4 : ℝ) * thetaCuspBornWittenRadialPowerMoment 0 1 1 +
    thetaCuspBornWittenRadialPowerMoment 1 1 1 -
    (7 / 8 : ℝ) * thetaCuspBornWittenRadialPowerMoment 2 1 1 -
    (1 / 2 : ℝ) * thetaCuspBornWittenRadialPowerMoment 3 1 1 +
    (5 / 16 : ℝ) * thetaCuspBornWittenRadialPowerMoment 4 1 1 +
    8 * thetaCuspLiouvilleGibbsMoment 3 1 +
    (1 + 6 * thetaCuspFirstAtomMorseFisherDecayFactor) *
      thetaCuspLiouvilleGibbsMoment 4 1 -
    (8 + 18 * thetaCuspFirstAtomMorseFisherDecayFactor) *
      thetaCuspLiouvilleGibbsMoment 5 1 +
    ((11 / 4 : ℝ) +
      (51 / 2 : ℝ) * thetaCuspFirstAtomMorseFisherDecayFactor) *
      thetaCuspLiouvilleGibbsMoment 6 1 -
    15 * thetaCuspFirstAtomMorseFisherDecayFactor *
      thetaCuspLiouvilleGibbsMoment 7 1 +
    3 * thetaCuspFirstAtomMorseFisherDecayFactor *
      thetaCuspLiouvilleGibbsMoment 8 1

/-- The quadratic-envelope Gibbs integral is exactly a six-coordinate polynomial moment value. -/
theorem integral_morseQuadraticEnvelopeUpperGibbs_eq_gibbsMoments :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspFirstRadialQuadraticMorseGibbsField x +
          6 * thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspFirstAtomMorseFisherQuadraticEnvelope x) *
        thetaCuspLiouvilleGibbsAtom 1 x) =
      8 * thetaCuspLiouvilleGibbsMoment 3 1 +
        (1 + 6 * thetaCuspFirstAtomMorseFisherDecayFactor) *
          thetaCuspLiouvilleGibbsMoment 4 1 -
        (8 + 18 * thetaCuspFirstAtomMorseFisherDecayFactor) *
          thetaCuspLiouvilleGibbsMoment 5 1 +
        ((11 / 4 : ℝ) +
          (51 / 2 : ℝ) * thetaCuspFirstAtomMorseFisherDecayFactor) *
          thetaCuspLiouvilleGibbsMoment 6 1 -
        15 * thetaCuspFirstAtomMorseFisherDecayFactor *
          thetaCuspLiouvilleGibbsMoment 7 1 +
        3 * thetaCuspFirstAtomMorseFisherDecayFactor *
          thetaCuspLiouvilleGibbsMoment 8 1 := by
  let A := thetaCuspFirstAtomMorseFisherDecayFactor
  let b : ℕ → ℝ → ℝ := fun m x =>
    x ^ m * thetaCuspLiouvilleGibbsAtom 1 x
  let f3 : ℝ → ℝ := fun x => 8 * b 3 x
  let f4 : ℝ → ℝ := fun x => (1 + 6 * A) * b 4 x
  let f5 : ℝ → ℝ := fun x => -(8 + 18 * A) * b 5 x
  let f6 : ℝ → ℝ := fun x => ((11 / 4 : ℝ) + (51 / 2 : ℝ) * A) * b 6 x
  let f7 : ℝ → ℝ := fun x => -(15 * A) * b 7 x
  let f8 : ℝ → ℝ := fun x => (3 * A) * b 8 x
  have hb (m : ℕ) : IntegrableOn (b m) (Ioi 0) := by
    simpa only [b, thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        m (X ^ 2) (by norm_num : 0 < (1 : ℕ))
  have hf3 : IntegrableOn f3 (Ioi 0) := (hb 3).const_mul 8
  have hf4 : IntegrableOn f4 (Ioi 0) := (hb 4).const_mul (1 + 6 * A)
  have hf5 : IntegrableOn f5 (Ioi 0) := (hb 5).const_mul (-(8 + 18 * A))
  have hf6 : IntegrableOn f6 (Ioi 0) :=
    (hb 6).const_mul ((11 / 4 : ℝ) + (51 / 2 : ℝ) * A)
  have hf7 : IntegrableOn f7 (Ioi 0) := (hb 7).const_mul (-(15 * A))
  have hf8 : IntegrableOn f8 (Ioi 0) := (hb 8).const_mul (3 * A)
  have hpoint : (fun x : ℝ =>
      (thetaCuspFirstRadialQuadraticMorseGibbsField x +
          6 * thetaCuspFirstRadialQuadraticMorseField x *
            thetaCuspFirstAtomMorseFisherQuadraticEnvelope x) *
        thetaCuspLiouvilleGibbsAtom 1 x) =
      fun x => ((((f3 x + f4 x) + f5 x) + f6 x) + f7 x) + f8 x := by
    funext x
    rw [thetaCuspFirstRadialQuadraticMorseGibbsField_eq,
      thetaCuspFirstRadialQuadraticMorseField_eq]
    dsimp [A, b, f3, f4, f5, f6, f7, f8]
    unfold thetaCuspFirstAtomMorseFisherQuadraticEnvelope
    ring
  rw [hpoint]
  have h34 :
      (∫ x : ℝ in Ioi 0, f3 x + f4 x) =
        (∫ x : ℝ in Ioi 0, f3 x) + (∫ x : ℝ in Ioi 0, f4 x) := by
    simpa only [Pi.add_apply] using integral_add hf3 hf4
  have h345 :
      (∫ x : ℝ in Ioi 0, (f3 x + f4 x) + f5 x) =
        (∫ x : ℝ in Ioi 0, f3 x + f4 x) + (∫ x : ℝ in Ioi 0, f5 x) := by
    simpa only [Pi.add_apply] using integral_add (hf3.add hf4) hf5
  have h3456 :
      (∫ x : ℝ in Ioi 0, ((f3 x + f4 x) + f5 x) + f6 x) =
        (∫ x : ℝ in Ioi 0, (f3 x + f4 x) + f5 x) +
          (∫ x : ℝ in Ioi 0, f6 x) := by
    simpa only [Pi.add_apply] using integral_add ((hf3.add hf4).add hf5) hf6
  have h34567 :
      (∫ x : ℝ in Ioi 0, (((f3 x + f4 x) + f5 x) + f6 x) + f7 x) =
        (∫ x : ℝ in Ioi 0, ((f3 x + f4 x) + f5 x) + f6 x) +
          (∫ x : ℝ in Ioi 0, f7 x) := by
    simpa only [Pi.add_apply] using
      integral_add (((hf3.add hf4).add hf5).add hf6) hf7
  have h345678 :
      (∫ x : ℝ in Ioi 0,
        ((((f3 x + f4 x) + f5 x) + f6 x) + f7 x) + f8 x) =
        (∫ x : ℝ in Ioi 0, (((f3 x + f4 x) + f5 x) + f6 x) + f7 x) +
          (∫ x : ℝ in Ioi 0, f8 x) := by
    simpa only [Pi.add_apply] using
      integral_add ((((hf3.add hf4).add hf5).add hf6).add hf7) hf8
  rw [h345678, h34567, h3456, h345, h34]
  dsimp [f3, f4, f5, f6, f7, f8]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]
  simp only [thetaCuspLiouvilleGibbsMoment, b]
  dsimp [A]
  ring

/-- Exact finite-moment expansion of the sharpened upper energy. -/
theorem thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy_eq_finiteMoments :
    thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy =
      thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeFiniteMomentUpperValue := by
  rw [thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy,
    thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeFiniteMomentUpperValue,
    integral_morseSourceField_weight_gibbs_eq_radialPowerMoments,
    integral_morseQuadraticEnvelopeUpperGibbs_eq_gibbsMoments]
  ring

/-- Source-specific scalar certificate after the exponential Morse decay has been retained. -/
def ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate : Prop :=
  (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialQuadraticSteinCoupling ^ 2

theorem thetaCusp_quadraticVirialEnergyCertificate_of_morseQuadraticEnvelope
    (hcert : ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate) :
    ThetaCuspFirstRadialQuadraticVirialEnergyCertificate := by
  rw [ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate] at hcert
  rw [ThetaCuspFirstRadialQuadraticVirialEnergyCertificate]
  have hfactor : 0 ≤
      (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 := by
    positivity
  calc
    (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialQuadraticVirialEnergy ≤
        (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy :=
      mul_le_mul_of_nonneg_left
        thetaCuspFirstRadialQuadraticVirialEnergy_le_morseQuadraticEnvelopeUpperEnergy
        hfactor
    _ ≤ 9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialQuadraticSteinCoupling ^ 2 := hcert

theorem thetaCusp_firstRadial_upper_of_morseQuadraticEnvelope
    (hcert : ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate) :
    14 * ((3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 :=
  thetaCusp_firstRadial_upper_of_quadraticVirialEnergyCertificate
    (thetaCusp_quadraticVirialEnergyCertificate_of_morseQuadraticEnvelope hcert)

/-- Direct interface from the sharpened source estimate to every linear prime--archimedean
Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_morseQuadraticEnvelope
    (hcert : ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  exact forall_primeArchSourceTraceHankel_linear_nonneg_of_radialBornWittenAmplitude
    (thetaCusp_firstRadial_upper_of_morseQuadraticEnvelope hcert) hrelaxed

/-- Statement package for the source side of the Connes--Born/Witten route.  The first five
clauses are unconditional; the final implication identifies exactly how the remaining finite
scalar estimate enters the first nonconstant trace-Hankel block. -/
def ThetaCuspFirstAtomMorseFisherExponentialEnvelopeMaster : Prop :=
    (∀ x : ℝ, 0 ≤ x →
      thetaCuspMorseScale 1 x / thetaCuspBornWittenWeight 1 x ≤
        thetaCuspFirstAtomMorseFisherExponentialEnvelope x) ∧
    (∀ x : ℝ, 0 < x →
      thetaCuspFirstAtomMorseFisherExponentialEnvelope x <
        thetaCuspFirstAtomMorseFisherEndpointFactor) ∧
    thetaCuspFirstRadialQuadraticMorseFisherResidual ≤
      ∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticMorseField x *
          thetaCuspFirstAtomMorseFisherExponentialEnvelope x *
            thetaCuspLiouvilleGibbsAtom 1 x ∧
    thetaCuspFirstRadialQuadraticVirialEnergy ≤
      thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy ∧
    thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy =
      thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeFiniteMomentUpperValue ∧
    (ThetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeCertificate →
      14 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
        9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
          thetaCuspBornWittenRadialRawMoment 2 1 1)

/-- Capstone proof of the exponentially sharpened source estimate package. -/
theorem thetaCuspFirstAtomMorseFisherExponentialEnvelopeMaster :
    ThetaCuspFirstAtomMorseFisherExponentialEnvelopeMaster := by
  rw [ThetaCuspFirstAtomMorseFisherExponentialEnvelopeMaster]
  exact ⟨
    fun x hx => thetaCuspFirstAtom_morseScale_div_weight_le_exponential hx,
    fun x hx => thetaCuspFirstAtomMorseFisherExponentialEnvelope_lt_endpoint hx,
    thetaCuspFirstRadialQuadraticMorseFisherResidual_le_exponentialEnvelope,
    thetaCuspFirstRadialQuadraticVirialEnergy_le_morseQuadraticEnvelopeUpperEnergy,
    thetaCuspFirstRadialQuadraticMorseQuadraticEnvelopeUpperEnergy_eq_finiteMoments,
    thetaCusp_firstRadial_upper_of_morseQuadraticEnvelope⟩

end

end RHTower
