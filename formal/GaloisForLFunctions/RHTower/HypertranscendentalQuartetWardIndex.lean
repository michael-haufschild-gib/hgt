import GaloisForLFunctions.HTGeometry.MulPolynomialInvariance
import GaloisForLFunctions.RHTower.EntireFunctionalEquationOffLine
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional
import GaloisForLFunctions.RHTower.XiRationalQuartetGauge
import GaloisForLFunctions.RHTower.XiWardEdgeMassQuantization

/-!
# Hypertranscendental quartet surgery and the quantized Ward index

Multiplication by the centered quartet polynomial preserves completed-Xi
hypertranscendence, entire regularity, the functional equation, Schwarz
symmetry, and nonvanishing on the open real critical segment, while inserting
an arbitrary off-critical quartet.  The inserted right-upper Schwarz pair
carries one universal Euler-edge infinitesimal Ward packet of mass `8π`.

The same surgery changes the exact logarithmic source by a nonzero rational
charge.  Thus differential-algebraic complexity and elementary completed
symmetries are insensitive to this finite divisor surgery, whereas the Ward
index and exact source marking detect it.
-/

open Complex Filter MeasureTheory Real Set
open scoped Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-! ## The polynomial gauge and hypertranscendence -/

/-- Polynomial whose evaluation is the centered FE--Schwarz quartet gauge. -/
def centeredQuartetPolynomial (a b : ℝ) : Polynomial ℂ :=
  ((((Polynomial.X - Polynomial.C ((1 / 2 : ℝ) : ℂ)) -
        Polynomial.C (a : ℂ)) ^ 2 +
      Polynomial.C ((b ^ 2 : ℝ) : ℂ)) *
    (((Polynomial.X - Polynomial.C ((1 / 2 : ℝ) : ℂ)) +
        Polynomial.C (a : ℂ)) ^ 2 +
      Polynomial.C ((b ^ 2 : ℝ) : ℂ)))

theorem centeredQuartetPolynomial_eval (a b : ℝ) (s : ℂ) :
    Polynomial.eval s (centeredQuartetPolynomial a b) =
      centeredQuartetGauge a b s := by
  simp only [centeredQuartetPolynomial, centeredQuartetGauge, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  push_cast
  ring

theorem centeredQuartetPolynomial_ne_zero {a b : ℝ} (hb : 0 < b) :
    centeredQuartetPolynomial a b ≠ 0 := by
  intro hzero
  have h := congrArg (Polynomial.eval (1 / 2 : ℂ)) hzero
  rw [centeredQuartetPolynomial_eval] at h
  simp only [Polynomial.eval_zero] at h
  have hval :
      centeredQuartetGauge a b (1 / 2 : ℂ) =
        (((a ^ 2 + b ^ 2 : ℝ) : ℂ)) ^ 2 := by
    simp only [centeredQuartetGauge]
    push_cast
    ring
  rw [hval] at h
  have hbase : (((a ^ 2 + b ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact ofReal_ne_zero.mpr (by positivity)
  exact (pow_ne_zero 2 hbase) h

/-- **Finite divisor surgery preserves completed-Xi hypertranscendence.** -/
theorem quartetGaugedXi_hypertranscendental {a b : ℝ} (hb : 0 < b) :
    Hypertranscendental (quartetGaugedXi a b) := by
  have hxiSmooth : ContDiff ℂ (⊤ : ℕ∞) xi :=
    xi_analyticOnNhd_univ.contDiff
  have hfun :
      quartetGaugedXi a b =
        fun s : ℂ => Polynomial.eval s (centeredQuartetPolynomial a b) * xi s := by
    funext s
    rw [quartetGaugedXi, centeredQuartetPolynomial_eval]
  rw [hfun]
  exact
    hypertranscendental_mul_polynomial hxiSmooth
      (a := centeredQuartetPolynomial a b)
      (centeredQuartetPolynomial_ne_zero hb) xi_hypertranscendental

/-! ## The universal `8π` packet -/

/-- Anti-causal response of the strict-right Schwarz pair inserted by the
quartet surgery.  Its poles are the reflected pair
`-(a ± ib)`. -/
def quartetAntiCausalWardResponse (a b : ℝ) (w : ℂ) : ℂ :=
  2 * ((w + ((a : ℂ) + I * (b : ℂ)))⁻¹ +
    (w + ((a : ℂ) - I * (b : ℂ)))⁻¹)

/-- Euler-edge infinitesimal Ward density of the inserted quartet. -/
def quartetWardInfinitesimalDensity (a b t : ℝ) : ℝ :=
  2 * (2 * (a + 1 / 2) /
      ((a + 1 / 2) ^ 2 + (t + b) ^ 2) +
    2 * (a + 1 / 2) /
      ((a + 1 / 2) ^ 2 + (t - b) ^ 2))

/-- The declared density is exactly twice the real part of the quartet's
anti-causal Ward response on the Euler edge. -/
theorem quartetWardInfinitesimalDensity_eq_response
    (a b t : ℝ) :
    quartetWardInfinitesimalDensity a b t =
      2 * (quartetAntiCausalWardResponse a b
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  let lam : ℂ := (a : ℂ) + I * (b : ℂ)
  let w : ℂ := (1 / 2 : ℂ) + I * (t : ℂ)
  have hlamre : lam.re = a := by
    simp [lam, Complex.add_re, Complex.mul_re]
  have hlamim : lam.im = b := by
    simp [lam, Complex.add_im, Complex.mul_im]
  have hwre : w.re = 1 / 2 := by
    simp [w, Complex.add_re, Complex.mul_re]
  have hwim : w.im = t := by
    simp [w, Complex.add_im, Complex.mul_im]
  have hzre : (w + lam).re = a + 1 / 2 := by
    rw [Complex.add_re, hwre, hlamre]
    ring
  have hzim : (w + lam).im = t + b := by
    rw [Complex.add_im, hwim, hlamim]
  have hznormSq : Complex.normSq (w + lam) =
      (a + 1 / 2) ^ 2 + (t + b) ^ 2 := by
    rw [Complex.normSq_apply, hzre, hzim]
    ring
  have hz're : (w + (starRingEnd ℂ) lam).re = a + 1 / 2 := by
    rw [Complex.add_re, hwre, Complex.conj_re, hlamre]
    ring
  have hz'im : (w + (starRingEnd ℂ) lam).im = t - b := by
    rw [Complex.add_im, hwim, Complex.conj_im, hlamim]
    ring
  have hz'normSq : Complex.normSq (w + (starRingEnd ℂ) lam) =
      (a + 1 / 2) ^ 2 + (t - b) ^ 2 := by
    rw [Complex.normSq_apply, hz're, hz'im]
    ring
  have hconj : (starRingEnd ℂ) lam = (a : ℂ) - I * (b : ℂ) := by
    apply Complex.ext <;> simp [lam, Complex.mul_re, Complex.mul_im]
  change _ = 2 * (quartetAntiCausalWardResponse a b w).re
  rw [quartetAntiCausalWardResponse]
  rw [show (a : ℂ) + I * (b : ℂ) = lam by rfl, ← hconj]
  rw [show (2 : ℂ) * ((w + lam)⁻¹ + (w + (starRingEnd ℂ) lam)⁻¹) =
      2 * (w + lam)⁻¹ + 2 * (w + (starRingEnd ℂ) lam)⁻¹ by ring]
  rw [Complex.add_re]
  have h2a : (2 * (w + lam)⁻¹).re = 2 * ((w + lam)⁻¹).re := by
    norm_num [Complex.mul_re]
  have h2b : (2 * (w + (starRingEnd ℂ) lam)⁻¹).re =
      2 * ((w + (starRingEnd ℂ) lam)⁻¹).re := by
    norm_num [Complex.mul_re]
  rw [h2a, h2b, Complex.inv_re, Complex.inv_re, hzre, hznormSq, hz're,
    hz'normSq]
  unfold quartetWardInfinitesimalDensity
  ring

theorem quartetWardInfinitesimalDensity_nonneg
    {a b : ℝ} (ha : 0 < a + 1 / 2) (t : ℝ) :
    0 ≤ quartetWardInfinitesimalDensity a b t := by
  unfold quartetWardInfinitesimalDensity
  have h₁ := lorentzian_nonneg ha (t + b)
  have h₂ := lorentzian_nonneg ha (t - b)
  nlinarith

/-- **Universal quartet charge.**  The infinitesimal Ward mass of an inserted
off-critical quartet is exactly `8π`, independently of its horizontal
displacement and height. -/
theorem lintegral_quartetWardInfinitesimalDensity
    {a b : ℝ} (ha : 0 < a + 1 / 2) :
    ∫⁻ t : ℝ, ENNReal.ofReal (quartetWardInfinitesimalDensity a b t) =
      ENNReal.ofReal (8 * π) := by
  let L₁ : ℝ → ℝ := fun t =>
    2 * (a + 1 / 2) / ((a + 1 / 2) ^ 2 + (t + b) ^ 2)
  let L₂ : ℝ → ℝ := fun t =>
    2 * (a + 1 / 2) / ((a + 1 / 2) ^ 2 + (t + -b) ^ 2)
  have hL₁ : ∀ t, 0 ≤ L₁ t := fun t => lorentzian_nonneg ha (t + b)
  have hL₂ : ∀ t, 0 ≤ L₂ t := fun t => lorentzian_nonneg ha (t + -b)
  have hmeas₁ : Measurable fun t => ENNReal.ofReal (L₁ t) :=
    (ENNReal.continuous_ofReal.comp (lorentzian_continuous ha b)).measurable
  have heq : ∀ t, ENNReal.ofReal (quartetWardInfinitesimalDensity a b t) =
      2 * (ENNReal.ofReal (L₁ t) + ENNReal.ofReal (L₂ t)) := by
    intro t
    rw [quartetWardInfinitesimalDensity]
    have hsub : t - b = t + -b := by ring
    rw [hsub]
    change ENNReal.ofReal (2 * (L₁ t + L₂ t)) = _
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_add (hL₁ t) (hL₂ t)]
    norm_num
  rw [lintegral_congr heq]
  rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num)]
  rw [MeasureTheory.lintegral_add_left hmeas₁]
  change 2 * ((∫⁻ t : ℝ, ENNReal.ofReal
      (2 * (a + 1 / 2) / ((a + 1 / 2) ^ 2 + (t + b) ^ 2))) +
    (∫⁻ t : ℝ, ENNReal.ofReal
      (2 * (a + 1 / 2) / ((a + 1 / 2) ^ 2 + (t + -b) ^ 2)))) =
      ENNReal.ofReal (8 * π)
  rw [lorentzian_lintegral_shift ha, lorentzian_lintegral_shift ha]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [show 2 * π + 2 * π = 4 * π by ring]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  norm_num
  ring

/-! ## Exact source marking -/

/-- Endpoint source weight of the quartet
`1 / 2 ± a ± ib`.  It is the cross charge of one orbit representative. -/
def quartetEndpointSourceWeight (a b : ℝ) : ℝ :=
  (1 / 4 + b ^ 2 - a ^ 2) /
    ((((1 / 2 + a) ^ 2 + b ^ 2) *
      ((1 / 2 - a) ^ 2 + b ^ 2)))

theorem quartetEndpointSourceWeight_pos
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hb : 0 < b) :
    0 < quartetEndpointSourceWeight a b := by
  unfold quartetEndpointSourceWeight
  apply div_pos
  · nlinarith [mul_pos ha0 (sub_pos.mpr ha1), sq_pos_of_pos hb]
  · positivity

theorem centeredQuartetGauge_zero_eq_endpointDenominator (a b : ℝ) :
    centeredQuartetGauge a b 0 =
      (((((1 / 2 + a) ^ 2 + b ^ 2) *
        ((1 / 2 - a) ^ 2 + b ^ 2) : ℝ)) : ℂ) := by
  unfold centeredQuartetGauge
  push_cast
  ring

theorem centeredQuartetGauge_hasDerivAt_zero (a b : ℝ) :
    HasDerivAt (centeredQuartetGauge a b)
      ((-2 : ℂ) * (1 / 4 + b ^ 2 - a ^ 2)) 0 := by
  have hfun : centeredQuartetGauge a b =
      fun s : ℂ =>
        (((s - 1 / 2) - a) ^ 2 + b ^ 2) *
          (((s - 1 / 2) + a) ^ 2 + b ^ 2) := by
    funext s
    simp only [centeredQuartetGauge]
  rw [hfun]
  convert
    (((((hasDerivAt_id (𝕜 := ℂ) 0).sub_const (1 / 2)).sub_const (a : ℂ)).pow 2).add_const
        ((b ^ 2 : ℝ) : ℂ)).mul
      (((((hasDerivAt_id (𝕜 := ℂ) 0).sub_const (1 / 2)).add_const (a : ℂ)).pow 2).add_const
        ((b ^ 2 : ℝ) : ℂ))
    using 1
  · funext x
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    push_cast
    ring
  · simp only [Pi.pow_apply, id_eq]
    push_cast
    ring

theorem centeredQuartetGauge_logDeriv_zero (a b : ℝ) :
    logDeriv (centeredQuartetGauge a b) 0 =
      ((-2 : ℂ) * (1 / 4 + b ^ 2 - a ^ 2)) /
        centeredQuartetGauge a b 0 := by
  rw [logDeriv_apply, (centeredQuartetGauge_hasDerivAt_zero a b).deriv]

/-- **Endpoint source/Ward conservation.**  The logarithmic source charge of
one inserted quartet is exactly minus twice its endpoint weight. -/
theorem centeredQuartetGauge_logDeriv_zero_eq_neg_two_weight (a b : ℝ) :
    logDeriv (centeredQuartetGauge a b) 0 =
      (((-2) * quartetEndpointSourceWeight a b : ℝ) : ℂ) := by
  rw [centeredQuartetGauge_logDeriv_zero,
    centeredQuartetGauge_zero_eq_endpointDenominator]
  unfold quartetEndpointSourceWeight
  push_cast
  ring

/-- Source-weighted mass carried by the quartet's universal Ward packet. -/
def quartetSourceWeightedWardMass (a b : ℝ) : ℝ :=
  (8 * π) * quartetEndpointSourceWeight a b

/-- The source-weighted `8π` Ward mass is the endpoint logarithmic-source
response, with the universal normalization `-4π`. -/
theorem quartetSourceWeightedWardMass_eq_logDeriv (a b : ℝ) :
    quartetSourceWeightedWardMass a b =
      -4 * π * (logDeriv (centeredQuartetGauge a b) 0).re := by
  rw [centeredQuartetGauge_logDeriv_zero_eq_neg_two_weight]
  simp only [ofReal_re]
  unfold quartetSourceWeightedWardMass
  ring

theorem centeredQuartetGauge_logDeriv_zero_ne
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hb : 0 < b) :
    logDeriv (centeredQuartetGauge a b) 0 ≠ 0 := by
  rw [centeredQuartetGauge_logDeriv_zero]
  apply div_ne_zero
  · apply mul_ne_zero
    · norm_num
    · have ha2 : a ^ 2 < (1 / 2 : ℝ) ^ 2 := by
        nlinarith [mul_pos ha0 (sub_pos.mpr ha1)]
      have hreal : 0 < (1 / 4 : ℝ) + b ^ 2 - a ^ 2 := by
        nlinarith [sq_pos_of_pos hb]
      have hcast :
          (1 / 4 : ℂ) + (b : ℂ) ^ 2 - (a : ℂ) ^ 2 =
            (((1 / 4 : ℝ) + b ^ 2 - a ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast]
      exact ofReal_ne_zero.mpr hreal.ne'
  · have hpos := centeredQuartetGauge_real_pos (a := a) (σ := 0) hb
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re] at hre
    exact (ne_of_gt hpos) hre

/-- Exact source marking separates every admissible quartet surgery from Xi. -/
theorem quartetGaugedXi_logDeriv_zero_ne
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hb : 0 < b) :
    logDeriv (quartetGaugedXi a b) 0 ≠ logDeriv xi 0 := by
  have hprod :
      logDeriv (quartetGaugedXi a b) 0 =
        logDeriv (centeredQuartetGauge a b) 0 + logDeriv xi 0 := by
    change logDeriv (fun z => centeredQuartetGauge a b z * xi z) 0 = _
    rw [logDeriv_mul 0]
    · intro hzero
      have hre := congrArg Complex.re hzero
      simp only [Complex.zero_re] at hre
      exact (ne_of_gt (centeredQuartetGauge_real_pos (a := a) (σ := 0) hb)) hre
    · rw [xi_zero]
      norm_num
    · unfold centeredQuartetGauge
      fun_prop
    · exact xi_differentiable 0
  rw [hprod]
  intro h
  apply centeredQuartetGauge_logDeriv_zero_ne ha0 ha1 hb
  linear_combination h

/-! ## Packaged law -/

/-- **Hypertranscendental quartet/Ward-index law.**  Every point in the
strict right half of the critical strip and every positive height admits one
quartet surgery that preserves the completed analytic/symmetry/real-anchor
and hypertranscendental data, is generated by a nonnegative
reflection-compatible source correction, but is detected by a single `8π`
Ward packet and by the exact logarithmic source. -/
theorem hypertranscendental_quartetWardIndex_law
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hb : 0 < b) :
    Hypertranscendental (quartetGaugedXi a b) ∧
    (∀ s, AnalyticAt ℂ (quartetGaugedXi a b) s) ∧
    (∀ s, quartetGaugedXi a b (1 - s) = quartetGaugedXi a b s) ∧
    (∀ s, quartetGaugedXi a b ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (quartetGaugedXi a b s)) ∧
    (∀ σ : ℝ, 0 < σ → σ < 1 → quartetGaugedXi a b (σ : ℂ) ≠ 0) ∧
    (quartetPoint a b).re ≠ 1 / 2 ∧
    quartetGaugedXi a b (quartetPoint a b) = 0 ∧
    (∀ u : ℝ, 0 ≤ u → 0 ≤ entireFEDensity a b u) ∧
    (∀ s : ℂ, entireFETransform a b s + entireFETransform a b (1 - s) = 0) ∧
    (∀ t : ℝ, 0 ≤ quartetWardInfinitesimalDensity a b t) ∧
    (∫⁻ t : ℝ, ENNReal.ofReal (quartetWardInfinitesimalDensity a b t) =
      ENNReal.ofReal (8 * π)) ∧
    logDeriv (quartetGaugedXi a b) 0 ≠ logDeriv xi 0 := by
  refine ⟨quartetGaugedXi_hypertranscendental hb,
    quartetGaugedXi_analyticAt a b,
    quartetGaugedXi_one_sub a b,
    quartetGaugedXi_conj a b,
    fun _ hσ0 hσ1 => quartetGaugedXi_real_anchor_ne_zero hb hσ0 hσ1,
    quartetPoint_off_critical (ne_of_gt ha0),
    quartetGaugedXi_quartetPoint a b,
    fun _ hu => entireFEDensity_nonneg ha0 ha1 hu,
    entireFETransform_antisymm a b,
    fun t => quartetWardInfinitesimalDensity_nonneg (by linarith) t,
    lintegral_quartetWardInfinitesimalDensity (by linarith),
    quartetGaugedXi_logDeriv_zero_ne ha0 ha1 hb⟩

end RHTower
