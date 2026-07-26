import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardEulerEdgeCompleteness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Edge mass quantization of the anti-causal Ward response

On the Euler edge the real part of the continued Ward response is the sum over
strict-right Schwarz pairs of two Lorentzian profiles of half-width
`Re λ + 1/2` centered at the reflected heights `∓ Im λ`.  Each profile carries
edge mass exactly `2π`, independently of the pair, so the total edge mass
quantizes:

`∫⁻ t, ofReal (Re r(1/2+it)) = Σ' (q : XiRightUpperZeroCopy), ofReal (4π)`.

The mass is zero exactly when the strict-right divisor is empty; RH is
therefore equivalent to vanishing of one nonnegative edge integral, and every
off-line pair contributes the same universal charge `4π` regardless of its
distance from the critical line.
-/

open Complex Filter MeasureTheory Real

namespace RHTower

noncomputable section

/-! ## Lorentzian calculus -/

theorem lorentzian_integral {x : ℝ} (hx : 0 < x) :
    ∫ u : ℝ, 2 * x / (x ^ 2 + u ^ 2) = 2 * π := by
  have hx2 : x ^ 2 ≠ 0 := by positivity
  have hfun : ∀ u : ℝ, 2 * x / (x ^ 2 + u ^ 2) =
      (2 / x) * (1 + (u / x) ^ 2)⁻¹ := by
    intro u
    have hden : (0 : ℝ) < x ^ 2 + u ^ 2 := by positivity
    field_simp
  simp only [hfun]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_div
      (fun v : ℝ => (1 + v ^ 2)⁻¹) x,
    integral_univ_inv_one_add_sq, abs_of_pos hx, smul_eq_mul]
  field_simp

theorem lorentzian_integrable0 {x : ℝ} (hx : 0 < x) :
    Integrable fun u : ℝ => 2 * x / (x ^ 2 + u ^ 2) := by
  have hx2 : x ^ 2 ≠ 0 := by positivity
  have h1 : Integrable fun u : ℝ => (1 + (u / x) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_div hx.ne'
  apply (h1.const_mul (2 / x)).congr
  filter_upwards with u
  have hden : (0 : ℝ) < x ^ 2 + u ^ 2 := by positivity
  field_simp

theorem lorentzian_nonneg {x : ℝ} (hx : 0 < x) (u : ℝ) :
    0 ≤ 2 * x / (x ^ 2 + u ^ 2) := by
  apply div_nonneg (by linarith)
  positivity

theorem lorentzian_lintegral0 {x : ℝ} (hx : 0 < x) :
    ∫⁻ u : ℝ, ENNReal.ofReal (2 * x / (x ^ 2 + u ^ 2)) =
      ENNReal.ofReal (2 * π) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (lorentzian_integrable0 hx)
    (Filter.Eventually.of_forall (lorentzian_nonneg hx)),
    lorentzian_integral hx]

theorem lorentzian_lintegral_shift {x : ℝ} (hx : 0 < x) (c : ℝ) :
    ∫⁻ t : ℝ, ENNReal.ofReal (2 * x / (x ^ 2 + (t + c) ^ 2)) =
      ENNReal.ofReal (2 * π) := by
  have hshift := MeasureTheory.lintegral_add_right_eq_self (μ := volume)
    (fun u : ℝ => ENNReal.ofReal (2 * x / (x ^ 2 + u ^ 2))) c
  calc ∫⁻ t : ℝ, ENNReal.ofReal (2 * x / (x ^ 2 + (t + c) ^ 2))
      = ∫⁻ u : ℝ, ENNReal.ofReal (2 * x / (x ^ 2 + u ^ 2)) := hshift
    _ = ENNReal.ofReal (2 * π) := lorentzian_lintegral0 hx

theorem lorentzian_continuous {x : ℝ} (hx : 0 < x) (c : ℝ) :
    Continuous fun t : ℝ => 2 * x / (x ^ 2 + (t + c) ^ 2) := by
  apply Continuous.div continuous_const
  · exact continuous_const.add ((continuous_id.add continuous_const).pow 2)
  · intro t
    have h1 : (0 : ℝ) < x ^ 2 + (t + c) ^ 2 := by positivity
    exact h1.ne'

/-! ## The edge profile of one Schwarz pair -/

/-- On the Euler edge, one complete Schwarz pair contributes exactly two
Lorentzian profiles of common half-width `Re λ + 1/2`, centered at the two
reflected heights `∓ Im λ`. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq
    (q : XiRightUpperZeroCopy) (t : ℝ) :
    (xiAntiCausalWardSchwarzPairResponse q ((1 / 2 : ℂ) + I * (t : ℂ))).re =
      2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
        (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
          (t + (xiRightCenteredZero q.1).im) ^ 2) +
      2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
        (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
          (t + -(xiRightCenteredZero q.1).im) ^ 2) := by
  set lam := xiRightCenteredZero q.1
  set w : ℂ := (1 / 2 : ℂ) + I * (t : ℂ) with hwdef
  have hconj :
      xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1) =
        (starRingEnd ℂ) lam :=
    xiRightCenteredZero_conj q.1
  have hwre : w.re = 1 / 2 := by
    rw [hwdef]
    norm_num [Complex.add_re, Complex.mul_re]
  have hwim : w.im = t := by
    rw [hwdef]
    norm_num [Complex.add_im, Complex.mul_im]
  have hzre : (w + lam).re = lam.re + 1 / 2 := by
    rw [Complex.add_re, hwre]
    ring
  have hzim : (w + lam).im = t + lam.im := by
    rw [Complex.add_im, hwim]
  have hznormSq : Complex.normSq (w + lam) =
      (lam.re + 1 / 2) ^ 2 + (t + lam.im) ^ 2 := by
    rw [Complex.normSq_apply, hzre, hzim]
    ring
  have hz're : (w + (starRingEnd ℂ) lam).re = lam.re + 1 / 2 := by
    rw [Complex.add_re, hwre, Complex.conj_re]
    ring
  have hz'im : (w + (starRingEnd ℂ) lam).im = t + -lam.im := by
    rw [Complex.add_im, hwim, Complex.conj_im]
  have hz'normSq : Complex.normSq (w + (starRingEnd ℂ) lam) =
      (lam.re + 1 / 2) ^ 2 + (t + -lam.im) ^ 2 := by
    rw [Complex.normSq_apply, hz're, hz'im]
    ring
  rw [xiAntiCausalWardSchwarzPairResponse, hconj]
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
  ring

theorem re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_continuous
    (q : XiRightUpperZeroCopy) :
    Continuous fun t : ℝ =>
      (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  have ha : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by
    linarith [xiRightCenteredZero_re_pos q.1]
  have heq : (fun t : ℝ =>
      (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      fun t : ℝ =>
        2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2) +
        2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2) :=
    funext (re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq q)
  rw [heq]
  exact (lorentzian_continuous ha _).add (lorentzian_continuous ha _)

/-- **Universal pair charge**: every strict-right Schwarz pair carries edge
mass exactly `4π`, independently of its height and of its distance from the
critical line. -/
theorem lintegral_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge
    (q : XiRightUpperZeroCopy) :
    ∫⁻ t : ℝ, ENNReal.ofReal
        ((xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      ENNReal.ofReal (4 * π) := by
  have ha : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by
    linarith [xiRightCenteredZero_re_pos q.1]
  have hpt : ∀ t : ℝ, ENNReal.ofReal
      ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      ENNReal.ofReal
        (2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) +
      ENNReal.ofReal
        (2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) := by
    intro t
    rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq q t,
      ENNReal.ofReal_add (lorentzian_nonneg ha _) (lorentzian_nonneg ha _)]
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal
      (2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
        (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
          (t + (xiRightCenteredZero q.1).im) ^ 2)) :=
    (ENNReal.continuous_ofReal.comp
      (lorentzian_continuous ha (xiRightCenteredZero q.1).im)).measurable
  rw [lintegral_congr hpt, MeasureTheory.lintegral_add_left hmeas,
    lorentzian_lintegral_shift ha, lorentzian_lintegral_shift ha,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-! ## Edge mass quantization -/

noncomputable local instance : Countable XiRightZeroCopy := inferInstance

noncomputable local instance : Countable XiRightUpperZeroCopy := inferInstance

/-- **Edge mass quantization law.**  The total edge mass of the continued Ward
response counts the strict-right Schwarz pairs with universal charge `4π`. -/
theorem lintegral_re_continuedXiAntiCausalWardResponse_eulerEdge :
    ∫⁻ t : ℝ, ENNReal.ofReal
        ((continuedXiAntiCausalWardResponse
          ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      ∑' _ : XiRightUpperZeroCopy, ENNReal.ofReal (4 * π) := by
  have hpt : ∀ t : ℝ, ENNReal.ofReal
      ((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      ∑' q : XiRightUpperZeroCopy,
        ENNReal.ofReal
          ((xiAntiCausalWardSchwarzPairResponse q
            ((1 / 2 : ℂ) + I * (t : ℂ))).re) := by
    intro t
    have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
      norm_num [Complex.add_re, Complex.mul_re]
    have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
    have hreal : Summable (fun p : XiRightUpperZeroCopy =>
        (xiAntiCausalWardSchwarzPairResponse p
          ((1 / 2 : ℂ) + I * (t : ℂ))).re) := by
      simpa only [Complex.reCLM_apply] using hsum.mapL Complex.reCLM
    rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
      Complex.re_tsum hsum]
    exact ENNReal.ofReal_tsum_of_nonneg
      (fun p => (re_xiAntiCausalWardSchwarzPairResponse_pos p hw).le) hreal
  have hqmeas : ∀ q : XiRightUpperZeroCopy,
      AEMeasurable (fun t : ℝ => ENNReal.ofReal
        ((xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))).re)) :=
    fun q => ((ENNReal.continuous_ofReal.comp
      (re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_continuous
        q)).measurable).aemeasurable
  rw [lintegral_congr hpt, MeasureTheory.lintegral_tsum hqmeas]
  exact tsum_congr
    (fun q => lintegral_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge q)

/-- **RH as vanishing edge mass.**  RH is equivalent to the vanishing of the
single nonnegative edge integral of the continued Ward response. -/
theorem riemannHypothesis_iff_lintegral_re_continuedXiAntiCausalWardResponse_eq_zero :
    RiemannHypothesis ↔
      ∫⁻ t : ℝ, ENNReal.ofReal
          ((continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + I * (t : ℂ))).re) = 0 := by
  rw [lintegral_re_continuedXiAntiCausalWardResponse_eulerEdge]
  constructor
  · intro hRH
    letI : IsEmpty XiRightZeroCopy := by
      constructor
      intro q
      obtain ⟨s, hs⟩ := xiSpectralPoint_real_of_rh hRH q.1
      have hpos := q.2
      rw [hs] at hpos
      simp at hpos
    letI : IsEmpty XiRightUpperZeroCopy := ⟨fun q => isEmptyElim q.1⟩
    simp
  · intro h0
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
    have hle := ENNReal.le_tsum
      (f := fun _ : XiRightUpperZeroCopy => ENNReal.ofReal (4 * π)) q
    rw [h0, le_zero_iff, ENNReal.ofReal_eq_zero] at hle
    nlinarith [pi_pos]

end

end RHTower
