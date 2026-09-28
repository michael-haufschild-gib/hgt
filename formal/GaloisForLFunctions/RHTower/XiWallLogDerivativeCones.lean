import GaloisForLFunctions.RHTower.ThetaHalfLinePortGauge
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# Strict phase cones of `X'/X` at the physical wall

With `X(w) = Ξ_C(iw)` the symmetrized theta transform, the paired canonical-product identity gives,
away from the zeros of `X`,

`z(w) = X'(w)/X(w) = w Σ_q 1/(w² + ζ_q²)`   (absolutely convergent, with multiplicity).

At `w_h = 1/2 + ih` each term has real numerator `C/2 + hD > (t - h)²/2 > 0` and cone numerator
`(h - k/2)C - (1/2 + kh)D > (h - k/2)(t² - h²) - (1/2 + kh)(h + t)`, where `C > t² - h²`,
`h - t < D < h + t`, `t = |Re ζ_q| ≥ 61/5` (zero radius) and `|Im ζ_q| < 1/2`.  Summing:
`Im z_h > k_h Re z_h > 0` for `(h, k_h) = (2, 11/4), (4, 15/4), (6, 4), (8, 2)`; in particular
`Re z₂/|z₂| < 4/√137 < 1/2`.  The wall points are not zeros of `X` (`Re s = 1`).
-/
open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-! ## The logarithmic derivative of the symmetrized port as a reciprocal-square resolvent -/

theorem thetaSymmetrizedPort_eq_XiC (w : ℂ) : thetaSymmetrizedPort w = XiC (I * w) :=
  thetaHalfLaplace_add_neg w

theorem deriv_thetaSymmetrizedPort_eq_XiC (w : ℂ) :
    deriv thetaSymmetrizedPort w = I * deriv XiC (I * w) := by
  have h := (XiC_differentiable (I * w)).hasDerivAt.comp w ((hasDerivAt_id w).const_mul I)
  have e : thetaSymmetrizedPort = XiC ∘ HMul.hMul I := by
    funext z; simp [thetaSymmetrizedPort_eq_XiC]
  rw [e, h.deriv]; ring

/-- The wall logarithmic derivative `z(w) = X'(w)/X(w)`. -/
def thetaPortLogDeriv (w : ℂ) : ℂ := deriv thetaSymmetrizedPort w / thetaSymmetrizedPort w

theorem exists_xiZeroCopy : Nonempty XiZeroCopy := by
  obtain ⟨t, _, ht⟩ := exists_Xi_zero_gt 0
  have h : XiC (t : ℂ) = 0 := by rw [XiC_ofReal, ht, Complex.ofReal_zero]
  obtain ⟨q, _⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp h
  exact ⟨q⟩

theorem summable_wallTerm {w : ℂ} (hX : thetaSymmetrizedPort w ≠ 0) :
    Summable fun q : XiZeroCopy => w / (w ^ 2 + xiSpectralPoint q ^ 2) := by
  rw [thetaSymmetrizedPort_eq_XiC] at hX
  have h := (summable_xiReciprocalSquareResolventTerm hX).mul_left w
  refine h.congr fun q => ?_
  have hρ := xiSpectralPoint_ne_zero q
  rw [xiReciprocalSquareResolventTerm, xiZeroCopyReciprocalSquare]
  have hne : w ^ 2 + xiSpectralPoint q ^ 2 ≠ 0 := by
    intro h0
    apply hX
    rw [XiC_eq_zero_iff_exists_xiZeroCopy]
    have : (I * w) ^ 2 = xiSpectralPoint q ^ 2 := by
      rw [mul_pow, Complex.I_sq]; linear_combination -h0
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h1 | h1
    · exact ⟨q, h1.symm⟩
    · exact ⟨xiZeroCopyReflectEquiv q, by rw [xiSpectralPoint_reflect, ← h1]⟩
  field_simp
  rw [Complex.I_sq, show xiSpectralPoint q ^ 2 - w ^ 2 * (-1) = w ^ 2 + xiSpectralPoint q ^ 2 by ring,
    mul_div_assoc, div_self hne, mul_one]

/-- **(18).** Away from the zeros of `X`, `X'/X(w) = w Σ_q 1/(w² + ζ_q²)`, summed with
multiplicity over the Xi divisor. -/
theorem thetaPortLogDeriv_eq {w : ℂ} (hX : thetaSymmetrizedPort w ≠ 0) :
    thetaPortLogDeriv w = ∑' q : XiZeroCopy, w / (w ^ 2 + xiSpectralPoint q ^ 2) := by
  have hX' : XiC (I * w) ≠ 0 := by rwa [← thetaSymmetrizedPort_eq_XiC]
  have h1 := logDeriv_XiC_eq_relativeResolventTrace hX'
  rw [xiRelativeResolventTrace_eq_reciprocalSquareResolvent hX', logDeriv_apply] at h1
  rw [thetaPortLogDeriv, deriv_thetaSymmetrizedPort_eq_XiC, thetaSymmetrizedPort_eq_XiC,
    mul_div_assoc, h1, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  have hρ := xiSpectralPoint_ne_zero q
  rw [xiReciprocalSquareResolventTerm, xiZeroCopyReciprocalSquare]
  have hne : w ^ 2 + xiSpectralPoint q ^ 2 ≠ 0 := by
    intro h0
    apply hX'
    rw [XiC_eq_zero_iff_exists_xiZeroCopy]
    have : (I * w) ^ 2 = xiSpectralPoint q ^ 2 := by
      rw [mul_pow, Complex.I_sq]; linear_combination -h0
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h1 | h1
    · exact ⟨q, h1.symm⟩
    · exact ⟨xiZeroCopyReflectEquiv q, by rw [xiSpectralPoint_reflect, ← h1]⟩
  field_simp
  rw [Complex.I_sq, show xiSpectralPoint q ^ 2 - (-1) * w ^ 2 = w ^ 2 + xiSpectralPoint q ^ 2 by ring,
    show (-1 : ℂ) * w * (w ^ 2 + xiSpectralPoint q ^ 2) = -(w * (w ^ 2 + xiSpectralPoint q ^ 2)) by
      ring, neg_div, neg_neg, mul_div_assoc, div_self hne, mul_one]

/-- The wall points `1/2 + ih` are not zeros of `X` (they lie on `Re s = 1` after reflection). -/
theorem thetaSymmetrizedPort_wall_ne_zero (h : ℝ) : thetaSymmetrizedPort (1 / 2 + h * I) ≠ 0 := by
  rw [thetaSymmetrizedPort_eq_XiC]
  intro h0
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp h0
  have him := (xiSpectralPoint_im_mem_openHalf q).2
  rw [hq] at him
  simp at him

/-! ## Strict cones at the wall heights -/

/-- The zero radius: every centered Xi frequency exceeds `61/5` in modulus. -/
theorem sixtyOne_fifths_le_abs_xiSpectralPoint_re (q : XiZeroCopy) :
    (61 / 5 : ℝ) ≤ |(xiSpectralPoint q).re| := by
  have h := fiveHundredNinetyNine_fourths_lt_xiSpectralPoint_re_sq q
  rw [← sq_abs] at h
  nlinarith [abs_nonneg (xiSpectralPoint q).re]

/-- **The termwise cone (19), (33).** If `h > 0`, `h - k/2 > 0`, `h < 61/5` and
`(h - k/2)(t² - h²) - (1/2 + kh)(h + t) > 0` for `t ≥ 61/5`, then every resolvent term at
`w = 1/2 + ih` lies in the cone `Im > k Re > 0`. -/
theorem wallTerm_cone {h k : ℝ} (hh : 0 < h) (hk : 0 ≤ k) (hkh : 0 < h - k / 2) (h61 : h < 61 / 5)
    (hpoly : ∀ t : ℝ, 61 / 5 ≤ t → 0 < (h - k / 2) * (t ^ 2 - h ^ 2) - (1 / 2 + k * h) * (h + t))
    (q : XiZeroCopy) :
    0 < ((1 / 2 + h * I) / ((1 / 2 + h * I) ^ 2 + xiSpectralPoint q ^ 2)).re ∧
      k * ((1 / 2 + h * I) / ((1 / 2 + h * I) ^ 2 + xiSpectralPoint q ^ 2)).re <
        ((1 / 2 + h * I) / ((1 / 2 + h * I) ^ 2 + xiSpectralPoint q ^ 2)).im := by
  set γ := (xiSpectralPoint q).re
  set δ := (xiSpectralPoint q).im
  set t := |γ|
  have ht : 61 / 5 ≤ t := sixtyOne_fifths_le_abs_xiSpectralPoint_re q
  have hδ := xiSpectralPoint_im_mem_openHalf q
  have hδ2 : δ ^ 2 < 1 / 4 := by nlinarith [hδ.1, hδ.2]
  have hγ2 : γ ^ 2 = t ^ 2 := (sq_abs γ).symm
  set C := 1 / 4 - h ^ 2 + γ ^ 2 - δ ^ 2
  set D := h + 2 * γ * δ
  have hv : (1 / 2 + h * I) ^ 2 + xiSpectralPoint q ^ 2 = (C : ℂ) + (D : ℂ) * I := by
    have hq : xiSpectralPoint q = (γ : ℂ) + (δ : ℂ) * I := (Complex.re_add_im _).symm
    rw [hq]
    apply Complex.ext <;> simp [sq, C, D] <;> ring
  have hC : t ^ 2 - h ^ 2 < C := by simp only [C]; linarith
  have hγδ : |2 * γ * δ| < t := by
    rw [abs_mul, abs_mul, abs_two]
    have : |δ| < 1 / 2 := abs_lt.mpr ⟨by linarith [hδ.1], hδ.2⟩
    nlinarith [abs_nonneg γ, abs_nonneg δ]
  have hD1 : h - t < D := by simp only [D]; linarith [neg_abs_le (2 * γ * δ)]
  have hD2 : D < h + t := by simp only [D]; linarith [le_abs_self (2 * γ * δ)]
  have hCpos : 0 < C := by nlinarith
  have hN : 0 < C ^ 2 + D ^ 2 := by positivity
  have hre : ((1 / 2 + h * I) / ((C : ℂ) + (D : ℂ) * I)).re = (C / 2 + h * D) / (C ^ 2 + D ^ 2) := by
    rw [Complex.div_re]; simp [Complex.normSq_apply]; ring
  have him : ((1 / 2 + h * I) / ((C : ℂ) + (D : ℂ) * I)).im = (h * C - D / 2) / (C ^ 2 + D ^ 2) := by
    rw [Complex.div_im]; simp [Complex.normSq_apply]; ring
  rw [hv, hre, him]
  have hnum : 0 < C / 2 + h * D := by nlinarith
  have hcone : 0 < (h * C - D / 2) - k * (C / 2 + h * D) := by
    have h1 := hpoly t ht
    have h2 : (h - k / 2) * (t ^ 2 - h ^ 2) < (h - k / 2) * C := mul_lt_mul_of_pos_left hC hkh
    have h3 : (1 / 2 + k * h) * D < (1 / 2 + k * h) * (h + t) :=
      mul_lt_mul_of_pos_left hD2 (by positivity)
    nlinarith
  refine ⟨div_pos hnum hN, ?_⟩
  rw [← mul_div_assoc, div_lt_div_iff_of_pos_right hN]
  linarith

/-- Summing a strict cone condition over the divisor. -/
theorem wallLogDeriv_cone {h k : ℝ} (hh : 0 < h) (hk : 0 ≤ k) (hkh : 0 < h - k / 2)
    (h61 : h < 61 / 5)
    (hpoly : ∀ t : ℝ, 61 / 5 ≤ t → 0 < (h - k / 2) * (t ^ 2 - h ^ 2) - (1 / 2 + k * h) * (h + t)) :
    0 < (thetaPortLogDeriv (1 / 2 + h * I)).re ∧
      k * (thetaPortLogDeriv (1 / 2 + h * I)).re < (thetaPortLogDeriv (1 / 2 + h * I)).im := by
  have hX := thetaSymmetrizedPort_wall_ne_zero h
  have hs := summable_wallTerm hX
  obtain ⟨q₀⟩ := exists_xiZeroCopy
  have hcone := wallTerm_cone hh hk hkh h61 hpoly
  rw [thetaPortLogDeriv_eq hX, Complex.re_tsum hs, Complex.im_tsum hs]
  have hre := hs.mapL Complex.reCLM
  have him := hs.mapL Complex.imCLM
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
  refine ⟨hre.tsum_pos (fun q => (hcone q).1.le) q₀ (hcone q₀).1, ?_⟩
  have hdiff := (him.sub (hre.mul_left k))
  have hpos := hdiff.tsum_pos (fun q => sub_nonneg.mpr (hcone q).2.le) q₀
    (sub_pos.mpr (hcone q₀).2)
  rw [him.tsum_sub (hre.mul_left k), tsum_mul_left] at hpos
  linarith

/-- **(19a).** At `w₀ = 1/2 + 2i`: `0 < Re z₀` and `Im z₀ > (11/4) Re z₀`. -/
theorem thetaPortLogDeriv_cone_two :
    0 < (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re ∧
      11 / 4 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re <
        (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im :=
  wallLogDeriv_cone (by norm_num) (by norm_num) (by norm_num) (by norm_num) fun t ht => by nlinarith

/-- **(35).** At `1/2 + 4i`: `Im z₄ > (15/4) Re z₄ > 0`. -/
theorem thetaPortLogDeriv_cone_four :
    0 < (thetaPortLogDeriv (1 / 2 + (4 : ℝ) * I)).re ∧
      15 / 4 * (thetaPortLogDeriv (1 / 2 + (4 : ℝ) * I)).re <
        (thetaPortLogDeriv (1 / 2 + (4 : ℝ) * I)).im :=
  wallLogDeriv_cone (by norm_num) (by norm_num) (by norm_num) (by norm_num) fun t ht => by nlinarith

/-- **(35).** At `1/2 + 6i`: `Im z₆ > 4 Re z₆ > 0`. -/
theorem thetaPortLogDeriv_cone_six :
    0 < (thetaPortLogDeriv (1 / 2 + (6 : ℝ) * I)).re ∧
      4 * (thetaPortLogDeriv (1 / 2 + (6 : ℝ) * I)).re <
        (thetaPortLogDeriv (1 / 2 + (6 : ℝ) * I)).im :=
  wallLogDeriv_cone (by norm_num) (by norm_num) (by norm_num) (by norm_num) fun t ht => by nlinarith

/-- At `1/2 + 8i`: `Im z₈ > 2 Re z₈ > 0`. -/
theorem thetaPortLogDeriv_cone_eight :
    0 < (thetaPortLogDeriv (1 / 2 + (8 : ℝ) * I)).re ∧
      2 * (thetaPortLogDeriv (1 / 2 + (8 : ℝ) * I)).re <
        (thetaPortLogDeriv (1 / 2 + (8 : ℝ) * I)).im :=
  wallLogDeriv_cone (by norm_num) (by norm_num) (by norm_num) (by norm_num) fun t ht => by nlinarith

/-- The phase aperture at `w₀`: `Re z₀/|z₀| < 4/√137 < 1/2`. -/
theorem thetaPortLogDeriv_two_aperture :
    (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re / ‖thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)‖ <
      4 / Real.sqrt 137 ∧ 4 / Real.sqrt 137 < 1 / 2 := by
  obtain ⟨h1, h2⟩ := thetaPortLogDeriv_cone_two
  set z := thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)
  have hs : 0 < Real.sqrt 137 := by positivity
  have hsq : Real.sqrt 137 ^ 2 = 137 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 137 / 4 * z.re < ‖z‖ := by
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have : (Real.sqrt 137 / 4 * z.re) ^ 2 < ‖z‖ ^ 2 := by
      rw [hnorm, mul_pow, div_pow, hsq]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  have hz : 0 < ‖z‖ := by nlinarith
  constructor
  · rw [div_lt_div_iff₀ hz hs]; nlinarith
  · rw [div_lt_div_iff₀ hs (by norm_num)]
    nlinarith [Real.sqrt_nonneg 137, sq_nonneg (Real.sqrt 137 - 8)]

end

end RHTower
