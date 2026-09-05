import GaloisForLFunctions.RHTower.GammaVerticalRatioUniform
import GaloisForLFunctions.RHTower.ZetaChiStripGrowth
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftGeneralPowerBound
import GaloisForLFunctions.RHTower.WeightedMeanSquareTransfer

/-!
# High-block law: the sharp modulus of `χ` on a moving displaced line

`‖χ(½ − d + iτ)‖ = (τ/2π)^d · e^{e(d,τ)}` with `|e(d,τ)| ≤ d (π/τ + 5/τ²)`, uniformly for
`0 ≤ d ≤ ¼` and every `τ > 0`. This is the exact weight of the dual×dual term: with
`d = R/log T` and `τ ≍ T` it is `e^{2R}(1 + o(1))` after squaring, the `e^{2R}` of the
Levinson/Young constant. Built from the corpus's quantitative vertical Gamma-ratio law
(`abs_gamma_vertical_ratio_log_le`) and the modulus identity `norm_zetaChi_eq_mul_inv`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The two Gamma arguments of `χ` on the displaced line. -/
theorem displaced_one_sub_div_two (d τ : ℝ) :
    (1 - displacedLinePt d τ) / 2 =
      ((1 / 4 + d / 2 : ℝ) : ℂ) + ((-(τ / 2) : ℝ) : ℂ) * I := by
  unfold displacedLinePt
  push_cast
  ring

theorem displaced_div_two (d τ : ℝ) :
    displacedLinePt d τ / 2 = ((1 / 4 - d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
  unfold displacedLinePt
  push_cast
  ring

/-- **Sharp modulus of `χ` on the moving displaced line, with explicit error.** -/
theorem abs_log_norm_zetaChi_displacedLinePt_sub_le {d τ : ℝ} (hd0 : 0 ≤ d) (hd4 : d ≤ 1 / 4)
    (hτ : 0 < τ) :
    |Real.log ‖zetaChi (displacedLinePt d τ)‖ - d * Real.log (τ / (2 * Real.pi))| ≤
      d * (Real.pi / τ + 5 / τ ^ 2) := by
  have hsim : (displacedLinePt d τ).im ≠ 0 := by
    simp [displacedLinePt]
    exact hτ.ne'
  have hre : (displacedLinePt d τ).re = 1 / 2 - d := by simp [displacedLinePt]
  have hconj : (starRingEnd ℂ) (((1 / 4 + d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I) =
      ((1 / 4 + d / 2 : ℝ) : ℂ) + ((-(τ / 2) : ℝ) : ℂ) * I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hΓ1 : ‖Complex.Gamma ((1 - displacedLinePt d τ) / 2)‖ =
      ‖Complex.Gamma (((1 / 4 + d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ := by
    rw [displaced_one_sub_div_two, ← hconj, Complex.Gamma_conj, Complex.norm_conj]
  have hA : Complex.Gamma (((1 / 4 + d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp
    linarith
  have hB : Complex.Gamma (((1 / 4 - d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp
    linarith
  have hApos : 0 < ‖Complex.Gamma (((1 / 4 + d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ :=
    norm_pos_iff.mpr hA
  have hBpos : 0 < ‖Complex.Gamma (((1 / 4 - d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ :=
    norm_pos_iff.mpr hB
  rw [norm_zetaChi_eq_mul_inv hsim, hre, hΓ1, displaced_div_two, norm_inv,
    show (1 / 2 - d - 1 / 2 : ℝ) = -d by ring,
    Real.log_mul (by positivity) (by positivity), Real.log_mul hApos.ne' (inv_pos.mpr hBpos).ne',
    Real.log_inv, Real.log_rpow Real.pi_pos]
  have hτ' : 0 < τ / 2 := by linarith
  have hkey := GaloisForLFunctions.RHTower.abs_gamma_vertical_ratio_log_le (a := 1 / 4 - d / 2) (δ := d) (τ := τ / 2)
    (by linarith) hd0 hτ'
  rw [show (1 / 4 - d / 2 + d : ℝ) = 1 / 4 + d / 2 by ring] at hkey
  have hlog : Real.log (τ / (2 * Real.pi)) = Real.log (τ / 2) - Real.log Real.pi := by
    rw [show τ / (2 * Real.pi) = (τ / 2) / Real.pi by ring,
      Real.log_div hτ'.ne' Real.pi_pos.ne']
  rw [hlog]
  have hE : d * (1 / (τ / 2) ^ 2 + Real.pi / (2 * (τ / 2)) +
      (1 / 2) * ((1 / 4 + d / 2) ^ 2 / (τ / 2) ^ 2)) ≤ d * (Real.pi / τ + 5 / τ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hd0
    have h1 : 1 / (τ / 2) ^ 2 = 4 / τ ^ 2 := by field_simp; ring
    have h2 : Real.pi / (2 * (τ / 2)) = Real.pi / τ := by field_simp
    have h3 : (1 / 2) * ((1 / 4 + d / 2) ^ 2 / (τ / 2) ^ 2) = 2 * (1 / 4 + d / 2) ^ 2 / τ ^ 2 := by
      field_simp; try ring
    have h4 : 2 * (1 / 4 + d / 2) ^ 2 / τ ^ 2 ≤ 1 / τ ^ 2 := by
      gcongr
      nlinarith
    rw [h1, h2, h3]
    have h5 : 4 / τ ^ 2 + 1 / τ ^ 2 = 5 / τ ^ 2 := by ring
    linarith
  have hrearr : -d * Real.log Real.pi +
      (Real.log ‖Complex.Gamma (((1 / 4 + d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ +
        -Real.log ‖Complex.Gamma (((1 / 4 - d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) -
      d * (Real.log (τ / 2) - Real.log Real.pi) =
      -((Real.log ‖Complex.Gamma (((1 / 4 - d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ -
        Real.log ‖Complex.Gamma (((1 / 4 + d / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) +
        d * Real.log (τ / 2)) := by ring
  rw [hrearr, abs_neg]
  exact hkey.trans hE

/-- Multiplicative form: `‖χ(½ − d + iτ)‖ = (τ/2π)^d e^{e}` with `|e| ≤ d(π/τ + 5/τ²)`. -/
theorem exists_norm_zetaChi_displacedLinePt_eq_weight_mul_exp {d τ : ℝ} (hd0 : 0 ≤ d)
    (hd4 : d ≤ 1 / 4) (hτ : 0 < τ) :
    ∃ e : ℝ, |e| ≤ d * (Real.pi / τ + 5 / τ ^ 2) ∧
      ‖zetaChi (displacedLinePt d τ)‖ = chiModulusWeight d τ * Real.exp e := by
  have hχ : zetaChi (displacedLinePt d τ) ≠ 0 := by
    apply zetaChi_ne_zero_of_mem_openStrip <;> simp [displacedLinePt] <;> linarith
  have hχpos : 0 < ‖zetaChi (displacedLinePt d τ)‖ := norm_pos_iff.mpr hχ
  have hw : 0 < τ / (2 * Real.pi) := by positivity
  refine ⟨Real.log ‖zetaChi (displacedLinePt d τ)‖ - d * Real.log (τ / (2 * Real.pi)),
    abs_log_norm_zetaChi_displacedLinePt_sub_le hd0 hd4 hτ, ?_⟩
  have hexp : Real.exp (d * Real.log (τ / (2 * Real.pi))) = chiModulusWeight d τ := by
    rw [chiModulusWeight, Real.rpow_def_of_pos hw, mul_comm]
  rw [Real.exp_sub, Real.exp_log hχpos, hexp]
  have hwpos : 0 < chiModulusWeight d τ := chiModulusWeight_pos hτ
  field_simp

/-- Squared form, the weight of the dual×dual term:
`‖χ‖² = (τ/2π)^{2d} e^{2e}`. -/
theorem exists_normSq_zetaChi_displacedLinePt_eq_weight_mul_exp {d τ : ℝ} (hd0 : 0 ≤ d)
    (hd4 : d ≤ 1 / 4) (hτ : 0 < τ) :
    ∃ e : ℝ, |e| ≤ 2 * d * (Real.pi / τ + 5 / τ ^ 2) ∧
      ‖zetaChi (displacedLinePt d τ)‖ ^ 2 = chiModulusWeight (2 * d) τ * Real.exp e := by
  obtain ⟨e, he, heq⟩ := exists_norm_zetaChi_displacedLinePt_eq_weight_mul_exp hd0 hd4 hτ
  refine ⟨2 * e, ?_, ?_⟩
  · rw [abs_mul, abs_two]
    linarith
  · have hw : 0 < τ / (2 * Real.pi) := by positivity
    rw [heq, mul_pow, ← Real.exp_nat_mul, chiModulusWeight, chiModulusWeight,
      ← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    push_cast
    ring_nf

end

end RHTower
