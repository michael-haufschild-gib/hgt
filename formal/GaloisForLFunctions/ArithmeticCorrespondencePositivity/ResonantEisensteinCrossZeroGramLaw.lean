import GaloisForLFunctions.RHTower.EisensteinResonantPartnerAngle
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# Bilateral Cauchy–Szegő Gram Law and Multiplicity Defect of Truncated Resonant Eisenstein States

For a nontrivial zero `ρ` of `Λ = reflectedCompletedLambda` in the critical strip `0 < Re ρ < 1`
with resonant spectral parameter `u(ρ) = (ρ − 1)/2`, the Arthur-truncated line model
`Λ^Y E_{u(ρ)}` (`Y ≥ 1`) lives in `L²(𝒟)` on the modular fundamental domain `𝒟 = fd`. Existing
corpus modules compute only the single-zero norm (`EisensteinResonantStateNorm`) and the pairing of
`ρ` with its functional-equation reflection `1 − conj ρ` (`EisensteinResonantPartnerAngle`).

This module establishes the complete `L²(𝒟)` Gram matrix across **all** pairs of strip zeros in
all four ordinate-sign quadrants:

1. **Upper-half-strip Cauchy–Szegő Gram law** (`hermitianPairing_resonantState_upper`,
   `crossZero_angle_law_upper`, `crossZero_cauchySchwarz_residual_upper`,
   `crossZero_saturation_upper_iff`): for any two upper-strip zeros `ρ₁, ρ₂` (`Im ρ_j > 0`) and
   `Y ≥ 1`,
   `⟨Λ^Y E_{u(ρ₁)}, Λ^Y E_{u(ρ₂)}⟩ = 2 Λ(ρ₁ − 1) conj(Λ(ρ₂ − 1)) Y^{1 − (ρ₁ + conj ρ₂)/2} / (2 − ρ₁ − conj ρ₂)`,
   with `Y`- and `Λ`-independent normalized squared cosine
   `4 (1 − Re ρ₁)(1 − Re ρ₂) / ‖2 − ρ₁ − conj ρ₂‖² = 1 − ‖ρ₁ − ρ₂‖² / ‖2 − ρ₁ − conj ρ₂‖²`.
   Cauchy–Schwarz saturates iff `ρ₁ = ρ₂`, and setting `ρ₂ = 1 − conj ρ₁` recovers the partner
   angle law `4 Re ρ₁ (1 − Re ρ₁)`.

2. **Full bilateral strip Gram matrix and Kronecker multiplicity defect**
   (`truncatedPairing_diag_resonantState`, `hermitianPairing_resonantState_all`): across all strip
   zeros `ρ₁, ρ₂` of arbitrary ordinate signs (`Im ρ_j ≠ 0`), off-conjugate pairs follow the exact
   same Cauchy–Szegő rational kernel, while conjugate pairs `ρ₂ = conj ρ₁` acquire the
   `Y`-independent L'Hôpital derivative residue `2 Λ(ρ₁ − 1) Λ'(ρ₁)`, which vanishes iff `ρ₁` is a
   multiple zero (`Λ'(ρ₁) = 0`).

3. **Half-line Laplace Gram isometry** (`hermitianPairing_resonantState_upper_eq_laplace_integral`,
   `resonantGramQuadraticForm_upper_eq_laplace_normSq`): the `L²(𝒟)` Hermitian Gram quadratic form
   of any finite linear combination of upper-strip resonant states equals the `L²((0, ∞), dt)`
   squared norm of the associated Laplace exponential packet.
-/

open Complex MeasureTheory Set Filter Topology ModularGroup
open scoped UpperHalfPlane
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

noncomputable section

/-! ### Strip zero preliminaries and conjugation symmetries -/

/-- Every zero of `reflectedCompletedLambda` in the open strip `0 < Re ρ < 1` lies off the real
axis, since `Γ_ℝ` has no zeros on `Re s > 0` and `ζ` is strictly negative on `(0, 1)`. -/
theorem im_ne_zero_of_reflectedCompletedLambda_strip_zero {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ.im ≠ 0 := by
  intro him
  unfold reflectedCompletedLambda at hρ
  have hζ : riemannZeta ρ = 0 :=
    (mul_eq_zero.mp hρ).resolve_left (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  have hreal : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hreal] at hζ
  exact riemannZeta_real_strip_ne_zero h0 h1 hζ

theorem resonantParameter_conj_eq (ρ : ℂ) :
    resonantParameter (starRingEnd ℂ ρ) = starRingEnd ℂ (resonantParameter ρ) := by
  unfold resonantParameter
  simp only [map_sub, map_div₀, map_one, map_ofNat]

theorem truncatedPairing_conj_both (Y : ℝ) (u v : ℂ) :
    truncatedPairing Y (starRingEnd ℂ u) (starRingEnd ℂ v) =
      starRingEnd ℂ (truncatedPairing Y u v) := by
  unfold truncatedPairing
  rw [← integral_conj]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  rw [← truncatedLineModel_conj, ← truncatedLineModel_conj, ← map_mul]

theorem hermitianPairing_conj_both (Y : ℝ) (u v : ℂ) :
    hermitianPairing Y (starRingEnd ℂ u) (starRingEnd ℂ v) =
      starRingEnd ℂ (hermitianPairing Y u v) := by
  unfold hermitianPairing
  rw [← integral_conj]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  rw [← truncatedLineModel_conj, ← truncatedLineModel_conj, ← map_mul]

theorem two_sub_add_conj_ne_zero {ρ₁ ρ₂ : ℂ} (h1₁ : ρ₁.re < 1) (h1₂ : ρ₂.re < 1) :
    2 - ρ₁ - starRingEnd ℂ ρ₂ ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

/-! ### Universal upper-half-strip Cauchy–Szegő Gram law -/

/-- **Universal upper-half-strip Cauchy–Szegő Gram law.** For any two upper-strip zeros `ρ₁, ρ₂`
of `Λ` (`0 < Re ρ_j < 1`, `0 < Im ρ_j`) and every truncation height `Y ≥ 1`, their truncated
resonant states pair through the shifted Cauchy–Szegő kernel `2 / (2 − ρ₁ − conj ρ₂)`. -/
theorem hermitianPairing_resonantState_upper {ρ₁ ρ₂ : ℂ}
    (hρ₁ : reflectedCompletedLambda ρ₁ = 0) (h0₁ : 0 < ρ₁.re) (_h1₁ : ρ₁.re < 1) (him₁ : 0 < ρ₁.im)
    (hρ₂ : reflectedCompletedLambda ρ₂ = 0) (h0₂ : 0 < ρ₂.re) (h1₂ : ρ₂.re < 1) (him₂ : 0 < ρ₂.im)
    {Y : ℝ} (hY : 1 ≤ Y) :
    hermitianPairing Y (resonantParameter ρ₁) (resonantParameter ρ₂) =
      2 * reflectedCompletedLambda (ρ₁ - 1) * starRingEnd ℂ (reflectedCompletedLambda (ρ₂ - 1)) *
        (Y : ℂ) ^ (1 - (ρ₁ + starRingEnd ℂ ρ₂) / 2) / (2 - ρ₁ - starRingEnd ℂ ρ₂) := by
  set u₁ := resonantParameter ρ₁
  set u₂ := resonantParameter ρ₂
  set w₂ := -(starRingEnd ℂ u₂)
  have hu₁ : u₁ ∈ eisensteinLineDomain := resonantParameter_mem h0₁ him₁
  have hu₂ : u₂ ∈ eisensteinLineDomain := resonantParameter_mem h0₂ him₂
  have hw₂ : w₂ ∈ eisensteinLineDomain :=
    neg_conj_mem_eisensteinLineDomain hu₂ (by linarith [resonantParameter_re_neg h1₂])
  have hherm : hermitianPairing Y u₁ u₂ = truncatedPairing Y u₁ w₂ := by
    unfold hermitianPairing truncatedPairing
    refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
    have him_conj : (starRingEnd ℂ u₂).im ≠ 0 := by simp [hu₂.2.ne']
    rw [truncatedLineModel_conj, ← truncatedLineModel_neg him_conj]
  have hms := maassSelberg_lineModel hu₁ hw₂ hY
  have hAu₁ : msA u₁ = 0 := by rw [msA_resonantParameter]; exact hρ₁
  have hBu₁ : msB u₁ = reflectedCompletedLambda (ρ₁ - 1) := msB_resonantParameter ρ₁
  have hAw₂ : msA w₂ = starRingEnd ℂ (reflectedCompletedLambda (ρ₂ - 1)) := by
    rw [msA_neg_conj hu₂.2.ne', msB_resonantParameter]
  have hBw₂ : msB w₂ = 0 := by
    rw [msB_neg_conj hu₂.2.ne', msA_resonantParameter, hρ₂, map_zero]
  have hexp : w₂ - u₁ = 1 - (ρ₁ + starRingEnd ℂ ρ₂) / 2 := by
    simp only [u₁, u₂, w₂, resonantParameter, map_sub, map_div₀, map_one, map_ofNat]
    ring
  have hsub : u₁ - w₂ = -(2 - ρ₁ - starRingEnd ℂ ρ₂) / 2 := by
    simp only [u₁, u₂, w₂, resonantParameter, map_sub, map_div₀, map_one, map_ofNat]
    ring
  have hadd_ne : u₁ + w₂ ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [u₁, u₂, w₂, resonantParameter, map_sub, map_div₀, map_one, map_ofNat,
      Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.div_ofNat_im, Complex.conj_im,
      Complex.one_im, Complex.zero_im] at him
    linarith
  have hden_ne : 2 - ρ₁ - starRingEnd ℂ ρ₂ ≠ 0 := two_sub_add_conj_ne_zero _h1₁ h1₂
  unfold msRight at hms
  rw [hAu₁, hBu₁, hAw₂, hBw₂, hexp, hsub] at hms
  simp only [zero_mul, mul_zero, zero_add, sub_zero, zero_sub] at hms
  have hcancel : (-(2 - ρ₁ - starRingEnd ℂ ρ₂) / 2) * truncatedPairing Y u₁ w₂ =
      -(reflectedCompletedLambda (ρ₁ - 1) * starRingEnd ℂ (reflectedCompletedLambda (ρ₂ - 1)) *
        (Y : ℂ) ^ (1 - (ρ₁ + starRingEnd ℂ ρ₂) / 2)) := by
    refine mul_left_cancel₀ hadd_ne ?_
    linear_combination hms
  rw [hherm, eq_div_iff hden_ne]
  linear_combination -2 * hcancel

/-- Pure complex norm identity governing the Cauchy–Szegő angle between two points in the strip:
`‖2 − ρ₁ − conj ρ₂‖² − 4 (1 − Re ρ₁)(1 − Re ρ₂) = ‖ρ₁ − ρ₂‖²`. -/
theorem norm_sq_two_sub_add_conj (ρ₁ ρ₂ : ℂ) :
    ‖2 - ρ₁ - starRingEnd ℂ ρ₂‖ ^ 2 - 4 * (1 - ρ₁.re) * (1 - ρ₂.re) = ‖ρ₁ - ρ₂‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  norm_num
  ring

/-- **Cross-zero angle law in the upper strip.** The normalized squared Hermitian inner product of
two truncated resonant states depends only on `(ρ₁, ρ₂)`, independent of the truncation height `Y`
and of the special values `Λ(ρ_j − 1)`. -/
theorem crossZero_angle_law_upper {ρ₁ ρ₂ : ℂ}
    (hρ₁ : reflectedCompletedLambda ρ₁ = 0) (h0₁ : 0 < ρ₁.re) (h1₁ : ρ₁.re < 1) (him₁ : 0 < ρ₁.im)
    (hρ₂ : reflectedCompletedLambda ρ₂ = 0) (h0₂ : 0 < ρ₂.re) (h1₂ : ρ₂.re < 1) (him₂ : 0 < ρ₂.im)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ‖hermitianPairing Y (resonantParameter ρ₁) (resonantParameter ρ₂)‖ ^ 2 =
      (4 * (1 - ρ₁.re) * (1 - ρ₂.re) / ‖2 - ρ₁ - starRingEnd ℂ ρ₂‖ ^ 2) *
        ((∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₁) Y z‖ ^ 2) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₂) Y z‖ ^ 2) := by
  have hYpos : 0 < Y := by linarith
  rw [hermitianPairing_resonantState_upper hρ₁ h0₁ h1₁ him₁ hρ₂ h0₂ h1₂ him₂ hY,
    integral_norm_sq_resonantState hρ₁ h0₁ h1₁ him₁ hY,
    integral_norm_sq_resonantState hρ₂ h0₂ h1₂ him₂ hY]
  have hYpow : ‖(Y : ℂ) ^ (1 - (ρ₁ + starRingEnd ℂ ρ₂) / 2)‖ ^ 2 =
      Y ^ (1 - ρ₁.re) * Y ^ (1 - ρ₂.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos, ← Real.rpow_natCast,
      ← Real.rpow_mul hYpos.le, ← Real.rpow_add hYpos]
    congr 1
    simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.add_re,
      Complex.conj_re, Nat.cast_ofNat]
    ring
  have hden : ‖2 - ρ₁ - starRingEnd ℂ ρ₂‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (two_sub_add_conj_ne_zero h1₁ h1₂)
  have hre₁ : 1 - ρ₁.re ≠ 0 := by linarith
  have hre₂ : 1 - ρ₂.re ≠ 0 := by linarith
  rw [norm_div, div_pow, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow,
    Complex.norm_conj, show ‖(2 : ℂ)‖ = 2 by simp, hYpow]
  field_simp
  ring

/-- **Cauchy–Schwarz residual form of the cross-zero angle law.** -/
theorem crossZero_cauchySchwarz_residual_upper {ρ₁ ρ₂ : ℂ}
    (hρ₁ : reflectedCompletedLambda ρ₁ = 0) (h0₁ : 0 < ρ₁.re) (h1₁ : ρ₁.re < 1) (him₁ : 0 < ρ₁.im)
    (hρ₂ : reflectedCompletedLambda ρ₂ = 0) (h0₂ : 0 < ρ₂.re) (h1₂ : ρ₂.re < 1) (him₂ : 0 < ρ₂.im)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ‖hermitianPairing Y (resonantParameter ρ₁) (resonantParameter ρ₂)‖ ^ 2 =
      (1 - ‖ρ₁ - ρ₂‖ ^ 2 / ‖2 - ρ₁ - starRingEnd ℂ ρ₂‖ ^ 2) *
        ((∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₁) Y z‖ ^ 2) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₂) Y z‖ ^ 2) := by
  rw [crossZero_angle_law_upper hρ₁ h0₁ h1₁ him₁ hρ₂ h0₂ h1₂ him₂ hY]
  congr 1
  have hden : ‖2 - ρ₁ - starRingEnd ℂ ρ₂‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (two_sub_add_conj_ne_zero h1₁ h1₂))
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hden]
  linarith [norm_sq_two_sub_add_conj ρ₁ ρ₂]

/-- **Strict non-collinearity of distinct resonant states:** Cauchy–Schwarz between two upper-strip
truncated resonant states is saturated if and only if `ρ₁ = ρ₂`. -/
theorem crossZero_saturation_upper_iff {ρ₁ ρ₂ : ℂ}
    (hρ₁ : reflectedCompletedLambda ρ₁ = 0) (h0₁ : 0 < ρ₁.re) (h1₁ : ρ₁.re < 1) (him₁ : 0 < ρ₁.im)
    (hρ₂ : reflectedCompletedLambda ρ₂ = 0) (h0₂ : 0 < ρ₂.re) (h1₂ : ρ₂.re < 1) (him₂ : 0 < ρ₂.im)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ‖hermitianPairing Y (resonantParameter ρ₁) (resonantParameter ρ₂)‖ ^ 2 =
      (∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₁) Y z‖ ^ 2) *
        (∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₂) Y z‖ ^ 2) ↔
      ρ₁ = ρ₂ := by
  rw [crossZero_cauchySchwarz_residual_upper hρ₁ h0₁ h1₁ him₁ hρ₂ h0₂ h1₂ him₂ hY]
  have hYpos : 0 < Y := by linarith
  have hpos₁ : 0 < ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₁) Y z‖ ^ 2 := by
    rw [integral_norm_sq_resonantState hρ₁ h0₁ h1₁ him₁ hY]
    have hn := norm_pos_iff.mpr (reflectedCompletedLambda_sub_one_ne_zero h1₁ him₁.ne')
    have hr : 0 < 1 - ρ₁.re := by linarith
    have hYp : 0 < Y ^ (1 - ρ₁.re) := Real.rpow_pos_of_pos hYpos _
    positivity
  have hpos₂ : 0 < ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₂) Y z‖ ^ 2 := by
    rw [integral_norm_sq_resonantState hρ₂ h0₂ h1₂ him₂ hY]
    have hn := norm_pos_iff.mpr (reflectedCompletedLambda_sub_one_ne_zero h1₂ him₂.ne')
    have hr : 0 < 1 - ρ₂.re := by linarith
    have hYp : 0 < Y ^ (1 - ρ₂.re) := Real.rpow_pos_of_pos hYpos _
    positivity
  have hprod_ne : ((∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₁) Y z‖ ^ 2) *
      ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₂) Y z‖ ^ 2) ≠ 0 :=
    (mul_pos hpos₁ hpos₂).ne'
  have hden_ne : ‖2 - ρ₁ - starRingEnd ℂ ρ₂‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (two_sub_add_conj_ne_zero h1₁ h1₂))
  constructor
  · intro h
    have h1 : (‖ρ₁ - ρ₂‖ ^ 2 / ‖2 - ρ₁ - starRingEnd ℂ ρ₂‖ ^ 2) *
        ((∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₁) Y z‖ ^ 2) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ₂) Y z‖ ^ 2) = 0 := by
      linear_combination -h
    have h2 : ‖ρ₁ - ρ₂‖ ^ 2 / ‖2 - ρ₁ - starRingEnd ℂ ρ₂‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h1).resolve_right hprod_ne
    have h3 : ‖ρ₁ - ρ₂‖ ^ 2 = 0 := (div_eq_zero_iff.mp h2).resolve_right hden_ne
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h3))
  · rintro rfl
    simp

/-- Specializing the cross-zero angle coefficient to the reflected partner `ρ₂ = 1 − conj ρ₁`
collapses `2 − ρ₁ − conj ρ₂` to `1` and recovers `4 Re ρ₁ (1 − Re ρ₁)`. -/
theorem crossZero_angle_coeff_partner (ρ : ℂ) :
    4 * (1 - ρ.re) * (1 - (1 - starRingEnd ℂ ρ).re) /
      ‖2 - ρ - starRingEnd ℂ (1 - starRingEnd ℂ ρ)‖ ^ 2 =
    4 * ρ.re * (1 - ρ.re) := by
  have hden : 2 - ρ - starRingEnd ℂ (1 - starRingEnd ℂ ρ) = 1 := by
    rw [map_sub, map_one, Complex.conj_conj]; ring
  rw [hden, norm_one, one_pow, div_one]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  ring

/-! ### Bilinear self-pairing, full bilateral strip Gram law, and multiplicity defect -/

/-- **Bilinear diagonal self-pairing of a truncated resonant state** at any strip zero `ρ` of `Λ`
(either `Im ρ > 0` or `Im ρ < 0`):
`∫_𝒟 (Λ^Y E_{u(ρ)})² dμ = Λ(ρ − 1)² Y^{1 − ρ} / (1 − ρ) + 2 Λ(ρ − 1) Λ'(ρ)`. -/
theorem truncatedPairing_diag_resonantState {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {Y : ℝ} (hY : 1 ≤ Y) :
    truncatedPairing Y (resonantParameter ρ) (resonantParameter ρ) =
      reflectedCompletedLambda (ρ - 1) ^ 2 * (Y : ℂ) ^ (1 - ρ) / (1 - ρ) +
        2 * reflectedCompletedLambda (ρ - 1) * deriv reflectedCompletedLambda ρ := by
  have hupper : ∀ {w : ℂ}, reflectedCompletedLambda w = 0 → 0 < w.re → w.re < 1 → 0 < w.im →
      truncatedPairing Y (resonantParameter w) (resonantParameter w) =
        reflectedCompletedLambda (w - 1) ^ 2 * (Y : ℂ) ^ (1 - w) / (1 - w) +
          2 * reflectedCompletedLambda (w - 1) * deriv reflectedCompletedLambda w := by
    intro w hw h0w h1w himw
    set u := resonantParameter w
    have hu : u ∈ eisensteinLineDomain := resonantParameter_mem h0w himw
    rw [truncatedPairing_diag hu hY]
    unfold msDiag
    have hAu : msA u = 0 := by rw [msA_resonantParameter]; exact hw
    have hBu : msB u = reflectedCompletedLambda (w - 1) := msB_resonantParameter w
    have h12u : 1 + 2 * u = w := by simp only [u, resonantParameter]; ring
    have hneg2u : -u - u = 1 - w := by simp only [u, resonantParameter]; ring
    have h2u : 2 * u = -(1 - w) := by simp only [u, resonantParameter]; ring
    have huu : u + u = -(1 - w) := by simp only [u, resonantParameter]; ring
    have h1w_ne : 1 - w ≠ 0 := by
      intro hc
      have hre := congrArg Complex.re hc
      simp at hre
      linarith
    rw [hAu, hBu, h12u, hneg2u, huu, h2u]
    simp only [sq, zero_mul, mul_zero, neg_zero, zero_add, sub_zero]
    field_simp
    ring
  have him : ρ.im ≠ 0 := im_ne_zero_of_reflectedCompletedLambda_strip_zero hρ h0 h1
  rcases lt_or_gt_of_ne him with hneg | hpos
  · set σ := starRingEnd ℂ ρ with hσ
    have hσz : reflectedCompletedLambda σ = 0 := by
      rw [hσ, reflectedCompletedLambda_conj, hρ, map_zero]
    have hσ0 : 0 < σ.re := by simpa [hσ] using h0
    have hσ1 : σ.re < 1 := by simpa [hσ] using h1
    have hσpos : 0 < σ.im := by simp [hσ]; linarith
    have hdiag := hupper hσz hσ0 hσ1 hσpos
    have hρσ : ρ = starRingEnd ℂ σ := by rw [hσ, Complex.conj_conj]
    have hYpos : 0 < Y := by linarith
    rw [hρσ, resonantParameter_conj_eq, truncatedPairing_conj_both, hdiag]
    simp only [map_add, map_div₀, map_mul, map_pow, map_sub, map_one, map_ofNat]
    rw [← reflectedCompletedLambda_conj, conj_cpow_of_pos hYpos,
      ← deriv_reflectedCompletedLambda_conj hσpos.ne']
    simp only [map_sub, map_one]
  · exact hupper hρ h0 h1 hpos

/-- The `Y`-independent constant term `2 Λ(ρ − 1) Λ'(ρ)` in the bilinear self-pairing vanishes if
and only if `Λ'(ρ) = 0` (i.e. `ρ` is a multiple zero). -/
theorem bilinearDiagConstant_eq_zero_iff_deriv_eq_zero {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    2 * reflectedCompletedLambda (ρ - 1) * deriv reflectedCompletedLambda ρ = 0 ↔
      deriv reflectedCompletedLambda ρ = 0 := by
  have him : ρ.im ≠ 0 := im_ne_zero_of_reflectedCompletedLambda_strip_zero hρ h0 h1
  have hne : 2 * reflectedCompletedLambda (ρ - 1) ≠ 0 :=
    mul_ne_zero two_ne_zero (reflectedCompletedLambda_sub_one_ne_zero h1 him)
  exact mul_eq_zero_iff_left hne

/-- **Full bilateral strip Gram matrix and Kronecker multiplicity defect.** For *any* two strip
zeros `ρ₁, ρ₂` of `Λ` (`0 < Re ρ_j < 1`, arbitrary signs of `Im ρ₁, Im ρ₂ ≠ 0`) and every `Y ≥ 1`,
`⟨Λ^Y E_{u(ρ₁)}, Λ^Y E_{u(ρ₂)}⟩` equals the universal Cauchy–Szegő kernel plus the Kronecker delta
multiplicity residue `2 Λ(ρ₁ − 1) Λ'(ρ₁) δ_{ρ₂, conj ρ₁}`. -/
theorem hermitianPairing_resonantState_all {ρ₁ ρ₂ : ℂ}
    (hρ₁ : reflectedCompletedLambda ρ₁ = 0) (h0₁ : 0 < ρ₁.re) (h1₁ : ρ₁.re < 1)
    (hρ₂ : reflectedCompletedLambda ρ₂ = 0) (h0₂ : 0 < ρ₂.re) (h1₂ : ρ₂.re < 1)
    {Y : ℝ} (hY : 1 ≤ Y) :
    hermitianPairing Y (resonantParameter ρ₁) (resonantParameter ρ₂) =
      2 * reflectedCompletedLambda (ρ₁ - 1) * starRingEnd ℂ (reflectedCompletedLambda (ρ₂ - 1)) *
        (Y : ℂ) ^ (1 - (ρ₁ + starRingEnd ℂ ρ₂) / 2) / (2 - ρ₁ - starRingEnd ℂ ρ₂) +
      if ρ₂ = starRingEnd ℂ ρ₁ then
        2 * reflectedCompletedLambda (ρ₁ - 1) * deriv reflectedCompletedLambda ρ₁
      else 0 := by
  -- First prove for `Im ρ₁ > 0` and arbitrary `ρ₂` (`Im ρ₂ > 0` or `Im ρ₂ < 0`)
  have hpos_left : ∀ {w₁ w₂ : ℂ},
      reflectedCompletedLambda w₁ = 0 → 0 < w₁.re → w₁.re < 1 → 0 < w₁.im →
      reflectedCompletedLambda w₂ = 0 → 0 < w₂.re → w₂.re < 1 →
      hermitianPairing Y (resonantParameter w₁) (resonantParameter w₂) =
        2 * reflectedCompletedLambda (w₁ - 1) * starRingEnd ℂ (reflectedCompletedLambda (w₂ - 1)) *
          (Y : ℂ) ^ (1 - (w₁ + starRingEnd ℂ w₂) / 2) / (2 - w₁ - starRingEnd ℂ w₂) +
        if w₂ = starRingEnd ℂ w₁ then
          2 * reflectedCompletedLambda (w₁ - 1) * deriv reflectedCompletedLambda w₁
        else 0 := by
    intro w₁ w₂ hw₁ h0w₁ h1w₁ himw₁ hw₂ h0w₂ h1w₂
    have himw₂ : w₂.im ≠ 0 := im_ne_zero_of_reflectedCompletedLambda_strip_zero hw₂ h0w₂ h1w₂
    rcases lt_or_gt_of_ne himw₂ with hneg₂ | hpos₂
    · -- Opposite-hemisphere case: `Im w₁ > 0` and `Im w₂ < 0`
      set σ₂ := starRingEnd ℂ w₂ with hσ₂
      have hσ₂z : reflectedCompletedLambda σ₂ = 0 := by
        rw [hσ₂, reflectedCompletedLambda_conj, hw₂, map_zero]
      have hσ₂0 : 0 < σ₂.re := by simpa [hσ₂] using h0w₂
      have hσ₂1 : σ₂.re < 1 := by simpa [hσ₂] using h1w₂
      have hσ₂pos : 0 < σ₂.im := by simp [hσ₂]; linarith
      have hherm : hermitianPairing Y (resonantParameter w₁) (resonantParameter w₂) =
          truncatedPairing Y (resonantParameter w₁) (resonantParameter σ₂) := by
        unfold hermitianPairing truncatedPairing
        refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
        rw [truncatedLineModel_conj, ← resonantParameter_conj_eq]
      rw [hherm]
      by_cases heq : w₂ = starRingEnd ℂ w₁
      · -- Conjugate-pair resonance: `w₂ = conj w₁`, i.e. `σ₂ = w₁`
        have hσ₂_eq : σ₂ = w₁ := by rw [hσ₂, heq, Complex.conj_conj]
        rw [if_pos heq, hσ₂_eq, truncatedPairing_diag_resonantState hw₁ h0w₁ h1w₁ hY]
        congr 1
        have hconj_lam : starRingEnd ℂ (reflectedCompletedLambda (w₂ - 1)) =
            reflectedCompletedLambda (w₁ - 1) := by
          rw [← reflectedCompletedLambda_conj, map_sub, map_one, ← hσ₂, hσ₂_eq]
        have h1w₁_ne : 1 - w₁ ≠ 0 := by
          intro hc
          have hre := congrArg Complex.re hc
          simp at hre
          linarith
        have hden : 2 - w₁ - w₁ = 2 * (1 - w₁) := by ring
        have hexp : 1 - (w₁ + w₁) / 2 = 1 - w₁ := by ring
        rw [hconj_lam, hexp, hden]
        field_simp
      · -- Distinct opposite-hemisphere pair: `σ₂ ≠ w₁`
        rw [if_neg heq, add_zero]
        have hσ₂_ne : σ₂ ≠ w₁ := fun hc => heq (by rw [← hc, hσ₂, Complex.conj_conj])
        set u₁ := resonantParameter w₁
        set v₂ := resonantParameter σ₂
        have hu₁ : u₁ ∈ eisensteinLineDomain := resonantParameter_mem h0w₁ himw₁
        have hv₂ : v₂ ∈ eisensteinLineDomain := resonantParameter_mem hσ₂0 hσ₂pos
        have hms := maassSelberg_lineModel hu₁ hv₂ hY
        have hAu₁ : msA u₁ = 0 := by rw [msA_resonantParameter]; exact hw₁
        have hAv₂ : msA v₂ = 0 := by rw [msA_resonantParameter]; exact hσ₂z
        have hBu₁ : msB u₁ = reflectedCompletedLambda (w₁ - 1) := msB_resonantParameter w₁
        have hBv₂ : msB v₂ = starRingEnd ℂ (reflectedCompletedLambda (w₂ - 1)) := by
          rw [msB_resonantParameter, ← reflectedCompletedLambda_conj]
          simp [hσ₂]
        have hsub_ne : u₁ - v₂ ≠ 0 := by
          intro hc
          have : w₁ - σ₂ = 0 := by
            simp only [u₁, v₂, resonantParameter] at hc
            linear_combination 2 * hc
          exact hσ₂_ne (sub_eq_zero.mp this).symm
        have hadd : u₁ + v₂ = -(2 - w₁ - starRingEnd ℂ w₂) / 2 := by
          simp only [u₁, v₂, hσ₂, resonantParameter]
          ring
        have hexp : -u₁ - v₂ = 1 - (w₁ + starRingEnd ℂ w₂) / 2 := by
          simp only [u₁, v₂, hσ₂, resonantParameter]
          ring
        have hden_ne : 2 - w₁ - starRingEnd ℂ w₂ ≠ 0 := two_sub_add_conj_ne_zero h1w₁ h1w₂
        unfold msRight at hms
        rw [hAu₁, hAv₂, hBu₁, hBv₂, hexp] at hms
        simp only [zero_mul, mul_zero, sub_self, zero_add, zero_sub] at hms
        have hcancel : (u₁ + v₂) * truncatedPairing Y u₁ v₂ =
            -(reflectedCompletedLambda (w₁ - 1) *
              starRingEnd ℂ (reflectedCompletedLambda (w₂ - 1)) *
              (Y : ℂ) ^ (1 - (w₁ + starRingEnd ℂ w₂) / 2)) := by
          refine mul_left_cancel₀ hsub_ne ?_
          linear_combination hms
        rw [hadd] at hcancel
        rw [eq_div_iff hden_ne]
        linear_combination -2 * hcancel
    · -- Same-hemisphere upper case: `Im w₁ > 0` and `Im w₂ > 0`
      have hne_conj : w₂ ≠ starRingEnd ℂ w₁ := by
        intro hc
        have him := congrArg Complex.im hc
        simp only [Complex.conj_im] at him
        linarith
      rw [if_neg hne_conj, add_zero]
      exact hermitianPairing_resonantState_upper hw₁ h0w₁ h1w₁ himw₁ hw₂ h0w₂ h1w₂ hpos₂ hY
  -- Deduce `Im ρ₁ < 0` from `hpos_left` by simultaneous conjugation of `(ρ₁, ρ₂)`
  have him₁ : ρ₁.im ≠ 0 := im_ne_zero_of_reflectedCompletedLambda_strip_zero hρ₁ h0₁ h1₁
  rcases lt_or_gt_of_ne him₁ with hneg₁ | hpos₁
  · set σ₁ := starRingEnd ℂ ρ₁ with hσ₁
    set σ₂ := starRingEnd ℂ ρ₂ with hσ₂
    have hσ₁z : reflectedCompletedLambda σ₁ = 0 := by
      rw [hσ₁, reflectedCompletedLambda_conj, hρ₁, map_zero]
    have hσ₂z : reflectedCompletedLambda σ₂ = 0 := by
      rw [hσ₂, reflectedCompletedLambda_conj, hρ₂, map_zero]
    have hσ₁0 : 0 < σ₁.re := by simpa [hσ₁] using h0₁
    have hσ₁1 : σ₁.re < 1 := by simpa [hσ₁] using h1₁
    have hσ₁pos : 0 < σ₁.im := by simp [hσ₁]; linarith
    have hσ₂0 : 0 < σ₂.re := by simpa [hσ₂] using h0₂
    have hσ₂1 : σ₂.re < 1 := by simpa [hσ₂] using h1₂
    have hmain := hpos_left hσ₁z hσ₁0 hσ₁1 hσ₁pos hσ₂z hσ₂0 hσ₂1
    have hρ₁σ : ρ₁ = starRingEnd ℂ σ₁ := by rw [hσ₁, Complex.conj_conj]
    have hρ₂σ : ρ₂ = starRingEnd ℂ σ₂ := by rw [hσ₂, Complex.conj_conj]
    have hYpos : 0 < Y := by linarith
    rw [hρ₁σ, hρ₂σ, resonantParameter_conj_eq σ₁, resonantParameter_conj_eq σ₂,
      hermitianPairing_conj_both, hmain]
    have hcond : (starRingEnd ℂ σ₂ = σ₁) ↔ (σ₂ = starRingEnd ℂ σ₁) :=
      ⟨fun hc => by rw [← hc, Complex.conj_conj], fun hc => by rw [hc, Complex.conj_conj]⟩
    rw [map_add, map_div₀, map_mul, map_mul, map_mul, map_ofNat, Complex.conj_conj,
      ← reflectedCompletedLambda_conj, ← reflectedCompletedLambda_conj, conj_cpow_of_pos hYpos]
    simp only [map_sub, map_add, map_div₀, map_one, map_ofNat, Complex.conj_conj]
    congr 1
    by_cases hc : σ₂ = starRingEnd ℂ σ₁
    · rw [if_pos hc, if_pos (hcond.mpr hc), map_mul, map_mul, map_ofNat,
        ← reflectedCompletedLambda_conj, ← deriv_reflectedCompletedLambda_conj hσ₁pos.ne',
        map_sub, map_one]
    · rw [if_neg hc, if_neg (fun h => hc (hcond.mp h)), map_zero]
  · exact hpos_left hρ₁ h0₁ h1₁ hpos₁ hρ₂ h0₂ h1₂

/-! ### Half-line Laplace Gram isometric representation -/

/-- The Laplace exponential wavepacket on `(0, ∞)` associated to a finite family `S` of upper-strip
zeros of `Λ` at truncation height `Y`:
`P(t) = Σ_{ρ ∈ S} c(ρ) Λ(ρ − 1) Y^{(1 − ρ)/2} exp(−t (1 − ρ)/2)`. -/
def resonantLaplacePacket (Y : ℝ) (S : Finset ℂ) (c : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∑ ρ ∈ S, c ρ * reflectedCompletedLambda (ρ - 1) * (Y : ℂ) ^ ((1 - ρ) / 2) *
    Complex.exp (-(((1 - ρ) / 2) * (t : ℂ)))

/-- Entrywise Laplace integral representation of the upper-strip resonant Hermitian pairing. -/
theorem hermitianPairing_resonantState_upper_eq_laplace_integral {ρ₁ ρ₂ : ℂ}
    (hρ₁ : reflectedCompletedLambda ρ₁ = 0) (h0₁ : 0 < ρ₁.re) (h1₁ : ρ₁.re < 1) (him₁ : 0 < ρ₁.im)
    (hρ₂ : reflectedCompletedLambda ρ₂ = 0) (h0₂ : 0 < ρ₂.re) (h1₂ : ρ₂.re < 1) (him₂ : 0 < ρ₂.im)
    {Y : ℝ} (hY : 1 ≤ Y) :
    hermitianPairing Y (resonantParameter ρ₂) (resonantParameter ρ₁) =
      ∫ t in Ioi (0 : ℝ),
        (reflectedCompletedLambda (ρ₂ - 1) * (Y : ℂ) ^ ((1 - ρ₂) / 2) *
          Complex.exp (-(((1 - ρ₂) / 2) * (t : ℂ)))) *
        starRingEnd ℂ
          (reflectedCompletedLambda (ρ₁ - 1) * (Y : ℂ) ^ ((1 - ρ₁) / 2) *
            Complex.exp (-(((1 - ρ₁) / 2) * (t : ℂ)))) := by
  have hYpos : 0 < Y := by linarith
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hYpos.ne'
  set z : ℂ := 1 - (ρ₂ + starRingEnd ℂ ρ₁) / 2 with hz_def
  have hz_re : 0 < z.re := by
    simp only [hz_def, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.add_re,
      Complex.conj_re]
    linarith
  have hpt : ∀ t : ℝ,
      (reflectedCompletedLambda (ρ₂ - 1) * (Y : ℂ) ^ ((1 - ρ₂) / 2) *
        Complex.exp (-(((1 - ρ₂) / 2) * (t : ℂ)))) *
      starRingEnd ℂ
        (reflectedCompletedLambda (ρ₁ - 1) * (Y : ℂ) ^ ((1 - ρ₁) / 2) *
          Complex.exp (-(((1 - ρ₁) / 2) * (t : ℂ)))) =
      (reflectedCompletedLambda (ρ₂ - 1) * starRingEnd ℂ (reflectedCompletedLambda (ρ₁ - 1)) *
        (Y : ℂ) ^ z) * Complex.exp (-(z * (t : ℂ))) := by
    intro t
    rw [map_mul, map_mul, conj_cpow_of_pos hYpos, ← Complex.exp_conj]
    have hYadd : (Y : ℂ) ^ ((1 - ρ₂) / 2) * (Y : ℂ) ^ (starRingEnd ℂ ((1 - ρ₁) / 2)) =
        (Y : ℂ) ^ z := by
      rw [← Complex.cpow_add _ _ hYne]
      congr 1
      simp only [hz_def, map_div₀, map_sub, map_one, map_ofNat]
      ring
    have hexp_conj : starRingEnd ℂ (-(((1 - ρ₁) / 2) * (t : ℂ))) =
        -(((1 - starRingEnd ℂ ρ₁) / 2) * (t : ℂ)) := by
      simp only [map_neg, map_mul, map_div₀, map_sub, map_one, map_ofNat, Complex.conj_ofReal]
    rw [hexp_conj]
    calc (reflectedCompletedLambda (ρ₂ - 1) * (Y : ℂ) ^ ((1 - ρ₂) / 2) *
            Complex.exp (-(((1 - ρ₂) / 2) * (t : ℂ)))) *
          (starRingEnd ℂ (reflectedCompletedLambda (ρ₁ - 1)) *
            (Y : ℂ) ^ (starRingEnd ℂ ((1 - ρ₁) / 2)) *
            Complex.exp (-(((1 - starRingEnd ℂ ρ₁) / 2) * (t : ℂ))))
        = (reflectedCompletedLambda (ρ₂ - 1) * starRingEnd ℂ (reflectedCompletedLambda (ρ₁ - 1)) *
            ((Y : ℂ) ^ ((1 - ρ₂) / 2) * (Y : ℂ) ^ (starRingEnd ℂ ((1 - ρ₁) / 2)))) *
          (Complex.exp (-(((1 - ρ₂) / 2) * (t : ℂ))) *
            Complex.exp (-(((1 - starRingEnd ℂ ρ₁) / 2) * (t : ℂ)))) := by ring
      _ = (reflectedCompletedLambda (ρ₂ - 1) * starRingEnd ℂ (reflectedCompletedLambda (ρ₁ - 1)) *
            (Y : ℂ) ^ z) * Complex.exp (-(z * (t : ℂ))) := by
            rw [hYadd, ← Complex.exp_add]
            congr 2
            simp only [hz_def]
            ring
  simp_rw [hpt]
  rw [integral_const_mul, GaloisForLFunctions.HTGeometry.integral_cexp_neg_mul hz_re,
    hermitianPairing_resonantState_upper hρ₂ h0₂ h1₂ him₂ hρ₁ h0₁ h1₁ him₁ hY, ← hz_def]
  have hz_den : 2 - ρ₂ - starRingEnd ℂ ρ₁ = 2 * z := by
    simp only [hz_def]; ring
  have hz_ne : z ≠ 0 := by
    intro hc; rw [hc] at hz_re; simp at hz_re
  rw [hz_den]
  field_simp

/-- **Laplace Gram isometric representation.** For any finite set `S` of upper-strip zeros of `Λ`,
complex weights `c : ℂ → ℂ`, and truncation height `Y ≥ 1`, the `S × S` Hermitian Gram quadratic
form of the truncated resonant states equals `∫_0^∞ ‖resonantLaplacePacket Y S c t‖² dt`. -/
theorem resonantGramQuadraticForm_upper_eq_laplace_normSq
    {S : Finset ℂ}
    (hS : ∀ ρ ∈ S, reflectedCompletedLambda ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im)
    (c : ℂ → ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S,
      starRingEnd ℂ (c ρ₁) * c ρ₂ *
        hermitianPairing Y (resonantParameter ρ₂) (resonantParameter ρ₁)) =
      ((∫ t in Ioi (0 : ℝ), ‖resonantLaplacePacket Y S c t‖ ^ 2 : ℝ) : ℂ) := by
  set atom : ℂ → ℝ → ℂ := fun ρ t =>
    reflectedCompletedLambda (ρ - 1) * (Y : ℂ) ^ ((1 - ρ) / 2) *
      Complex.exp (-(((1 - ρ) / 2) * (t : ℂ))) with hatom
  have hint_pair : ∀ ρ₁ ∈ S, ∀ ρ₂ ∈ S,
      IntegrableOn (fun t : ℝ =>
        starRingEnd ℂ (c ρ₁) * c ρ₂ * (atom ρ₂ t * starRingEnd ℂ (atom ρ₁ t)))
        (Ioi (0 : ℝ)) := by
    intro ρ₁ hρ₁S ρ₂ hρ₂S
    obtain ⟨_, _, h1₁, _⟩ := hS ρ₁ hρ₁S
    obtain ⟨_, _, h1₂, _⟩ := hS ρ₂ hρ₂S
    have hYpos : 0 < Y := by linarith
    have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hYpos.ne'
    set z : ℂ := 1 - (ρ₂ + starRingEnd ℂ ρ₁) / 2 with hz_def
    have hz_re : 0 < z.re := by
      simp only [hz_def, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.add_re,
        Complex.conj_re]
      linarith
    have hcongr : (fun t : ℝ =>
        starRingEnd ℂ (c ρ₁) * c ρ₂ * (atom ρ₂ t * starRingEnd ℂ (atom ρ₁ t))) =
        fun t : ℝ => (starRingEnd ℂ (c ρ₁) * c ρ₂ *
          (reflectedCompletedLambda (ρ₂ - 1) * starRingEnd ℂ (reflectedCompletedLambda (ρ₁ - 1)) *
            (Y : ℂ) ^ z)) * Complex.exp (-(z * (t : ℂ))) := by
      funext t
      simp only [hatom]
      rw [map_mul, map_mul, conj_cpow_of_pos hYpos, ← Complex.exp_conj]
      have hYadd : (Y : ℂ) ^ ((1 - ρ₂) / 2) * (Y : ℂ) ^ (starRingEnd ℂ ((1 - ρ₁) / 2)) =
          (Y : ℂ) ^ z := by
        rw [← Complex.cpow_add _ _ hYne]
        congr 1
        simp only [hz_def, map_div₀, map_sub, map_one, map_ofNat]
        ring
      have hexp_conj : starRingEnd ℂ (-(((1 - ρ₁) / 2) * (t : ℂ))) =
          -(((1 - starRingEnd ℂ ρ₁) / 2) * (t : ℂ)) := by
        simp only [map_neg, map_mul, map_div₀, map_sub, map_one, map_ofNat, Complex.conj_ofReal]
      rw [hexp_conj]
      have hexp_add : Complex.exp (-(((1 - ρ₂) / 2) * (t : ℂ))) *
          Complex.exp (-(((1 - starRingEnd ℂ ρ₁) / 2) * (t : ℂ))) =
          Complex.exp (-(z * (t : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        simp only [hz_def]
        ring
      calc starRingEnd ℂ (c ρ₁) * c ρ₂ *
            ((reflectedCompletedLambda (ρ₂ - 1) * (Y : ℂ) ^ ((1 - ρ₂) / 2) *
                Complex.exp (-(((1 - ρ₂) / 2) * (t : ℂ)))) *
              (starRingEnd ℂ (reflectedCompletedLambda (ρ₁ - 1)) *
                (Y : ℂ) ^ (starRingEnd ℂ ((1 - ρ₁) / 2)) *
                Complex.exp (-(((1 - starRingEnd ℂ ρ₁) / 2) * (t : ℂ)))))
          = (starRingEnd ℂ (c ρ₁) * c ρ₂ *
              (reflectedCompletedLambda (ρ₂ - 1) *
                starRingEnd ℂ (reflectedCompletedLambda (ρ₁ - 1)) *
                ((Y : ℂ) ^ ((1 - ρ₂) / 2) * (Y : ℂ) ^ (starRingEnd ℂ ((1 - ρ₁) / 2))))) *
            (Complex.exp (-(((1 - ρ₂) / 2) * (t : ℂ))) *
              Complex.exp (-(((1 - starRingEnd ℂ ρ₁) / 2) * (t : ℂ)))) := by ring
        _ = _ := by rw [hYadd, hexp_add]
    rw [hcongr]
    exact (GaloisForLFunctions.HTGeometry.integrableOn_cexp_neg_mul hz_re).const_mul _
  have hentry : ∀ ρ₁ ∈ S, ∀ ρ₂ ∈ S,
      starRingEnd ℂ (c ρ₁) * c ρ₂ *
        hermitianPairing Y (resonantParameter ρ₂) (resonantParameter ρ₁) =
      ∫ t in Ioi (0 : ℝ),
        starRingEnd ℂ (c ρ₁) * c ρ₂ * (atom ρ₂ t * starRingEnd ℂ (atom ρ₁ t)) := by
    intro ρ₁ hρ₁S ρ₂ hρ₂S
    obtain ⟨hρ₁, h0₁, h1₁, him₁⟩ := hS ρ₁ hρ₁S
    obtain ⟨hρ₂, h0₂, h1₂, him₂⟩ := hS ρ₂ hρ₂S
    rw [hermitianPairing_resonantState_upper_eq_laplace_integral
      hρ₁ h0₁ h1₁ him₁ hρ₂ h0₂ h1₂ him₂ hY, ← integral_const_mul]
  have hsum_eq : (∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S,
      starRingEnd ℂ (c ρ₁) * c ρ₂ *
        hermitianPairing Y (resonantParameter ρ₂) (resonantParameter ρ₁)) =
      ∑ ρ₁ ∈ S, ∑ ρ₂ ∈ S,
        ∫ t in Ioi (0 : ℝ),
          starRingEnd ℂ (c ρ₁) * c ρ₂ * (atom ρ₂ t * starRingEnd ℂ (atom ρ₁ t)) :=
    Finset.sum_congr rfl fun ρ₁ hρ₁ => Finset.sum_congr rfl fun ρ₂ hρ₂ => hentry ρ₁ hρ₁ ρ₂ hρ₂
  rw [hsum_eq]
  have hswap : ∀ ρ₁ ∈ S,
      (∑ ρ₂ ∈ S, ∫ t in Ioi (0 : ℝ),
        starRingEnd ℂ (c ρ₁) * c ρ₂ * (atom ρ₂ t * starRingEnd ℂ (atom ρ₁ t))) =
      ∫ t in Ioi (0 : ℝ), ∑ ρ₂ ∈ S,
        starRingEnd ℂ (c ρ₁) * c ρ₂ * (atom ρ₂ t * starRingEnd ℂ (atom ρ₁ t)) :=
    fun ρ₁ hρ₁ => (integral_finsetSum S fun ρ₂ hρ₂ => hint_pair ρ₁ hρ₁ ρ₂ hρ₂).symm
  rw [Finset.sum_congr rfl hswap, ← integral_finsetSum S fun ρ₁ hρ₁ =>
    integrable_finsetSum S fun ρ₂ hρ₂ => hint_pair ρ₁ hρ₁ ρ₂ hρ₂, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  set P : ℂ := resonantLaplacePacket Y S c t with hP
  have hP_sum : P = ∑ ρ ∈ S, c ρ * atom ρ t := by
    simp only [hP, resonantLaplacePacket, hatom, mul_assoc]
  have hP_conj : starRingEnd ℂ P = ∑ ρ ∈ S, starRingEnd ℂ (c ρ) * starRingEnd ℂ (atom ρ t) := by
    rw [hP_sum, map_sum]
    exact Finset.sum_congr rfl fun ρ _ => map_mul (starRingEnd ℂ) (c ρ) (atom ρ t)
  have hnormP : ((‖P‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ P * P := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm]
  rw [hnormP, hP_conj, hP_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ₁ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ₂ _ => by ring

end

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
