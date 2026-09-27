import GaloisForLFunctions.RHTower.CCMFiniteLocalizationChain

/-!
# One bounded weight for an entire localization chain

The overlap of the successive sine channels and final cosine remainder is a
unit-vector correlation. Its absolute value is at most one. Consequently the
combined localization weight lies in [0,4], independently of chain length.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace RHTower

def thetaLocalizationChainOverlap : List 𝓢(ℝ, ℝ) → ℝ → ℝ → ℝ
  | [], _, _ => 1
  | theta :: rest, x, y => Real.sin (theta x) * Real.sin (theta y) +
      Real.cos (theta x) * Real.cos (theta y) * thetaLocalizationChainOverlap rest x y

def thetaLocalizationChainWeight (angles : List 𝓢(ℝ, ℝ)) (x y : ℝ) : ℝ :=
  2 * (1 - thetaLocalizationChainOverlap angles x y)

private theorem abs_circle_overlap_le_one (s t k : ℝ) (hk : |k| ≤ 1) :
    |Real.sin s * Real.sin t + Real.cos s * Real.cos t * k| ≤ 1 := by
  have hk2 : k ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one k).mpr hk
  have hprod := mul_nonneg (sq_nonneg (Real.cos t)) (sub_nonneg.mpr hk2)
  have hunit : (Real.sin s ^ 2 + Real.cos s ^ 2) *
      (Real.sin t ^ 2 + Real.cos t ^ 2 * k ^ 2) ≤ 1 := by
    rw [Real.sin_sq_add_cos_sq, one_mul]
    nlinarith only [hprod, Real.sin_sq_add_cos_sq t]
  have hid : (Real.sin s * Real.sin t + Real.cos s * Real.cos t * k) ^ 2 +
      (Real.sin s * Real.cos t * k - Real.cos s * Real.sin t) ^ 2 =
      (Real.sin s ^ 2 + Real.cos s ^ 2) *
        (Real.sin t ^ 2 + Real.cos t ^ 2 * k ^ 2) := by ring
  apply (sq_le_one_iff_abs_le_one _).mp
  nlinarith only [hid, hunit, sq_nonneg
    (Real.sin s * Real.cos t * k - Real.cos s * Real.sin t)]

theorem abs_thetaLocalizationChainOverlap_le_one (angles : List 𝓢(ℝ, ℝ)) (x y : ℝ) :
    |thetaLocalizationChainOverlap angles x y| ≤ 1 := by
  induction angles with
  | nil => simp only [thetaLocalizationChainOverlap, abs_one, le_refl]
  | cons theta rest ih => exact abs_circle_overlap_le_one (theta x) (theta y) _ ih

theorem thetaLocalizationChainWeight_nonneg (angles : List 𝓢(ℝ, ℝ)) (x y : ℝ) :
    0 ≤ thetaLocalizationChainWeight angles x y := by
  have h := (abs_le.mp (abs_thetaLocalizationChainOverlap_le_one angles x y)).2
  unfold thetaLocalizationChainWeight
  linarith only [h]

theorem thetaLocalizationChainWeight_le_four (angles : List 𝓢(ℝ, ℝ)) (x y : ℝ) :
    thetaLocalizationChainWeight angles x y ≤ 4 := by
  have h := (abs_le.mp (abs_thetaLocalizationChainOverlap_le_one angles x y)).1
  unfold thetaLocalizationChainWeight
  linarith only [h]

theorem thetaLocalizationChainWeight_cons (theta : 𝓢(ℝ, ℝ))
    (rest : List 𝓢(ℝ, ℝ)) (x y : ℝ) :
    thetaLocalizationChainWeight (theta :: rest) x y = thetaLocalizationWeight theta x y +
      Real.cos (theta x) * Real.cos (theta y) * thetaLocalizationChainWeight rest x y := by
  rw [thetaLocalizationWeight_eq_cos, Real.cos_sub]
  simp only [thetaLocalizationChainWeight, thetaLocalizationChainOverlap]
  ring

theorem ccmCosLocalizedSource_correlation {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (x y : ℝ) :
    (ccmCosLocalizedSource u theta y * star (ccmCosLocalizedSource u theta x)).re =
      Real.cos (theta x) * Real.cos (theta y) * (u y * star (u x)).re := by
  simp only [ccmCosLocalizedSource_apply, Complex.star_def, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero]
  ring

theorem ccmSinLocalizedSource_correlation {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (x y : ℝ) :
    (ccmSinLocalizedSource u theta y * star (ccmSinLocalizedSource u theta x)).re =
      Real.sin (theta x) * Real.sin (theta y) * (u y * star (u x)).re := by
  simp only [ccmSinLocalizedSource_apply, Complex.star_def, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero]
  ring

theorem ccmLocalization_correlation_conservation {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (x y : ℝ) :
    (ccmLocalizationRemainder u angles y * star (ccmLocalizationRemainder u angles x)).re +
      ((ccmLocalizationPieces u angles).map (fun v => (v y * star (v x)).re)).sum =
      thetaLocalizationChainOverlap angles x y * (u y * star (u x)).re := by
  induction angles generalizing u with
  | nil => simp only [ccmLocalizationRemainder, ccmLocalizationPieces,
      thetaLocalizationChainOverlap, List.map_nil, List.sum_nil, add_zero, one_mul]
  | cons theta rest ih =>
    have h := ih (ccmCosLocalizedSource u theta)
    rw [ccmCosLocalizedSource_correlation] at h
    simp only [ccmLocalizationRemainder, ccmLocalizationPieces, List.map_cons, List.sum_cons,
      ccmSinLocalizedSource_correlation, thetaLocalizationChainOverlap]
    nlinarith only [h]

end RHTower
