import GaloisForLFunctions.RHTower.PolynomialFockPotentialGeometry

/-! # Clipping the tangent of a convex power -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- The slope at h of the response x ↦ x^q. -/
def tangentSlope (q h : ℝ) := q * h^(q-1)

/-- The increasing part of the tangent excess, held constant after the contact point. -/
def tangentCap (q h x : ℝ) := tangentSlope q h * min x h - (min x h)^q

private theorem slope_mono {q x y : ℝ} (hq : 1 ≤ q) (hx : 0 ≤ x) (hxy : x ≤ y) :
    tangentSlope q x ≤ tangentSlope q y :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy (sub_nonneg.mpr hq)) (zero_le_one.trans hq)

theorem tangentCap_mono {q h x y : ℝ} (hq : 1 ≤ q) (hh : 0 < h) (hx : 0 ≤ x) (hxy : x ≤ y) :
    tangentCap q h x ≤ tangentCap q h y := by
  let a := min x h
  let b := min y h
  have ha : 0 ≤ a := le_min hx hh.le
  have hab : a ≤ b := min_le_min_right h hxy
  change tangentSlope q h * a - a^q ≤ tangentSlope q h * b - b^q
  rcases eq_or_lt_of_le (ha.trans hab) with hb | hb
  · have he := le_antisymm hab (by rw [← hb]; exact ha)
    rw [he]
  · have ht := _root_.RHTower.rpow_tangent_lower hb ha hq
    change b^q + tangentSlope q b * (a-b) ≤ a^q at ht
    have hs := mul_le_mul_of_nonpos_right (slope_mono hq hb.le (min_le_right y h)) (sub_nonpos.mpr hab)
    simp only [mul_sub] at ht hs
    linarith only [ht,hs]

theorem tangentCap_zero {q h : ℝ} (hq : 1 ≤ q) (hh : 0 ≤ h) : tangentCap q h 0 = 0 := by
  simp only [tangentCap,min_eq_left hh,mul_zero,Real.zero_rpow (zero_lt_one.trans_le hq).ne',sub_self]

theorem tangentSlope_mul_self {q h : ℝ} (hh : 0 < h) : tangentSlope q h * h = q * h^q := by
  have he : h^(q-1) * h = h^q := by
    rw [← Real.rpow_add_one hh.ne',sub_add_cancel]
  rw [tangentSlope,mul_assoc,he]

theorem tangentCap_le {q h x : ℝ} (hq : 1 ≤ q) (hh : 0 < h) (hx : 0 ≤ x) :
    tangentCap q h x ≤ (q-1)*h^q := by
  have he : tangentCap q h h = (q-1)*h^q := by
    rw [tangentCap,min_self,tangentSlope_mul_self hh,sub_mul,one_mul]
  rw [← he]
  by_cases hxh : x ≤ h
  · exact tangentCap_mono hq hh hx hxh
  · simp only [tangentCap,min_eq_right (le_of_not_ge hxh),min_self,le_refl]

theorem continuous_tangentCap {q : ℝ} (hq : 1 ≤ q) (h : ℝ) : Continuous (tangentCap q h) := by
  have hc : Continuous (fun x : ℝ => min x h) := continuous_id.min continuous_const
  exact (continuous_const.mul hc).sub ((Real.continuous_rpow_const (zero_le_one.trans hq)).comp hc)

/-- Tangent deficit on any interval is paid by the change in the bounded cap. -/
theorem tangentCap_gap {q h x y : ℝ} (hq : 1 ≤ q) (hh : 0 < h) (hy : 0 ≤ y) (hyx : y ≤ x) :
    tangentSlope q h * (x-y) ≤ x^q-y^q + (tangentCap q h x-tangentCap q h y) := by
  by_cases hx : x ≤ h
  · simp only [tangentCap,min_eq_left hx,min_eq_left (hyx.trans hx)]
    rw [mul_sub]
    linarith only []
  · have hhx := le_of_not_ge hx
    by_cases hhy : h ≤ y
    · have ht := _root_.RHTower.rpow_tangent_lower (hh.trans_le hhy) (hy.trans hyx) hq
      change y^q + tangentSlope q y * (x-y) ≤ x^q at ht
      have hs := mul_le_mul_of_nonneg_right (slope_mono hq hh.le hhy) (sub_nonneg.mpr hyx)
      simp only [tangentCap,min_eq_right hhx,min_eq_right hhy,sub_self,add_zero]
      linarith only [hs,ht]
    · have ht := _root_.RHTower.rpow_tangent_lower hh (hy.trans hyx) hq
      change h^q + tangentSlope q h * (x-h) ≤ x^q at ht
      simp only [tangentCap,min_eq_right hhx,min_eq_left (le_of_not_ge hhy)]
      simp only [mul_sub] at ht ⊢
      linarith only [ht]

#print axioms tangentCap_gap
#print axioms tangentCap_mono

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
