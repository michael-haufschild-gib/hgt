import GaloisForLFunctions.RHTower.CHMDArchimedeanLevyTranslateForm

/-!
# Quadratic control of increments of the archimedean density

The two exponential factors in the Levy density have elementary increment
bounds. Separating their numerator and denominator variations gives a global
inverse-square bound, suitable for summing errors along logarithmic atom rows.
-/

noncomputable section

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open _root_.RHTower

private theorem exp_neg_sub_le (a b : ℝ) :
    Real.exp (-a) - Real.exp (-b) ≤ (b - a) * Real.exp (-a) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a - b))
    (Real.exp_pos (-a)).le
  have he : Real.exp (-a) * Real.exp (a - b) = Real.exp (-b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  nlinarith only [h]

/-- The squared denominator pays the exponentially damped inverse-square term. -/
private theorem sq_mul_exp_neg_two_le {a : ℝ} (ha : 0 < a) :
    a ^ 2 * Real.exp (-2 * a) ≤ (1 - Real.exp (-2 * a)) ^ 2 := by
  have hz : 0 < Real.exp (-a) := Real.exp_pos _
  have hz1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hadd := Real.add_one_le_exp a
  have hex : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
  have hzsq : Real.exp (-a) ^ 2 = Real.exp (-2 * a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hlin : a * Real.exp (-a) ≤ 1 - Real.exp (-2 * a) := by
    have h := mul_le_mul_of_nonneg_right
      (show a ≤ Real.exp a - Real.exp (-a) by linarith only [hadd, hz1]) hz.le
    nlinarith only [h, hex, hzsq]
  have h0 : 0 ≤ a * Real.exp (-a) := mul_nonneg ha.le hz.le
  have hd0 : 0 ≤ 1 - Real.exp (-2 * a) := h0.trans hlin
  have hsq : (a * Real.exp (-a)) ^ 2 ≤ (1 - Real.exp (-2 * a)) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlin) (add_nonneg hd0 h0)]
  simpa only [mul_pow, hzsq] using hsq

/-- A global inverse-square increment bound for the literal Levy density. -/
theorem archLevyDensity_sub_le_quadratic {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    archLevyDensity a - archLevyDensity b ≤ 19 * (b - a) / a ^ 2 := by
  let u := Real.exp (-a / 2)
  let v := Real.exp (-b / 2)
  let q := Real.exp (-2 * a)
  let r := Real.exp (-2 * b)
  let D := 1 - q
  let E := 1 - r
  have hb : 0 < b := ha.trans_le hab
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hu : 0 < u := Real.exp_pos _
  have hv : 0 < v := Real.exp_pos _
  have hv1 : v ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hb])
  have hq : 0 < q := Real.exp_pos _
  have hrq : r ≤ q := Real.exp_le_exp.mpr (by linarith)
  have hD : 0 < D := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hDE : D ≤ E := by dsimp only [D, E]; linarith only [hrq]
  have hE : 0 < E := hD.trans_le hDE
  have hnum : u - v ≤ (b - a) / 2 * u := by
    have h := exp_neg_sub_le (a / 2) (b / 2)
    dsimp only [u, v]
    simpa only [neg_div, ← sub_div] using h
  have hqr : q - r ≤ 2 * (b - a) * q := by
    have h := exp_neg_sub_le (2 * a) (2 * b)
    dsimp only [q, r]
    have heq : 2 * b - 2 * a = 2 * (b - a) := by ring
    simpa only [neg_mul, heq] using h
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hqa : q * a ^ 2 ≤ D ^ 2 := by
    simpa only [q, D, mul_comm] using sq_mul_exp_neg_two_le ha
  have hfrac : q / D ^ 2 ≤ 1 / a ^ 2 := by
    rw [div_le_div_iff₀ hD2 ha2]
    simpa only [one_mul] using hqa
  have hmass : u / D ≤ 34 / a ^ 2 := by
    have h := _root_.RHTower.CHMDLightCone.archLevyDensity_mul_sq_le ha
    have he : Real.exp (-(1 / 4 : ℝ) * a) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    rw [le_div_iff₀ ha2]
    change archLevyDensity a * a ^ 2 ≤ 34
    linarith only [h, he]
  have hfirst : (u - v) / D ≤ 17 * (b - a) / a ^ 2 := by
    calc
      (u - v) / D ≤ ((b - a) / 2 * u) / D :=
        div_le_div_of_nonneg_right hnum hD.le
      _ = ((b - a) / 2) * (u / D) := by ring
      _ ≤ ((b - a) / 2) * (34 / a ^ 2) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by ring
  have hsecond : v * (q - r) / (D * E) ≤ 2 * (b - a) / a ^ 2 := by
    have hqr0 : 0 ≤ q - r := sub_nonneg.mpr hrq
    have hden : D ^ 2 ≤ D * E := by nlinarith only [hD, hDE]
    calc
      v * (q - r) / (D * E) ≤ (q - r) / (D * E) := by
        exact div_le_div_of_nonneg_right
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hv1 hqr0)
          (mul_nonneg hD.le hE.le)
      _ ≤ (2 * (b - a) * q) / (D * E) :=
        div_le_div_of_nonneg_right hqr (mul_nonneg hD.le hE.le)
      _ ≤ (2 * (b - a) * q) / D ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hD2 hden
      _ = (2 * (b - a)) * (q / D ^ 2) := by ring
      _ ≤ (2 * (b - a)) * (1 / a ^ 2) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = _ := by ring
  have heq : archLevyDensity a - archLevyDensity b =
      (u - v) / D + v * (q - r) / (D * E) := by
    change u / D - v / E = _
    field_simp [hD.ne', hE.ne']
    dsimp only [D, E]
    ring
  rw [heq]
  calc
    _ ≤ 17 * (b - a) / a ^ 2 + 2 * (b - a) / a ^ 2 := add_le_add hfirst hsecond
    _ = _ := by ring

/-- The variation across a positive pair window is linear in its width. -/
theorem archLevyDensity_window_sub_le {s w : ℝ} (hw : 0 ≤ w) (hws : w < s) :
    archLevyDensity (s - w) - archLevyDensity (s + w) ≤
      38 * w / (s - w) ^ 2 := by
  have h := archLevyDensity_sub_le_quadratic (sub_pos.mpr hws)
    (show s - w ≤ s + w by linarith)
  convert h using 1
  ring

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis

