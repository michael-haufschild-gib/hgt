import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

open Complex Set
noncomputable section
namespace RHTower

private theorem stationary_log_linear_error {a x : ℝ} (ha : 0 < a)
    (hx : |x - a| ≤ a / 2) :
    |Real.log (x / a) - (x - a) / a| ≤ 2 * |x - a| ^ 2 / a ^ 2 := by
  have hxlo := (abs_le.mp hx).1
  have hx0 : 0 < x := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hx0 ha)
  have hu := Real.log_le_sub_one_of_pos (div_pos hx0 ha)
  have he : x / a - 1 = (x - a) / a := by field_simp
  rw [he] at hu
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  have hfrac : a / x ≤ 2 := (div_le_iff₀ hx0).mpr (by linarith)
  have he' : (x - a) / a - (1 - (x / a)⁻¹) =
      (|x - a| ^ 2 / a ^ 2) * (a / x) := by
    rw [sq_abs]
    field_simp
  calc
    _ ≤ (x - a) / a - (1 - (x / a)⁻¹) := by linarith
    _ = (|x - a| ^ 2 / a ^ 2) * (a / x) := he'
    _ ≤ (|x - a| ^ 2 / a ^ 2) * 2 := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = _ := by ring

/-- A uniform cubic remainder for the actual conductor saddle entropy.
It remains valid on both sides of the stationary point. -/
theorem abs_stationary_entropy_sub_quadratic_le {a t : ℝ} (ha : 0 < a)
    (ht : |t - a| ≤ a / 2) :
    |t * Real.log (t / a) - t + a - (t - a) ^ 2 / (2 * a)| ≤
      2 * |t - a| ^ 3 / a ^ 2 := by
  let r : ℝ := |t - a|
  let f : ℝ → ℝ := fun x => x * (Real.log x - Real.log a) - x + a - (x - a) ^ 2 / (2 * a)
  let f' : ℝ → ℝ := fun x => Real.log x - Real.log a - (x - a) / a
  have hr : 0 ≤ r := abs_nonneg _
  have hrhalf : r ≤ a / 2 := ht
  have hxa (x : ℝ) (hx : x ∈ Icc (a - r) (a + r)) : |x - a| ≤ a / 2 :=
    (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans hrhalf
  have hxpos (x : ℝ) (hx : x ∈ Icc (a - r) (a + r)) : 0 < x := by
    linarith [hx.1]
  have hd (x : ℝ) (hx : x ∈ Icc (a - r) (a + r)) : HasDerivAt f (f' x) x := by
    have hx0 := hxpos x hx
    have h := ((((hasDerivAt_id x).mul ((Real.hasDerivAt_log hx0.ne').sub_const (Real.log a))).sub
      (hasDerivAt_id x)).add_const a).sub
        ((((hasDerivAt_id x).sub_const a).pow 2).div_const (2 * a))
    apply h.congr_deriv
    dsimp only [f', id]
    field_simp
    ring
  have hb (x : ℝ) (hx : x ∈ Icc (a - r) (a + r)) : ‖f' x‖ ≤ 2 * r ^ 2 / a ^ 2 := by
    have hx0 := hxpos x hx
    have h := stationary_log_linear_error ha (hxa x hx)
    rw [Real.log_div hx0.ne' ha.ne'] at h
    change |Real.log x - Real.log a - (x - a) / a| ≤ _
    apply h.trans
    have hxr : |x - a| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    gcongr
  have haa : a ∈ Icc (a - r) (a + r) := ⟨by linarith, by linarith⟩
  have hta : t ∈ Icc (a - r) (a + r) := by
    have h := abs_le.mp (le_refl |t - a|)
    exact ⟨by dsimp [r]; linarith [h.1], by dsimp [r]; linarith [h.2]⟩
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt) hb (convex_Icc (a - r) (a + r)) haa hta
  have hf : f a = 0 := by simp [f]
  rw [hf, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hm
  have ht0 := hxpos t hta
  rw [Real.log_div ht0.ne' ha.ne']
  calc
    _ ≤ (2 * r ^ 2 / a ^ 2) * |t - a| := hm
    _ = _ := by dsimp only [r]; ring

end RHTower
