import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection

/-! # Quantitative, invertible Cayley encoding of real sources

Reuse the native real Cayley map. Its exact difference law transports absolute
source-error budgets, while the explicit inverse retains every signed value.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex Filter
open scoped Topology

theorem paperRealCayley_denominator_norm (x : ℝ) : 1 ≤ ‖(x : ℂ) + I‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ) + I)

theorem paperRealCayley_sub (x y : ℝ) :
    realCayley x - realCayley y =
      2 * I * ((x : ℂ) - y) / (((x : ℂ) + I) * ((y : ℂ) + I)) := by
  unfold realCayley
  rw [div_sub_div _ _ (real_add_I_ne_zero x) (real_add_I_ne_zero y)]
  congr 1
  ring

theorem paperRealCayley_norm_sub_le (x y : ℝ) :
    ‖realCayley x - realCayley y‖ ≤ 2 * |x - y| := by
  rw [paperRealCayley_sub, norm_div, norm_mul, norm_mul, norm_mul, norm_I, mul_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [norm_ofNat]
  apply div_le_self (by positivity)
  nlinarith [paperRealCayley_denominator_norm x, paperRealCayley_denominator_norm y]

theorem paperRealCayley_ne_one (x : ℝ) : realCayley x ≠ 1 := by
  intro h
  have he := (div_eq_one_iff_eq (real_add_I_ne_zero x)).1 h
  have hi := congrArg Complex.im he
  norm_num at hi

/-- Explicit inverse; no sign or size information is lost at finite real sources. -/
def paperRealCayleyInverse (z : ℂ) : ℝ := (I * (1 + z) / (1 - z)).re

theorem paperRealCayleyInverse_apply (x : ℝ) :
    paperRealCayleyInverse (realCayley x) = x := by
  have hd : 1 - realCayley x ≠ 0 := sub_ne_zero.mpr (Ne.symm (paperRealCayley_ne_one x))
  have he : I * (1 + realCayley x) / (1 - realCayley x) = (x : ℂ) := by
    apply (div_eq_iff hd).2
    unfold realCayley
    field_simp [real_add_I_ne_zero x]
    ring
  exact congrArg Complex.re he

theorem paperRealCayley_neg_one : realCayley (-1) = I := by
  unfold realCayley
  apply (div_eq_iff (real_add_I_ne_zero (-1))).2
  norm_num [mul_add]
  ring

theorem paperRealCayley_sub_one (x : ℝ) :
    realCayley x - 1 = -(2 * I) / ((x : ℂ) + I) := by
  unfold realCayley
  field_simp [real_add_I_ne_zero x]
  ring

theorem paperRealCayley_tendsto_one : Tendsto realCayley atTop (𝓝 1) := by
  have hbig : Tendsto (fun x : ℝ => ‖(x : ℂ) + I‖) atTop atTop := by
    apply tendsto_atTop_mono (fun x => ?_) tendsto_id
    exact (le_abs_self x).trans (by simpa using Complex.abs_re_le_norm ((x : ℂ) + I))
  have h := hbig.inv_tendsto_atTop.const_mul 2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [paperRealCayley_sub_one, norm_div, norm_mul, div_eq_mul_inv] using h

end GaloisForLFunctions.HTGeometry
