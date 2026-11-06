import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.GaussianSaddleWindow
import GaloisForLFunctions.RHTower.KiKimLeeUniformReality

/-!
# Uniform Gaussian errors at inverse-logarithmic heat times

On `d ≤ tα ≤ 1`, the inverse heat prefactors grow at most linearly in
`α`. The distant Gaussian errors retain quadratic exponential decay.
The local model error depends only on `B√t`.
-/

open Filter Topology
open _root_.RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The scaled model error depends only on the variation across one Gaussian width. -/
theorem gaussianSaddleModelError_eq {B t : ℝ} (ht : 0 < t) :
    gaussianSaddleModelError B t =
      2 * (B * Real.sqrt t) * Real.exp ((1 + B * Real.sqrt t) ^ 2) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hs2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have he : t * (1 / Real.sqrt t + B) ^ 2 = (1 + B * Real.sqrt t) ^ 2 := by
    calc
      _ = (Real.sqrt t) ^ 2 * (1 / Real.sqrt t + B) ^ 2 := by rw [hs2]
      _ = _ := by field_simp [hs]
  rw [gaussianSaddleModelError, he]
  ring

/-- Enlarging the Gaussian width increases its model-error envelope. -/
theorem gaussianSaddleModelError_le_of_sqrt_le {B t q : ℝ}
    (ht : 0 < t) (hB : 0 ≤ B) (hq : B * Real.sqrt t ≤ q) :
    gaussianSaddleModelError B t ≤ 2 * q * Real.exp ((1 + q) ^ 2) := by
  rw [gaussianSaddleModelError_eq ht]
  have hBq : 0 ≤ B * Real.sqrt t := mul_nonneg hB (Real.sqrt_nonneg t)
  have hq0 : 0 ≤ q := hBq.trans hq
  gcongr

/-- The inverse heat scale is at most linear in the saddle slope. -/
theorem inv_heat_le_of_product_ge {d t α : ℝ} (hd : 0 < d) (ht : 0 < t)
    (hprod : d ≤ t * α) : 1 / t ≤ α / d := by
  rw [div_le_div_iff₀ ht hd]
  simpa only [one_mul, mul_one, mul_comm] using hprod

/-- The Gaussian normalization is bounded by the inverse heat time on this interval. -/
theorem gaussian_prefactor_le_inv_heat {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) :
    (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) ≤ 1 / t := by
  have hb : t ≤ 4 * Real.pi * t := by
    have hp := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 4 * Real.pi by
      linarith only [Real.pi_gt_three]) ht.le
    simpa only [one_mul] using hp
  calc
    _ ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos ht hb (by norm_num)
    _ ≤ t ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht
      (by linarith only [ht8]) (by norm_num)
    _ = 1 / t := by rw [Real.rpow_neg_one, one_div]

/-- All lower-tail derivative prefactors grow at most linearly in the saddle slope. -/
theorem gaussian_slope_prefactor_le {d t α : ℝ}
    (hd : 0 < d) (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hprod : d ≤ t * α) (hα : 1 ≤ α) :
    1 / (2 * t) + α + 1 + (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) ≤
      (2 + 3 / (2 * d)) * α := by
  have hi := inv_heat_le_of_product_ge hd ht hprod
  have hg := (gaussian_prefactor_le_inv_heat ht ht8).trans hi
  have hhalf : 1 / (2 * t) ≤ (α / d) / 2 := by
    rw [show 1 / (2 * t) = (1 / t) / 2 by ring]
    exact div_le_div_of_nonneg_right hi (by norm_num)
  calc
    _ ≤ (α / d) / 2 + α + 1 + α / d := by linarith only [hhalf, hg]
    _ = (2 + 3 / (2 * d)) * α + (1 - α) := by ring
    _ ≤ _ := by linarith only [hα]

/-- Below inverse-slope heat, every lower Gaussian tail decays exponentially in the slope. -/
theorem exp_neg_div_heat_le {k t α : ℝ} (hk : 0 ≤ k) (ht : 0 < t)
    (htα : t * α ≤ 1) : Real.exp (-(k / t)) ≤ Real.exp (-(k * α)) := by
  apply Real.exp_le_exp.mpr
  have hh : k * α ≤ k / t := by
    rw [le_div_iff₀ ht]
    nlinarith only [mul_le_mul_of_nonneg_left htα hk]
  exact neg_le_neg hh

/-- A logarithmic source envelope gives a uniform model error throughout `tα ≤ 1`. -/
theorem gaussianSaddleModelError_le_inverse_scale {B b t α : ℝ}
    (ht : 0 < t) (hα : 0 < α) (hB : 0 ≤ B) (hBb : B ≤ b) (htα : t * α ≤ 1) :
    gaussianSaddleModelError B t ≤
      2 * (b / Real.sqrt α) * Real.exp ((1 + b / Real.sqrt α) ^ 2) := by
  apply gaussianSaddleModelError_le_of_sqrt_le ht hB
  have hb : 0 ≤ b := hB.trans hBb
  have ht' : t ≤ 1 / α := (le_div_iff₀ hα).mpr htα
  calc
    B * Real.sqrt t ≤ b * Real.sqrt t := mul_le_mul_of_nonneg_right hBb (Real.sqrt_nonneg t)
    _ ≤ b * Real.sqrt (1 / α) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht') hb
    _ = b / Real.sqrt α := by rw [one_div, Real.sqrt_inv, div_eq_mul_inv]

/-- The upper model tail has a time-independent quadratic envelope. -/
theorem kklR2_le_small_heat {t α : ℝ} (ht8 : t ≤ 1 / 8) :
    kklR2 t α ≤ Real.exp (-α ^ 2 + 5 / 8) := by
  unfold kklR2
  apply Real.exp_le_exp.mpr
  linarith only [ht8]

/-- The distant integral keeps Gaussian decay when heat is bounded below by `d/α`. -/
theorem kklRC_le_small_heat {d t α : ℝ}
    (hd : 0 < d) (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hprod : d ≤ t * α) (hα : 8 ≤ α) :
    kklRC t α ≤ 4 * Real.exp 1 * (1 / (2 * d) + 2) * α * Real.exp (-α ^ 2) := by
  have hα0 : 0 ≤ α := by linarith only [hα]
  have hinv := inv_heat_le_of_product_ge hd ht hprod
  have hpre : 1 / (2 * t) + α + 1 ≤ (1 / (2 * d) + 2) * α := by
    have hid : 1 / (2 * t) = (1 / t) / 2 := by ring
    have hid' : (1 / (2 * d) + 2) * α = (α / d) / 2 + 2 * α := by ring
    rw [hid, hid']
    linarith only [hinv, hα]
  have hs : 8 * α ≤ α ^ 2 := by
    nlinarith only [mul_nonneg hα0 (sub_nonneg.mpr hα)]
  have hexp : -(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t ≤ -α ^ 2 := by
    have htα2 := mul_le_mul_of_nonneg_right ht8 (sq_nonneg α)
    have htα := mul_le_mul_of_nonneg_right ht8 hα0
    nlinarith only [htα2, htα, ht8, hs, hα]
  unfold kklRC
  calc
    _ ≤ 2 * Real.exp 1 * 2 * ((1 / (2 * d) + 2) * α) * Real.exp (-α ^ 2) := by
      gcongr
    _ = _ := by ring

/-- At `α ≥ 3`, the distant endpoint exponent is at most `−α²`. -/
theorem kkl_boundary_exponent_le {t α : ℝ}
    (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hα : 3 ≤ α) :
    -((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2 ≤
      -α ^ 2 := by
  have he : 2 * (α ^ 2 - 1 / 2) ^ 2 ≤ (α ^ 2 - 1 / 2) ^ 2 / (4 * t) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht8) (sq_nonneg (α ^ 2 - 1 / 2))]
  have htα := mul_le_mul_of_nonneg_right ht8 (sq_nonneg α)
  have hα0 : 0 ≤ α := by linarith only [hα]
  have ha1 : 3 * α ≤ α ^ 2 := by
    nlinarith only [mul_nonneg hα0 (sub_nonneg.mpr hα)]
  have ha2 : 3 * α ^ 2 ≤ α ^ 3 := by
    nlinarith only [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hα)]
  have ha3 : 3 * α ^ 3 ≤ α ^ 4 := by
    nlinarith only [mul_nonneg (pow_nonneg hα0 3) (sub_nonneg.mpr hα)]
  nlinarith only [he, htα, ha1, ha2, ha3, hα]

/-- The distant endpoint has a linear prefactor and a quadratic Gaussian exponent. -/
theorem kklRB_le_small_heat {d t α : ℝ}
    (hd : 0 < d) (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hprod : d ≤ t * α) (hα : 3 ≤ α) :
    kklRB t α ≤ (α / d) * Real.exp (-α ^ 2) := by
  unfold kklRB
  exact mul_le_mul
    ((gaussian_prefactor_le_inv_heat ht ht8).trans (inv_heat_le_of_product_ge hd ht hprod))
    (Real.exp_le_exp.mpr (kkl_boundary_exponent_le ht ht8 hα))
    (Real.exp_pos _).le (by positivity)

/-- The far integral and endpoint share one Gaussian envelope. -/
theorem kklRC_add_kklRB_le_small_heat {d t α : ℝ}
    (hd : 0 < d) (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hprod : d ≤ t * α) (hα : 8 ≤ α) :
    kklRC t α + kklRB t α ≤
      (4 * Real.exp 1 * (1 / (2 * d) + 2) + 1 / d) * α * Real.exp (-α ^ 2) := by
  have hc := kklRC_le_small_heat hd ht ht8 hprod hα
  have hb := kklRB_le_small_heat hd ht ht8 hprod (by linarith only [hα])
  calc
    _ ≤ 4 * Real.exp 1 * (1 / (2 * d) + 2) * α * Real.exp (-α ^ 2) +
        (α / d) * Real.exp (-α ^ 2) := add_le_add hc hb
    _ = _ := by ring

#print axioms gaussianSaddleModelError_eq
#print axioms kklRC_le_small_heat
#print axioms kkl_boundary_exponent_le

end

end GaloisForLFunctions.ZeroConfigurationGeometry
