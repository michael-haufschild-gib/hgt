import GaloisForLFunctions.HTGeometry.UniformSecondOrderJet
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Elementary horizon jets

The horizon coordinate `z` of the Birmingham--Mokhtari exterior satisfies `√(1-z) = radialUnit`,
so every elementary radial factor is a function of `√(1-z)`.  This file records the uniform
second-order jets of `√(1-z)` and of the parameter-dependent powers `(1+√(1-z))^{α(u)}` on
`z ∈ [0, b]`, with explicit constants depending only on a bound for `α` on the parameter set.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Complex
noncomputable section
set_option autoImplicit false

/-- `√(1-z) ≤ 1 - z/2` on `[0,1]`. -/
theorem sqrt_one_sub_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.sqrt (1 - z) ≤ 1 - z / 2 := by
  have h : 1 - z ≤ (1 - z / 2) ^ 2 := by nlinarith
  calc Real.sqrt (1 - z) ≤ Real.sqrt ((1 - z / 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = 1 - z / 2 := Real.sqrt_sq (by linarith)

/-- `1 - z/2 - z²/4 ≤ √(1-z)` on `[0,1/2]`. -/
theorem le_sqrt_one_sub {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    1 - z / 2 - z ^ 2 / 4 ≤ Real.sqrt (1 - z) := by
  apply Real.le_sqrt_of_sq_le
  have h : (1 - z / 2 - z ^ 2 / 4) ^ 2 = 1 - z - z ^ 2 / 4 * (1 - z - z ^ 2 / 4) := by ring
  have h2 : 0 ≤ z ^ 2 / 4 * (1 - z - z ^ 2 / 4) := by
    apply mul_nonneg (by positivity)
    nlinarith [sq_nonneg z]
  linarith

/-- The square-root jet, with constant coefficients. -/
theorem abs_sqrt_one_sub_sub_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    |Real.sqrt (1 - z) - (1 - z / 2)| ≤ z ^ 2 / 4 := by
  rw [abs_le]
  constructor
  · linarith [le_sqrt_one_sub hz0 hz1]
  · nlinarith [sqrt_one_sub_le hz0 (by linarith), sq_nonneg z]

theorem hasUniformJet2_sqrt_one_sub (S : Set ℂ) :
    HasUniformJet2 S (1 / 2) (fun _ z => (Real.sqrt (1 - z) : ℂ)) (fun _ => 1) (fun _ => -1 / 2)
      (1 / 4) := by
  intro u _ z hz
  have h := abs_sqrt_one_sub_sub_le hz.1.le hz.2
  have he : (Real.sqrt (1 - z) : ℂ) - 1 - (-1 / 2) * (z:ℂ) = ((Real.sqrt (1 - z) - (1 - z / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- `log((1+√(1-z))/2) = -z/4 + O(z²)` on `[0,1/2]`. -/
theorem abs_log_half_one_add_sqrt_add_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    |Real.log ((1 + Real.sqrt (1 - z)) / 2) + z / 4| ≤ z ^ 2 / 2 := by
  set x := (1 - Real.sqrt (1 - z)) / 2 with hx
  have hs := abs_sqrt_one_sub_sub_le hz0 hz1
  rw [abs_le] at hs
  have hx0 : 0 ≤ x := by
    have := sqrt_one_sub_le hz0 (by linarith); rw [hx]; linarith
  have hxz : x ≤ z / 4 + z ^ 2 / 8 := by rw [hx]; linarith [hs.1]
  have hxz' : z / 4 ≤ x := by
    rw [hx]; linarith [sqrt_one_sub_le hz0 (by linarith : z ≤ 1)]
  have hxlt : |x| < 1 := by
    rw [abs_of_nonneg hx0]; nlinarith
  have hxhalf : x ≤ 1 / 4 := by nlinarith
  have hlog : |x + Real.log (1 - x)| ≤ |x| ^ 2 / (1 - |x|) := by
    have := Real.abs_log_sub_add_sum_range_le hxlt 1
    simpa [Finset.sum_range_one] using this
  have hform : (1 + Real.sqrt (1 - z)) / 2 = 1 - x := by rw [hx]; ring
  rw [hform]
  have hden : 1 / 2 ≤ 1 - |x| := by rw [abs_of_nonneg hx0]; linarith
  have hbound : |x| ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
    rw [abs_of_nonneg hx0, div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  have hxsq : x ^ 2 ≤ z ^ 2 / 8 := by
    have h1 : x ≤ (3 / 8) * z := by nlinarith
    have h2 : x ^ 2 ≤ ((3 / 8) * z) ^ 2 := pow_le_pow_left₀ hx0 h1 2
    nlinarith
  calc |Real.log (1 - x) + z / 4| = |(x + Real.log (1 - x)) - (x - z / 4)| := by ring_nf
    _ ≤ |x + Real.log (1 - x)| + |x - z / 4| := abs_sub _ _
    _ ≤ 2 * x ^ 2 + z ^ 2 / 8 := by
      gcongr
      · exact hlog.trans hbound
      · rw [abs_le]; constructor <;> linarith
    _ ≤ z ^ 2 / 2 := by linarith

theorem cpow_ofReal_pos_eq {r : ℝ} (hr : 0 < r) (α : ℂ) :
    ((r:ℝ):ℂ) ^ α = Complex.exp (α * (Real.log r : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.ofReal_log hr.le, mul_comm]

/-- The uniform jet of `(1+√(1-z))^{α(u)}` for `α` bounded by `B` on the parameter set. -/
theorem hasUniformJet2_cpow_one_add_sqrt (S : Set ℂ) {α : ℂ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hα : ∀ u ∈ S, ‖α u‖ ≤ B) :
    HasUniformJet2 S (min (1 / 2) (1 / (B + 1)))
      (fun u z => ((1 + Real.sqrt (1 - z) : ℝ) : ℂ) ^ (α u))
      (fun u => (2:ℂ) ^ (α u)) (fun u => -(α u) * (2:ℂ) ^ (α u) / 4)
      ((2:ℝ) ^ B * (B / 2 + 9 * B ^ 2 / 16)) := by
  intro u hu z hz
  have hz0 : 0 ≤ z := hz.1.le
  have hzh : z ≤ 1 / 2 := hz.2.trans (min_le_left _ _)
  have hzB : z ≤ 1 / (B + 1) := hz.2.trans (min_le_right _ _)
  have hs0 : 0 < 1 + Real.sqrt (1 - z) := by positivity
  set ℓ : ℝ := Real.log ((1 + Real.sqrt (1 - z)) / 2) with hℓ
  have hℓb := abs_log_half_one_add_sqrt_add_le hz0 hzh
  have hℓabs : |ℓ| ≤ 3 / 4 * z := by
    have : |ℓ + z / 4| ≤ z ^ 2 / 2 := hℓb
    rw [abs_le] at this ⊢
    constructor <;> nlinarith [sq_nonneg z]
  have hsplit : ((1 + Real.sqrt (1 - z) : ℝ) : ℂ) ^ (α u) =
      (2:ℂ) ^ (α u) * Complex.exp (α u * (ℓ:ℂ)) := by
    rw [cpow_ofReal_pos_eq hs0, show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, cpow_ofReal_pos_eq (by norm_num),
      ← Complex.exp_add, hℓ, Real.log_div (by positivity) (by norm_num)]
    congr 1
    push_cast
    ring
  set y : ℂ := α u * (ℓ:ℂ) with hy
  have hyn : ‖y‖ ≤ 3 / 4 * B * z := by
    rw [hy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖α u‖ * |ℓ| ≤ B * (3 / 4 * z) := mul_le_mul (hα u hu) hℓabs (abs_nonneg _) hB
      _ = 3 / 4 * B * z := by ring
  have hy1 : ‖y‖ ≤ 1 := by
    have hBz : B * z ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hzB hB
      rw [mul_one_div] at this
      calc B * z ≤ B / (B + 1) := this
        _ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have hexp := Complex.norm_exp_sub_one_sub_id_le hy1
  have h2B : ‖(2:ℂ) ^ (α u)‖ ≤ (2:ℝ) ^ B := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact (Complex.re_le_norm _).trans (hα u hu)
  have hkey : ((1 + Real.sqrt (1 - z) : ℝ) : ℂ) ^ (α u) - (2:ℂ) ^ (α u) -
      (-(α u) * (2:ℂ) ^ (α u) / 4) * (z:ℂ) =
      (2:ℂ) ^ (α u) * ((Complex.exp y - 1 - y) + α u * ((ℓ:ℂ) + (z:ℂ) / 4)) := by
    rw [hsplit, hy]
    ring
  rw [hkey, norm_mul]
  have hrem : ‖(Complex.exp y - 1 - y) + α u * ((ℓ:ℂ) + (z:ℂ) / 4)‖ ≤
      (B / 2 + 9 * B ^ 2 / 16) * z ^ 2 := by
    calc ‖(Complex.exp y - 1 - y) + α u * ((ℓ:ℂ) + (z:ℂ) / 4)‖
        ≤ ‖Complex.exp y - 1 - y‖ + ‖α u * ((ℓ:ℂ) + (z:ℂ) / 4)‖ := norm_add_le _ _
      _ ≤ ‖y‖ ^ 2 + B * (z ^ 2 / 2) := by
        gcongr
        rw [norm_mul]
        apply mul_le_mul (hα u hu) _ (norm_nonneg _) hB
        have : (ℓ:ℂ) + (z:ℂ) / 4 = ((ℓ + z / 4 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs]
        exact hℓb
      _ ≤ (3 / 4 * B * z) ^ 2 + B * (z ^ 2 / 2) := by
        gcongr
      _ = (B / 2 + 9 * B ^ 2 / 16) * z ^ 2 := by ring
  calc ‖(2:ℂ) ^ (α u)‖ * ‖(Complex.exp y - 1 - y) + α u * ((ℓ:ℂ) + (z:ℂ) / 4)‖
      ≤ (2:ℝ) ^ B * ((B / 2 + 9 * B ^ 2 / 16) * z ^ 2) :=
        mul_le_mul h2B hrem (norm_nonneg _) (by positivity)
    _ = (2:ℝ) ^ B * (B / 2 + 9 * B ^ 2 / 16) * z ^ 2 := by ring

/-- `1/√(1-z) = 1 + z/2 + O(z²)` on `[0,1/2]`. -/
theorem abs_inv_sqrt_one_sub_sub_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    |(Real.sqrt (1 - z))⁻¹ - (1 + z / 2)| ≤ 2 * z ^ 2 := by
  have hup := sqrt_one_sub_le hz0 (by linarith)
  have hlo := le_sqrt_one_sub hz0 hz1
  have hpos : 1 / 2 ≤ Real.sqrt (1 - z) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hs0 : 0 < Real.sqrt (1 - z) := by linarith
  set n := 1 - (1 + z / 2) * Real.sqrt (1 - z) with hn
  have hn0 : 0 ≤ n := by rw [hn]; nlinarith
  have hn1 : n ≤ 9 / 16 * z ^ 2 := by rw [hn]; nlinarith
  have hform : (Real.sqrt (1 - z))⁻¹ - (1 + z / 2) = n / Real.sqrt (1 - z) := by
    rw [hn]; field_simp
  rw [hform, abs_of_nonneg (div_nonneg hn0 hs0.le), div_le_iff₀ hs0]
  nlinarith

theorem hasUniformJet2_inv_sqrt_one_sub (S : Set ℂ) :
    HasUniformJet2 S (1 / 2) (fun _ z => ((Real.sqrt (1 - z))⁻¹ : ℂ)) (fun _ => 1) (fun _ => 1 / 2) 2 := by
  intro u _ z hz
  have h := abs_inv_sqrt_one_sub_sub_le hz.1.le hz.2
  have he : ((Real.sqrt (1 - z))⁻¹ : ℂ) - 1 - (1 / 2) * (z:ℂ) =
      (((Real.sqrt (1 - z))⁻¹ - (1 + z / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  linarith

end
end GaloisForLFunctions.HTGeometry
