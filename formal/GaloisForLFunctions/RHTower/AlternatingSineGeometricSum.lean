import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The alternating sine geometric sum

The elementary identity behind the Lambert form of a moment-Borel transform:

`∑_{n≥1} (-1)^{n+1} sin(nα) u^n = u sin α / (1 + 2u cos α + u²)`   for `|u| < 1`.

It is the imaginary part of a geometric series with ratio `-u e^{iα}`; the denominator is
`|1 + u e^{iα}|²`, which is bounded below by `(1 - |u|)²` and so never vanishes.

* `GaloisForLFunctions.RHTower.im_neg_mul_exp_pow`;
* `GaloisForLFunctions.RHTower.tsum_alternating_sine_geometric`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

/-- The imaginary part of a power of `-u e^{iα}`. -/
theorem im_neg_mul_exp_pow (u α : ℝ) (n : ℕ) :
    ((((-u : ℝ) : ℂ) * Complex.exp ((α : ℝ) * Complex.I)) ^ n).im
      = (-u) ^ n * Real.sin (n * α) := by
  have hpow : ((((-u : ℝ) : ℂ) * Complex.exp ((α : ℝ) * Complex.I)) ^ n)
      = (((-u) ^ n : ℝ) : ℂ) * Complex.exp (((n * α : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_pow]
    congr 1
    push_cast
    ring
  rw [hpow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im]
  ring

/-- **The alternating sine geometric sum.** -/
theorem tsum_alternating_sine_geometric (α u : ℝ) (hu : |u| < 1) :
    ∑' k : ℕ, ((-1 : ℝ) ^ k * Real.sin ((k + 1) * α) * u ^ (k + 1))
      = u * Real.sin α / (1 + 2 * u * Real.cos α + u ^ 2) := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = ((-u : ℝ) : ℂ) * Complex.exp ((α : ℝ) * Complex.I) :=
    ⟨_, rfl⟩
  have hnorm : ‖q‖ = |u| := by
    rw [hqdef, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_neg]
  have hq1 : ‖q‖ < 1 := by rw [hnorm]; exact hu
  have hgs : Summable fun n : ℕ => q ^ n := summable_geometric_of_norm_lt_one hq1
  have hshift : Summable fun k : ℕ => q ^ (k + 1) :=
    hgs.comp_injective (add_left_injective 1)
  have hsum1 : ∑' k : ℕ, q ^ (k + 1) = (1 - q)⁻¹ - 1 := by
    have h0 := Summable.tsum_eq_zero_add hgs
    rw [tsum_geometric_of_norm_lt_one hq1] at h0
    simp only [pow_zero] at h0
    rw [h0]
    ring
  -- the real series is minus the imaginary part
  have hterm : ∀ k : ℕ, (-1 : ℝ) ^ k * Real.sin ((k + 1) * α) * u ^ (k + 1)
      = -((q ^ (k + 1)).im) := by
    intro k
    rw [hqdef, im_neg_mul_exp_pow]
    have hpow : (-u) ^ (k + 1) = -((-1 : ℝ) ^ k * u ^ (k + 1)) := by
      rw [neg_pow]
      ring
    rw [hpow]
    push_cast
    ring
  have hreal : ∑' k : ℕ, ((-1 : ℝ) ^ k * Real.sin ((k + 1) * α) * u ^ (k + 1))
      = -((∑' k : ℕ, q ^ (k + 1)).im) := by
    rw [tsum_congr hterm, tsum_neg]
    congr 1
    exact (ContinuousLinearMap.map_tsum Complex.imCLM hshift).symm
  -- the imaginary part of the geometric sum
  have hpos : (0 : ℝ) < 1 + 2 * u * Real.cos α + u ^ 2 := by
    have hc : |Real.cos α| ≤ 1 := Real.abs_cos_le_one α
    have hb : |2 * u * Real.cos α| ≤ 2 * |u| := by
      rw [abs_mul]
      have h2u : |2 * u| = 2 * |u| := by
        rw [abs_mul]
        simp
      calc |2 * u| * |Real.cos α| ≤ |2 * u| * 1 :=
            mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ = 2 * |u| := by rw [mul_one, h2u]
    have hge : -(2 * |u|) ≤ 2 * u * Real.cos α := (abs_le.mp hb).1
    have habs2 : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [sq_nonneg (1 - |u|), abs_nonneg u]
  have hden : (1 : ℝ) + 2 * u * Real.cos α + u ^ 2 ≠ 0 := ne_of_gt hpos
  have honeq : (1 : ℂ) - q = ((1 + u * Real.cos α : ℝ) : ℂ) + ((u * Real.sin α : ℝ) : ℂ) * I := by
    rw [hqdef, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have himinv : ((1 - q)⁻¹).im = -(u * Real.sin α) / (1 + 2 * u * Real.cos α + u ^ 2) := by
    rw [Complex.inv_im, honeq]
    have hnormsq : Complex.normSq (((1 + u * Real.cos α : ℝ) : ℂ)
        + ((u * Real.sin α : ℝ) : ℂ) * I) = 1 + 2 * u * Real.cos α + u ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      have hpyth := Real.sin_sq_add_cos_sq α
      nlinarith [hpyth]
    rw [hnormsq]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    ring
  rw [hreal, hsum1]
  simp only [Complex.sub_im, Complex.one_im, sub_zero, himinv]
  field_simp

end GaloisForLFunctions.RHTower
