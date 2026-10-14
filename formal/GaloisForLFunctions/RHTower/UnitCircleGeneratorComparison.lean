import GaloisForLFunctions.RHTower.TwistedArcMomentN1Reduction

/-!
# Spectral comparison of the unit-circle Poisson generators

For `|c| < 1` the symmetric kernel `𝒦_c(v) = (cosh v + c)^{−1/2} + (cosh v − c)^{−1/2}` is, up to
the factor `(y/2)^{1/2}`, the log-scale profile of the even `s = ½` Poisson generator attached to the
point `c + i√(1 − c²)` of the unit circle.  Its cosine transform is

`Ŝ_c(τ) = Σ_j 2 C(−½, 2j) c^{2j} C_j(τ)`,   `C_j(τ) = ∫ cos(τv) (cosh v)^{−1/2−2j} dv > 0`

(`hasSum_integral_cos_mul_symCoshKernel`), a series with positive coefficients in `c²`.

**Theorem** (`integral_cos_mul_symCoshKernel_le_of_abs_le`,
`integral_cos_mul_symCoshKernel_lt_of_abs_lt`).  If `|c'| ≤ |c| < 1` then `Ŝ_{c'}(τ) ≤ Ŝ_c(τ)` for
every real `τ`, strictly if `|c'| < |c|`.

So a generator closer to the real axis dominates, at every frequency, a generator higher up on the
unit circle.  A difference of two probability measures of generators, the first carried by
`|c| ≥ a` and the second by `|c| ≤ a`, therefore has nonnegative cosine transform: the leading
term `C_0`, which carries the `e^{−|v|/2}` tail, cancels, and every other term is ordered.
-/

open MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem pow_two_mul_le_of_abs_le {c c' : ℝ} (h : |c'| ≤ |c|) (j : ℕ) :
    c' ^ (2 * j) ≤ c ^ (2 * j) := by
  rw [pow_mul, pow_mul, ← sq_abs c', ← sq_abs c]
  exact pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (abs_nonneg _) h 2) j

/-- **Monotonicity of the generator spectra in `|c|`.** -/
theorem integral_cos_mul_symCoshKernel_le_of_abs_le {c c' : ℝ} (hc : |c| < 1) (h : |c'| ≤ |c|)
    (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * symCoshKernel c' v ≤ ∫ v, Real.cos (τ * v) * symCoshKernel c v := by
  refine hasSum_le (fun j => ?_) (hasSum_integral_cos_mul_symCoshKernel (lt_of_le_of_lt h hc) τ)
    (hasSum_integral_cos_mul_symCoshKernel hc τ)
  have h1 := choose_neg_half_even_pos j
  have h2 := coshPowerTransform_pos j τ
  have h3 := pow_two_mul_le_of_abs_le h j
  have : 0 ≤ 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * coshPowerTransform j τ := by positivity
  nlinarith

/-- **Strict monotonicity of the generator spectra in `|c|`.** -/
theorem integral_cos_mul_symCoshKernel_lt_of_abs_lt {c c' : ℝ} (hc : |c| < 1) (h : |c'| < |c|)
    (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * symCoshKernel c' v < ∫ v, Real.cos (τ * v) * symCoshKernel c v := by
  refine hasSum_lt (i := 1) (fun j => ?_) ?_
    (hasSum_integral_cos_mul_symCoshKernel (lt_trans h hc) τ)
    (hasSum_integral_cos_mul_symCoshKernel hc τ)
  · have h1 := choose_neg_half_even_pos j
    have h2 := coshPowerTransform_pos j τ
    have h3 := pow_two_mul_le_of_abs_le h.le j
    have : 0 ≤ 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * coshPowerTransform j τ := by positivity
    show 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * c' ^ (2 * j) * coshPowerTransform j τ ≤
      2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * c ^ (2 * j) * coshPowerTransform j τ
    nlinarith
  · have h1 := choose_neg_half_even_pos 1
    have h2 := coshPowerTransform_pos 1 τ
    have h3 : c' ^ (2 * 1) < c ^ (2 * 1) := by
      rw [mul_one, ← sq_abs c', ← sq_abs c]
      exact pow_lt_pow_left₀ h (abs_nonneg _) (by norm_num)
    have hK : 0 < 2 * Ring.choose (-1 / 2 : ℝ) (2 * 1) * coshPowerTransform 1 τ := by positivity
    show 2 * Ring.choose (-1 / 2 : ℝ) (2 * 1) * c' ^ (2 * 1) * coshPowerTransform 1 τ <
      2 * Ring.choose (-1 / 2 : ℝ) (2 * 1) * c ^ (2 * 1) * coshPowerTransform 1 τ
    calc 2 * Ring.choose (-1 / 2 : ℝ) (2 * 1) * c' ^ (2 * 1) * coshPowerTransform 1 τ
        = (2 * Ring.choose (-1 / 2 : ℝ) (2 * 1) * coshPowerTransform 1 τ) * c' ^ (2 * 1) := by
          ring
      _ < (2 * Ring.choose (-1 / 2 : ℝ) (2 * 1) * coshPowerTransform 1 τ) * c ^ (2 * 1) :=
          mul_lt_mul_of_pos_left h3 hK
      _ = 2 * Ring.choose (-1 / 2 : ℝ) (2 * 1) * c ^ (2 * 1) * coshPowerTransform 1 τ := by ring

end

end RHTower
