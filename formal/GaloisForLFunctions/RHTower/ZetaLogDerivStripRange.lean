import GaloisForLFunctions.RHTower.ZetaLogDerivLowHeight
import GaloisForLFunctions.RHTower.ZetaLogDerivBound

/-!
# The strip `ζ′/ζ` bound over a height range

For `9 ≤ |y| ≤ T` and `|σ - 1| ≤ A/(2·log⁹T)`, the logarithmic
derivative obeys `‖ζ′/ζ(σ+iy)‖ ≤ (2240/A)·log⁹T`: the point lies in
the zero-free strip at its own height since `A/(2·log⁹T) ≤ A/log⁹|y|`,
and the height-`|y|` bound is monotone in the height.
-/

noncomputable section

namespace RHTower

/-- **Strip bound over a height range**: `‖ζ′/ζ(σ+iy)‖ ≤ (2240/A)·log⁹T`
for `9 ≤ |y| ≤ T` and `|σ-1| ≤ A/(2·log⁹T)`. -/
theorem norm_zeta_logDeriv_le_strip_range {σ y T : ℝ} (hT : 9 ≤ T)
    (hy9 : 9 ≤ |y|) (hyT : |y| ≤ T)
    (hσl : 1 - zetaLowerA / (2 * Real.log T ^ 9) ≤ σ)
    (hσu : σ ≤ 1 + zetaLowerA / (2 * Real.log T ^ 9)) :
    ‖deriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)
      / riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)‖
    ≤ 2240 / zetaLowerA * Real.log T ^ 9 := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hlogy0 : (0 : ℝ) < Real.log |y| := Real.log_pos (by linarith)
  have hlogT0 : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  have hmono : Real.log |y| ≤ Real.log T :=
    Real.log_le_log (by linarith) hyT
  have hpow : Real.log |y| ^ 9 ≤ Real.log T ^ 9 :=
    pow_le_pow_left₀ hlogy0.le hmono 9
  have hhalf : zetaLowerA / (2 * Real.log T ^ 9)
      ≤ zetaLowerA / Real.log |y| ^ 9 := by
    apply div_le_div_of_nonneg_left hA0.le (by positivity)
    calc Real.log |y| ^ 9 ≤ Real.log T ^ 9 := hpow
      _ ≤ 2 * Real.log T ^ 9 := by nlinarith [pow_pos hlogT0 9]
  have hb := norm_deriv_div_riemannZeta_le hy9
    (by linarith : 1 - zetaLowerA / Real.log |y| ^ 9 ≤ σ)
    (by linarith : σ ≤ 1 + zetaLowerA / Real.log |y| ^ 9)
  calc ‖deriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)
        / riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ 2240 / zetaLowerA * Real.log |y| ^ 9 := hb
    _ ≤ 2240 / zetaLowerA * Real.log T ^ 9 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

end RHTower
