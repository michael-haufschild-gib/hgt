import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegBound
import GaloisForLFunctions.RHTower.ZetaLogDerivBound

/-!
# The regular part on the zero-free strip

Above height `9` the strip `|σ - 1| ≤ A/log⁹|t|` carries a quantitative lower bound for `‖ζ‖`, hence
a bound for the logarithmic derivative.  The regular part differs from `-ζ'/ζ` by the pole term, so

    ‖zetaLogDerivReg(σ+it)‖ ≤ (2240/A)·log⁹|t| + 1/9.

Nothing beyond the strip estimate is needed: the pole is at distance at least `|t| ≥ 9`.
-/

namespace RHTower.Sieve

open Complex RHTower

/-- **`ζ` does not vanish on the strip.**  Immediate from the quartic lower bound. -/
theorem riemannZeta_ne_zero_strip {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ σ)
    (hσu : σ ≤ 1 + zetaLowerA / Real.log |t| ^ (9 : ℕ)) :
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hexp2 := exp_two_lt_eight
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hq := pow_four_norm_riemannZeta_ge_strip ht hσl hσu
  have hq0 : (0 : ℝ) < zetaLowerA ^ (3 : ℕ) / (12096 * Real.log |t| ^ (28 : ℕ)) := by positivity
  intro h
  rw [h] at hq
  simp only [norm_zero] at hq
  rw [show ((0 : ℝ)) ^ (4 : ℕ) = 0 by norm_num] at hq
  linarith

/-- **The regular part on the strip.** -/
theorem norm_zetaLogDerivReg_strip_le {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ σ)
    (hσu : σ ≤ 1 + zetaLowerA / Real.log |t| ^ (9 : ℕ)) :
    ‖zetaLogDerivReg ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2240 / zetaLowerA * Real.log |t| ^ (9 : ℕ) + 1 / 9 := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht0
    simp at ht0
  have hs1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    apply htne
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simpa using him.symm
  have hz := riemannZeta_ne_zero_strip ht hσl hσu
  have hbase := norm_zetaLogDerivReg_le hs1 hz
  have hlog := norm_deriv_div_riemannZeta_le ht hσl hσu
  have hprod : ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      * ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖
      ≤ 2240 / zetaLowerA * Real.log |t| ^ (9 : ℕ) := by
    rw [← norm_mul, ← div_eq_mul_inv]
    exact hlog
  have hpole : ‖(((σ : ℂ) + (t : ℂ) * Complex.I) - 1)⁻¹‖ ≤ 1 / 9 := by
    refine le_trans (norm_inv_sub_one_le_height (β := σ) htne) ?_
    rw [inv_le_comm₀ ht0 (by norm_num)]
    linarith
  linarith

end RHTower.Sieve
