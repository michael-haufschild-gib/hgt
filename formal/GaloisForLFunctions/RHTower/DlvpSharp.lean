import GaloisForLFunctions.RHTower.ZetaLogDerivSharpLandauZero
import GaloisForLFunctions.RHTower.Sieve.DeLaValleePoussinInequality

/-!
# The de la Vallée Poussin inequality on the sharp Landau input

Feeding `neg_re_logDeriv_riemannZeta_le_sub_resolvent` at height `γ` and
`neg_re_logDeriv_riemannZeta_le` at height `2γ` into the three-four-one inequality gives, for a zero
copy of `ξ` at `ρ = β + iγ` with `γ ≥ 4` and every `1 < σ ≤ 2`,

```text
4/(σ − β)  ≤  3/(σ − 1) + 5 log γ + K ,
```

with `K = 3A + 5(1/5 + C) + log 2` where `A` is the pole bound and `C` the digamma constant.  The
coefficient of `log γ` is `5`, against `320·(5/4) = 400` in `dlvp_inequality`: the archimedean factor
is the only source of growth, and the zeros of `ξ` only help.
-/

open Complex GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The constant of the sharp Landau bound. -/
def landauSharpConstant : ℝ := 1 / 5 + digammaVerticalLogConstant

/-- The constant of the sharp de la Vallée Poussin inequality. -/
def dlvpSharpConstant (A : ℝ) : ℝ := 3 * A + 5 * landauSharpConstant + Real.log 2

/-- **The sharp de la Vallée Poussin inequality.** -/
theorem dlvp_sharp {A σ : ℝ}
    (hA : ∀ u : ℝ, 1 < u → u ≤ 2 →
      (-deriv riemannZeta (u : ℂ) / riemannZeta (u : ℂ)).re ≤ 1 / (u - 1) + A)
    (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (q₀ : XiZeroCopy) (hγ : 4 ≤ (q₀.1 : ℂ).im) :
    4 / (σ - (q₀.1 : ℂ).re)
      ≤ 3 / (σ - 1) + 5 * Real.log ((q₀.1 : ℂ).im) + dlvpSharpConstant A := by
  set β : ℝ := (q₀.1 : ℂ).re with hβ
  set γ : ℝ := (q₀.1 : ℂ).im with hγdef
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one q₀
  have hσβ : 0 < σ - β := by linarith
  -- the bound at height `γ`, with the zero retained
  have hmain := neg_re_logDeriv_riemannZeta_le_sub_resolvent hσ1 hσ2 hγ q₀
  have hnormSq : Complex.normSq (((σ : ℂ) + (γ : ℂ) * Complex.I) - (q₀.1 : ℂ))
      = (σ - β) ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, ← hβ, ← hγdef]
    ring
  rw [hnormSq] at hmain
  have hdiv : (σ - β) / (σ - β) ^ (2 : ℕ) = 1 / (σ - β) := by
    rw [pow_two]
    field_simp
  rw [hdiv] at hmain
  -- the bound at height `2γ`
  have hB0 := neg_re_logDeriv_riemannZeta_le (σ := σ) (t := 2 * γ) hσ1 hσ2 (by linarith)
  have hcast : ((2 * γ : ℝ) : ℂ) = (2 * γ : ℂ) := by push_cast; ring
  rw [hcast] at hB0
  -- convert to the `-deriv/·` form used by the three-four-one inequality
  have hconvB : (-deriv riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)
      / riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)).re
      ≤ 1 / 5 + Real.log (2 * γ) + digammaVerticalLogConstant := by
    rw [Sieve.neg_div_re_eq_neg_logDeriv_re]
    exact hB0
  have hshift := Sieve.re_logDeriv_shift_le (σ := σ) (t := γ) hσ1 (hA σ hσ1 hσ2) hconvB
  rw [Sieve.neg_div_re_eq_neg_logDeriv_re] at hshift
  -- combine
  have hlog2 : Real.log (2 * γ) = Real.log 2 + Real.log γ := by
    rw [Real.log_mul (by norm_num) hγ0.ne']
  rw [hlog2] at hshift
  have hX : -(logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
      ≤ 1 / 5 + Real.log γ + digammaVerticalLogConstant - 1 / (σ - β) := hmain
  have hchain : 1 / (σ - β)
      ≤ 1 / 5 + Real.log γ + digammaVerticalLogConstant
        + (3 * (1 / (σ - 1) + A)
            + (1 / 5 + (Real.log 2 + Real.log γ) + digammaVerticalLogConstant)) / 4 := by
    linarith [hX, hshift]
  have hgoal4 : (4 : ℝ) / (σ - β) = 4 * (1 / (σ - β)) := by ring
  have hgoal3 : (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) := by ring
  rw [hgoal4, hgoal3]
  unfold dlvpSharpConstant landauSharpConstant
  linarith [hchain]

end

end RHTower
