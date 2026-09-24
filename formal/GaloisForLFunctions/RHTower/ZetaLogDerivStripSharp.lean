import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegionBound

/-!
# `ζ'/ζ = O(log² |γ|)` on a strip of width `1/(232 log |γ|)`

`Sieve.exists_logDeriv_zeta_bound_of_region` converts any exponent-one zero-free region of width
`c/log|γ|` valid from `T₀` into `‖ζ'/ζ‖ ≤ C log²|γ|` on the strip of width
`min(c/4, 1/160)/log|γ|` from `max 4 (T₀+1)`.  Fed with the corpus's own region it gives width
`1/40000` from `exp(40804)`; fed with `riemannZeta_ne_zero_of_one_sub_lt_re` it gives width `1/232`
from ordinate `5`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **`ζ'/ζ` on a strip of width `1/(232 log |γ|)`, from ordinate `5`.** -/
theorem exists_logDeriv_zeta_bound_sharp :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ γ : ℝ, 5 ≤ |γ| → 1 - 1 / 232 / Real.log |γ| ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| ^ (2 : ℕ) := by
  obtain ⟨C, hC0, hb⟩ := Sieve.exists_logDeriv_zeta_bound_of_region (c := 1 / 58) (T₀ := 4)
    (by norm_num)
    (fun β γ' hγ' _ hβ => riemannZeta_ne_zero_of_one_sub_lt_re hγ' hβ)
  refine ⟨C, hC0, fun σ γ hγ hlow hhigh => hb σ γ ?_ ?_ hhigh⟩
  · rw [show max (4 : ℝ) (4 + 1) = 5 by norm_num]
    exact hγ
  · rw [show min ((1 / 58 : ℝ) / 4) (1 / 160) = 1 / 232 by norm_num]
    exact hlow

end

end RHTower
