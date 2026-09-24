import GaloisForLFunctions.RHTower.XiLogDerivRePositiveStrict

/-!
# Arithmetic form of the completed positivity

The corpus's `re_logDeriv_xi_pos_of_one_le_re` and the explicit formula
`xi_explicitFormula_logDeriv` combine, right of the abscissa of convergence, into an unconditional
strict bound with no zeros in it:

```text
Re (Σ_n Λ(n) n^{-s})  <  Re (1/s) + Re (1/(s-1)) + Re (logDeriv Γ_ℝ s)   for Re s > 1 .
```

This is the arithmetic content of the divisor-side positivity: the von Mangoldt Dirichlet series
is dominated by purely polar and archimedean data.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Arithmetic form of the completed positivity.**  Right of the abscissa of convergence the
positivity of `Re (ξ'/ξ)` is an unconditional strict upper bound for the real part of the von
Mangoldt Dirichlet series in terms of purely polar and archimedean data. -/
theorem re_LSeries_vonMangoldt_lt_polar_add_archimedean {s : ℂ} (hs : 1 < s.re) :
    (LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s).re <
      (s⁻¹).re + ((s - 1)⁻¹).re + (logDeriv Complex.Gammaℝ s).re := by
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_le_re hs.le
  have hpos := re_logDeriv_xi_pos_of_one_le_re hs.le
  rw [logDeriv_xi_eq_partialFraction hxi, xi_explicitFormula_logDeriv hs] at hpos
  simp only [Complex.sub_re, Complex.add_re] at hpos
  linarith

end

end RHTower
