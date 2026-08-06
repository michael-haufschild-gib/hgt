# The smoothed Chebyshev sum has an explicit rate at exponent 1/2

`RHTower.Sieve.exists_norm_tsum_vonMangoldt_kappa_one_rate`
(`RHTower/Sieve/ChebyshevKappaOneRate.lean`):

    ∃ B ≥ 0, ∀ᶠ N in atTop,
      ‖ 2π ∑' Λ(n)·w(n) - (mellin w 1)·(2 arctan(T/(d-1)) - 2 arctan(T/(c-1))) ‖
        ≤ B · (N + H + 1) · exp( -√(log(N+H+1)) / 480000 )

with `H = chebWidthOne N`, `T = chebHeightOne (N+H+1)`, and
`B = 250000(1+Cr)(3+27Cm)·(4·(4·480000²))` explicit in the Mellin decay constant `Cm` and the
regular-part bound `Cr`.  Unconditional.

This is the exponent-`1/2` route completed at the smoothed level.  Full ladder in
`mem:route_e/chebyshev_kappa_one_chain_complete_except_instantiation_2026_08_06`.

## Two traps that cost build cycles

- **`Λ` is `ArithmeticFunction.vonMangoldt` notation.**  With `open ArithmeticFunction`, a named
  argument `(Λ := …)` fails to parse with `unexpected token ':='`.  Rename such binders (`Λ → Lg`).
  Any lemma in this corpus that takes a "logarithm" parameter and may be used under
  `open ArithmeticFunction` must avoid the name `Λ`.
- **`rw` must hit every hypothesis sharing an atom.**  Rewriting `log²T = 4 log Z` in one
  hypothesis left the others carrying `Real.log (chebHeightOne Z) ^ 2`, which `linarith` treats as
  an atom unrelated to `4 * Real.log Z`.  `rw [h] at hbase hshaped hstep` — then the whole assembly
  is one `linarith` over four hypotheses.

## What remains for `ψ(N)`

1. main term `(mellin w 1)·(bracket) → 2π·(N + O(H))`: `abs_bracket_kappa_one_le` (error
   `≤ 3/(T log T)`), `le_integral_smoothWeight`, `integral_smoothWeight_le` (mass in `[N, N+H]`);
2. `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` for the sharp sum, costing `(H+1)·log(N+H)`
   `= N·log N·exp(-√(log N)/240000)` — same order as the contour term after `sq_le_exp_div_gen`.

Target `|ψ(N) - N| ≪ N·exp(-√(log N)/480000)` versus `PNTPlus.MediumPNT`'s `exp(-c(log x)^{1/10})`.
