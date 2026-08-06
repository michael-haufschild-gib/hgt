# The κ=1 Chebyshev chain: every step proved, one instantiation left

Card: `docs/drafts/pipeline/1-in-progress/chebyshev-exponent-one-half.md`.
Target: `|ψ(N) - N| ≪ N·exp(-√(log N)/480000)`, beating `PNTPlus.MediumPNT`
(`ψ - id =O[atTop] x·exp(-c(log x)^{1/10})`).

## The ladder (all unconditional, all in `RHTower/Sieve/`)

| step | module | statement |
|---|---|---|
| region-width `ζ'/ζ` | `ZetaLogDerivRegUniform` | `exists_bound_zetaLogDerivReg_uniform`, `exists_zeta_uniform_kappa_one_zero_free`, `exists_bound_zetaLogDerivReg_box` |
| contour data | `ChebyshevKappaOneData` | `exists_cheb_kappa_one_data`, `one_sub_chebLeftTwo_inv`, `half_le_chebLeftTwo` |
| contour bound | `ChebyshevKappaOneContour` | `exists_norm_tsum_vonMangoldt_kappa_one_general` |
| height | `ChebyshevHeightOne`, `ChebyshevRatePowersOne` | `chebHeightOne x = exp(2√(log x))`; exact edge-power identities |
| width | `ChebyshevWidthOne` | `chebRatioOne N = exp(√(log N)/240000)`; `sq_le_exp_div_gen` |
| bracket | `ChebyshevBracketBound` | `abs_bracket_sub_two_pi_le`, `arctan_le_self` |
| shape data | `ChebyshevKappaOneShape` | series `≤ 8log²T`, width `≤ 2/log T` |
| term reductions | `ChebyshevKappaOneTerms` | four abstract per-term lemmas |
| edge powers | `ChebyshevPowersAtHeight` | `chebFactorOne Z = 3exp(-√(log Z)/80000)`, three bounds |
| balance | `ChebyshevBalanceOne` | `price_mul_factor_le`, `one_div_chebHeightOne_le_factor`, `width_price_le` |
| five→shape | `ChebyshevKappaOneShaped` | `cheb_kappa_one_terms_shaped` |
| coefficient | `ChebyshevKappaOneCoeff` | `cheb_kappa_one_coeff_le` (`≤ 250000(1+Cr)(1+Wb)log²T`) |
| collapse | `ChebyshevCollapseOne` | `one_add_width_mul_factor_le`, `sq_mul_exp_neg_le`, `sq_log_chebHeightOne` |

## What is left

Purely mechanical: instantiate `exists_norm_tsum_vonMangoldt_kappa_one_general` at
`T = chebHeightOne (N+H+1)`, `H = chebWidthOne N`; chain
`cheb_kappa_one_terms_shaped` → `cheb_kappa_one_coeff_le` → `one_add_width_mul_factor_le` →
`sq_mul_exp_neg_le`; add the bracket correction (`abs_bracket_kappa_one_le`, `≤ 3/(T log T)`);
transfer with `norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` (cost `(H+1)·log(N+H)`).

## Where the exponent's halvings happen (all four)

`1/40000` (region width) → `1/80000` (left edge, `saving_exponent_one`) → `1/240000` (the balance
against the smoothing's price, `price_mul_factor_le`) → `1/480000` (absorbing `log²T`,
`sq_mul_exp_neg_le`).  The `Y+1 → Y` shift costs a **constant**, not a halving — see
`mem:route_e/chebyshev_shift_is_a_constant_not_an_exponent_2026_08_06`.

Build discipline that worked: every arithmetic step a **top-level** lemma (heartbeats are
per-declaration), `mul_le_mul_of_nonneg_*` + `linarith` rather than `nlinarith` on high-degree
products, and `have hTT : T ^ (1+1) = T*T := by ring` before any `nlinarith` touching that exponent.
