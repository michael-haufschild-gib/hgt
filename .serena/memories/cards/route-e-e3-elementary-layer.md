# Route E E₃ cards: the elementary layer is formalized

Two stage-2 cards, both perturbations of Matomäki--Teräväinen's all-interval `E₃` theorem
(arXiv 2207.05038), which they quote rather than prove.

## `route-e-forbidden-support-e3-stability`
`RHTower.RouteEForbiddenSupportStability` (namespace `RHTower.ForbiddenSupport`):
- `card_mul_log_le_log`, `card_le_log_div_log` — an adversarial support has few prime divisors
  above `T`, because their product divides `A`.  This one fact serves both `#S₁ log P₁ ≤ log A`
  and `(FS11)`.
- `norm_cpow_le`, `norm_supportSum_le_card_div`, `norm_supportSum_le_log` — `(FS5)`.
- `sum_inv_le_log` — `(FS10)`.
- `norm_sq_sub_mul_le`, `integral_norm_sq_sub_mul_le` — `(FS6)`.
- `fsExponent`/`fsSmallScale`/`fsLargeScale`/`fsWindow` are `a`,`P₁`,`R`,`h` of `(FS1)`;
  `fsWindow_div_eq` is the EXACT identity `h/(P₁·R/2) = 4 log x`.
- `card_Ioc_floor_le`, `card_scaledWindow_le`, `card_window_le` — `(FS12)`.
- `tendsto_logRpow_div_sqrt`, `tendsto_fsNegligible` — `(FS13)`.
- `eventually_smallScale_lt_largeScale`, `sqrt_add_sub_sqrt_le`, `card_diagonalWindow_le` — §3.
- `mobiusComplexCoefficient_prime_mul_threePrime`, `mul_sqrt_div_eq_sqrt_mul`,
  `abs_amplified_gap_le` — `(FS14)`.

## `route-e-cofactor-amplified-e3-token-supply`
`RHTower.RouteECofactorParityBalance` (namespace `RHTower.CofactorParity`):
- `parityClass`, `oddBase`, `pairMap`, `moebius_two_mul`, `pairMap_mem`, `pairMap_injOn`,
  `half_sum_oddBase_le_sum_parityClass` — the card's "parity balance needs no signed Möbius
  estimate": the `s ↔ 2s` pairing gives EACH parity class at least half the harmonic mass of the
  odd squarefree band-avoiding source set.
- `dyadic_mem_iff`, `le_card_dyadicSlices` — `(6a)`.
Displacement `(5)` and parity `(4)` are `ForbiddenSupport.abs_amplified_gap_le` and
`mobiusCofactorToken_reverses`.

## Do not re-attempt
`(FS4)` and `(FS7)`.  `(FS7)` is provably out of reach of corpus assets:
`RHTower.Sieve.dirichlet_meanValue_theorem` has error `O(N log N)`; even Montgomery--Vaughan's
sharp `O(N)` yields only `O(1/log R)` for the second term, where the card needs `O((log x)^{-2})`.
The saving is the source's Section 5 two-dimensional sieve, not reproduced on the card.
