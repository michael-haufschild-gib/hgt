# The Chebyshev estimate at exponent 1/2 is complete

`RHTower.Sieve.exists_norm_sum_vonMangoldt_sub_self_kappa_one_rate`
(`RHTower/Sieve/ChebyshevSharpSelfRateOne.lean`):

    ∃ B ≥ 0, ∀ᶠ N in atTop,
      ‖ ∑_{n ≤ ⌊N⌋} Λ(n) - N ‖ ≤ B · Z · exp( -√(log Z) / 960000 ),
      Z = N + chebWidthOne N + 1.

Unconditional (`[propext, Classical.choice, Quot.sound]`).  Umbrella builds clean, lint passes.

Card: `docs/drafts/pipeline/1-in-progress/chebyshev-exponent-one-half.md`.

## Comparison

- vendored `PNTPlus.MediumPNT` : `ψ - id =O[atTop] x·exp(-c(log x)^{1/10})`
- corpus's own `Chebyshev*` chain : only the qualitative `ψ(N)/N → 1`
- **this chain** : `exp(-√(log N)/960000)` — the classical de la Vallée Poussin exponent `1/2`

## Why it works where Möbius stops at 1/3

`ζ'/ζ` (regular part) is bounded by `C log²|γ|` on the **full width** `(1/40000)/log|γ|` of the
exponent-one region (`exists_bound_zetaLogDerivReg_uniform`).  `1/ζ` is bounded only on width
`log^{-2}` (`exists_zeta_lower_strip`).  Width `log^{-w}` ⟹ saving exponent `1/(w+1)`.

## The five halvings of the exponent

`1/40000` (region width) → `1/80000` (left edge, `saving_exponent_one`) → `1/240000` (balance
against the smoothing's squared price, `price_mul_factor_le`) → `1/480000` (absorbing `log²T`,
`sq_mul_exp_neg_le`) → `1/960000` (absorbing the transfer's `log Z`, `sq_mul_exp_neg_le'`).
The `Y+1 → Y` shift costs a **constant**, never a halving — see
`mem:route_e/chebyshev_shift_is_a_constant_not_an_exponent_2026_08_06`.

## 17 modules

`ZetaLogDerivRegUniform` · `ChebyshevKappaOneData` · `ChebyshevKappaOneContour` ·
`ChebyshevHeightOne` · `ChebyshevRatePowersOne` · `ChebyshevWidthOne` · `ChebyshevBracketBound` ·
`ChebyshevKappaOneShape` · `ChebyshevKappaOneTerms` · `ChebyshevPowersAtHeight` ·
`ChebyshevBalanceOne` · `ChebyshevKappaOneShaped` · `ChebyshevKappaOneCoeff` ·
`ChebyshevCollapseOne` · `ChebyshevFinalCollapse` · `ChebyshevKappaOneThreshold` ·
`ChebyshevKappaOneRate` · `ChebyshevMainTermErrorOne` · `ChebyshevSharpTransferOne` ·
`ChebyshevSharpRateOne` · `ChebyshevSharpMassRateOne` · `ChebyshevSharpSelfRateOne`

## Build discipline that made it compile

- every arithmetic step a **top-level** lemma (heartbeats are per-declaration);
- `mul_le_mul_of_nonneg_*` + `linarith`, never `nlinarith` on a degree-5 product;
- `have hTT : T ^ (1+1) = T*T := by ring` before any `nlinarith` touching that exponent;
- **never `rw` with a self-referential equation** (`chebWidthOne_eq` rewrites inside
  `N + chebWidthOne N + 1`; `log Z = √(log Z)²` rewrites inside the root) — keep it a hypothesis;
- `rw` must hit **every** hypothesis sharing an atom, or `linarith` sees unrelated atoms;
- `Λ` is `ArithmeticFunction.vonMangoldt` notation — never use it as a binder name;
- `lake env lean` does not write the `.olean`; a downstream module needs `lake build` first.

## Next

The Vinogradov–Korobov exponent `3/5` would need VMVT, which is in neither the corpus nor mathlib.
See `mem:route_e/moebius_exponent_half_needs_explicit_formula_2026_08_06` for the explicit-formula
route, which is a different mechanism again.
