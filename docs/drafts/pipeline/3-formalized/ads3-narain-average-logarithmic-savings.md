# Rapid logarithmic savings at the Narain boundary

- **ID:** W11-NL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Quantitative saving](ads3-narain-quantitative-boundary-saving.md)

## Theorem

For every positive target-height pair `Y,Z` and every integer `N≥0`,

`yA_YZ(y)+(3/π)log y−B_YZ = o(y^(1/2)|log y|^(−N))` as `y→0+`.

## Proof

Put `L=−log y` and
`w(L)=(log L)^(−2/3)(log log L)^(−5/3)/10^8`.
The quantitative source theorem bounds the normalized remainder by
`C exp(−cLw(L))`, for some `C,c>0`.
The proved eventual inequality `w(L)≥1/log L` and `(log L)²=o(L)` give

`(N+1)log L≤cLw(L)`

for sufficiently large `L`. Hence
`L^N exp(−cLw(L))≤1/L→0`. Dividing the source bound by `√y/L^N`
and substituting `L=−log y` proves the displayed little-o limit.

## Lean

`NarainAverageLogSaving.lean` proves:

- `tendsto_pow_mul_exp_neg_vkWidth`: every polynomially weighted arithmetic saving tends to zero.
- `narainScalarHeatAverage_logarithmic_saving`: the displayed actual-source theorem.

Both endpoint axiom audits contain only `propext`, `Classical.choice`
and `Quot.sound`. The module and all supporting quantitative modules passed final direct
Lean checks and are imported by the umbrella.

The proved [Schwartz theorem](../3-formalized/ads3-narain-boundary-schwartz.md)
gives rapid decay of every boundary and clock derivative. The
[proved quantitative derivative bound](ads3-narain-logarithmic-derivative-saving.md)
gives a common arithmetic saving, factorial control and one threshold across all orders.
The Schwartz theorem uses Landau interpolation and Fourier inversion;
differentiating the scalar error estimate alone would not justify it.

## Gates

- [x] 0 → 1: quantitative saving and width lower bound audited.
- [x] 1 → 2: all logarithmically weighted source limits proved.
- [x] 2 → 3: final direct Lean checks, transitive axiom audits and umbrella import.
