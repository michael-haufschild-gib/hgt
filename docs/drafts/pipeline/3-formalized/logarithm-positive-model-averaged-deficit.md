# Averaged deficit of the positive-generator model

- **ID:** SPL-positive-model-average
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** The first-Riesz count deficit has exact logarithmic order
  after normalization by the endpoint.

## Statement

For the odd-prime system with extra norms three and four, put
`R(X)=Σ_{g: norm(g)≤X}(X−norm(g))=∫₀ˣN(t)dt`. For every `X≥1`,

`X log X/(12 log 3)≤X²/2−R(X)≤(2/3)X(log X/log 3+1)+X/2`.

Thus the integrated slope-one discrepancy is nonpositive, with magnitude
of exact order `X log X`. The pointwise error and exceptional-zero distance
remain separate questions.

## Proof

For a fibre of norm step `q`, let `J=⌊(X/q+1)/2⌋`. Its weighted odd-integer
count is `JX−qJ²`; its difference from `X²/(4q)` is
`q(J−X/(2q))²`, between zero and `q/4`.

First sum over powers of four, at endpoint `Y`. Choose
`4^B≤Y<4^(B+1)`. The finite rounding terms sum to at most `Y/3`, and the
omitted geometric main term is between `Y/12` and `Y/3`: its exact value
is `Y²/(3·4^(B+1))`, and `Y<4^(B+1)≤4Y`. Hence that count lies
between `Y²/3−2Y/3` and `Y²/3−Y/12`.

Next sum over powers of three. Each retained exponent costs between `X/12`
and `2X/3`; the remaining geometric main term costs at most `X/2`. There are
`⌊log X/log 3⌋+1` retained exponents, which is at least `log X/log 3`.

The coordinate bijection identifies these sums with the actual weighted
norm ball. Integrating the finite family of norm-threshold indicators
identifies it with `∫₀ˣN(t)dt`, retaining every norm multiplicity.

## Lean proof

Module `SumProductArithmeticOfTheLogarithm/PositiveNearCountRiesz.lean`,
namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount`:

- `rieszCount`: the actual weighted norm-ball sum.
- `riesz_log_bound`: the two explicit bounds.
- `rieszCount_eq_integral_count`: the exact count integral.
- `integral_count_deficit`: the bounds for that integral.

Direct source check and capstone dependency audit pass. Only `propext`,
`Classical.choice`, `Quot.sound` occur. No external novelty claim.
