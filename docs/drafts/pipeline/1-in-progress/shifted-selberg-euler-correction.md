# Uniform correction for reciprocal-logarithmic Selberg shifts

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** A111, `levinson-gate-from-below-square-root-twists.md`.

## Exact arithmetic target

Let `A_c = (μ(n)n^c) * (1/n)` under Dirichlet convolution. At prime powers,

`A_c(p^k) = (1−p^(1+c))/p^k`, `k≥1`.

Local correction coefficients are obtained from
`1−p^(−2)xy(1−p^c x)(1−p^c y)/((1−x/p)(1−y/p))`.
Globally the correction is the pushforward under `(r,u,v)↦(ru,rv)` of
`μ(r) A_{c,r}(u) A_{c,r}(v)/r²`, where the amplitudes have prime support in `r`.
The principal factor has shifted Möbius factors and diagonal coefficient `d^(c−1)`.

## Uniform majorant

For every real `c`,
`|1−p^(1+c)| ≤ (p−1)p^(2|c|)` for `p≥2`.
Multiplicative factorization therefore gives
`|A_c(n)| ≤ n^(2|c|)|A_0(n)|`.

At `c=C/log N`, each retained fibre has `u,v≤N`, so its absolute value is
at most `exp(4|C|)` times the existing absolutely summable correction fibre.
The extra coefficient twist `(ru·rv)^(V/log N)` costs at most `exp(2|V|)`
on the truncated convolution. Fixed fibres converge to their unshifted values.
Thus no new infinite power-weighted divisor majorant is needed.

## Remaining proof obligations

Formalize the parameterized amplitude, exact convolution, and fibre majorant.
Combine the smoothed Möbius test-function limit with harmonic scaling.
Transfer the first two frozen-coefficient displacement jets; their proof
must retain uniformity of the shifted correction, not merely pointwise limits.

## Lean drafts

- `TheShiftedSelbergAmplitudeHasTheSameMajorant`: multiplicative convolution,
  prime-power formula, coefficient continuity, and the amplitude majorant.
  Direct Lean check passed; umbrella import added.
- `TheShiftedSelbergCorrectionKeepsItsSummableEnvelope`: localized fibres,
  their continuity, the common summable envelope, and limiting unit mass
  of the actual finite-cutoff fibre sum. Direct check pending.
