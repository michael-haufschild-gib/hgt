# Exact shifted Selberg factorization and summable correction

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** A111, `levinson-gate-from-below-square-root-twists.md`.

## Statement

For every real `s`, let `A_s=(μ(n)n^s)*(1/n)` under Dirichlet convolution.
Restrict `A_s` to integers supported on the primes of `r`, writing `A_{s,r}`.
The correction is the pushforward under `(r,u,v)↦(ru,rv)` of
`W_s(r,u,v)=μ(r)A_{s,r}(u)A_{s,r}(v)/r²`.
Let `P_s` be the bivariate convolution of the diagonal coefficient
`d^(s−1)` with the two reciprocal Möbius rows. Then

`W_s * P_s (m,n) = μ(m)μ(n) gcd(m,n)^(1+s)/(mn)` for positive `m,n`.

For every finite weight, the principal factor collapses exactly to a
single harmonic sum of its two Möbius transforms, weighted by `d^s`.

For `N>1` and retained fibres `ru,rv≤N`,
`|W_{C/log N}(r,u,v)| ≤ exp(4|C|)|W_0(r,u,v)|`.
The majorant is summable over all three variables; the truncated shifted
fibre sum converges to `1`.

## Proof

At prime powers, `A_s(p^k)=(1−p^(1+s))/p^k` for `k≥1`.
Dirichlet inversion gives `A_s*(μ/n)=μ(n)n^s`.
Consequently the local correction times the principal factor is
`1−x/p−y/p+p^(s−1)xy`. Pair-coprime multiplicativity gives the global identity.
Finite divisor rearrangement and diagonal collapse give the weighted model.

The bound `|1−p^(1+s)|≤(p−1)p^(2|s|)` gives
`|A_s(n)|≤n^(2|s|)|A_0(n)|`. On retained fibres, `u,v≤N`.
Each fixed fibre is continuous in `s`; dominated convergence against the
existing absolute fibre sum preserves total mass `1`.

## Lean

Namespace `GaloisForLFunctions.MultiscaleMollifiedZetaField`:

- `TheShiftedSelbergAmplitudeHasTheSameMajorant`
- `TheShiftedSelbergCorrectionKeepsItsSummableEnvelope`
- `TheShiftedSelbergCorrectionIsMultiplicative`
- `TheShiftedSelbergEulerFactorsCancel.shiftedSelbergCorrection_convolution_principal`
- `TheShiftedSelbergFormIsAHarmonicModel.shiftedSelbergOriginal_weighted_eq_correction_harmonic_model`

Direct Lean checks passed; umbrella imports added. Shifted harmonic limits
and frozen-coefficient displacement derivatives remain separate obligations.
