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

## Normalized correction derivatives

`TheShiftedAmplitudeIsHolomorphic` extends the amplitude to an entire
function and proves the same complex absolute majorant.
`TheCorrectionJetsKeepTheSummableEnvelope.norm_normalizedCorrectionJet_le`
bounds its normalized fibre jet of order `j` at `C` by
`j! exp(4(|C|+1))|W_0|`.

Every positive-order normalized jet tends to zero on each fixed fibre.
Dominated convergence gives
`tendsto_tsum_cutoffNormalizedCorrectionJet_succ`: the corresponding
retained fibre sum tends to zero at every order. Direct Lean checks passed.

The positive-order jet decay also holds for every bounded moving centre
sequence. The declarations
`tendsto_entire_normalized_jet_succ_of_bounded_centres` and
`tendsto_tsum_cutoffNormalizedCorrectionJet_succ_of_bounded_centres`
use the same Cauchy and summable-majorant arguments. Lean check passed.

The summable pair majorant is the pushforward of absolute triple-fibre
mass: `A(m,n)=Σ_{r|gcd(m,n)}|W_0(r,m/r,n/r)|`, with zero values on the axes.
`TheShiftedCorrectionHasASummablePairMajorant` proves summability and
`|Corr_{C/log N}(m,n)|≤exp(4|C|)A(m,n)` for `m,n≤N`, `N>1`.
It also proves coefficient continuity and the zero-shift identity.
Lean check passed; umbrella import added.

`TheCorrectionCoefficientJetsHaveASummableMajorant` transfers these
estimates to the finite divisor coefficients: the normalized jet is
bounded by `j! exp(4(|C|+1))A(m,n)`, its real restriction is the actual
successive derivative, and every positive-order jet tends to zero along
bounded moving centres. Lean check passed; umbrella import added.

`TheCoupledEulerCorrectionPreservesThePolynomialLimit` proves that the
full corrected polynomial row, weighted by `t^k`, tends to
`∫₀¹ t^k (P′−vP)(Q′−vQ) dt`, with profiles evaluated at `1−t`.
The shift may be any convergent sequence. One uniform bound over all
retained dilation pairs permits summation against the absolute pair
majorant. Lean check passed; umbrella import added.
