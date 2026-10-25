# The Vaughan convolution separates its mean and logarithmic fluctuation

- **ID:** vaughan-convolution-mean-and-logarithmic-fluctuation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** The actual truncated Vaughan convolution splits into its harmonic mean and a divisor-square bounded fluctuation with every uniform logarithmic prefix saving.

## Exact arithmetic statement

Write `a_(U,V)=μ_≤U*μ_≤V*1`, `H_U=Σ_(d≤U)μ(d)/d`, and
`r_(U,V)(d)=a_(U,V)(d)-H_UH_V`. For positive `d`,
`|r_(U,V)(d)|≤2τ(d)²`, and its reciprocal damped mass is absolutely
summable for every `ε>0`. For every natural `q`, uniformly over all `U,V`,

`|Σ_(d≤n)r_(U,V)(d)|≤B_q n/(log n)^q`

eventually. For `0<ε≤1/2`, its actual centered damped floor prefix satisfies

`|A_(r,ε)(n)|≤K_(ε,q) n^(1-ε)/(log n)^q`

with one threshold for every cutoff pair. No additional arithmetic estimate
is assumed: the checked undamped convolution theorem supplies the partial-sum
bound, and the checked divisor-square transfer supplies the damped bound.

The centered third Vaughan row has the exact decomposition

`e₂(n)=-H_UH_V A_(1,ε)(n)-A_(r,ε)(n)`.

Its actual reciprocal mass is the negative of the third Vaughan mean. This
identity follows from uniqueness of the floor-average limit, then linearity
of the absolutely convergent reciprocal masses and finite floor sums.

## Lean declarations and audit

`TheVaughanConvolutionSeparatesItsSmoothMean.lean` defines
`pmVaughanConvolutionFluctuation` and `pmVaughanConvolutionFluctuationPrefix`.
Its nine audited theorems are:

- `abs_pmVaughanConvolutionFluctuation_le`
- `summable_pmVaughanConvolutionFluctuation_div`
- `sum_pmVaughanConvolutionFluctuation`
- `exists_uniform_pmVaughanConvolutionFluctuation_log_rate`
- `exists_uniform_pmVaughanConvolutionFluctuation_prefix_log_rate`
- `summable_damped_pmPronicVaughanSmallSmallCoeff_div`
- `tsum_damped_pmPronicVaughanSmallSmallCoeff_div`
- `pmPronicVaughanCentredPiece_smallSmall_eq_prefix`
- `pmPronicVaughanCentredPiece_smallSmall_eq_unit_add_fluctuation`

All nine scratch transitive axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Producing and final direct
`lake --old env lean` checks passed. The module is wired into the BVI
umbrella; its scratch file was removed. No limits were raised.

The uniform prefix-to-energy and complete Gram consequences remain under
formalization. These logarithmic bounds do not prove a fixed power gain or
resolve Q-I.
