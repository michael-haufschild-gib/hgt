# Uniform logarithmic cancellation for every truncated Möbius receiver

- **ID:** uniform-logarithmic-truncated-mobius-receivers
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** Every truncated Möbius partial sum and positively damped centered floor prefix shares each prescribed logarithmic saving, uniformly over the truncation cutoff.

## Exact result

For every natural `q`, one constant and one threshold work for all cutoffs `U`:

`|Σ_(d≤n) μ_≤U(d)| ≤ C_q n/(log n)^q`.

For every `0<ε≤1/2` the corresponding centered damped floor prefix satisfies

`|A_(μ_≤U,ε)(n)| ≤ K_(ε,q) n^(1-ε)/(log n)^q`,

again with a common threshold for all `U`. The reciprocal mass in this prefix
is its actual absolutely convergent series; no arithmetic cancellation input
is added as a premise.

The truncated partial sum is exactly `M(min(U,n))`. Below `sqrt(n)` the
absolute bound pays the prefix; above it, the actual arbitrary logarithmic
Mertens theorem applies and `log(min(U,n))≥(log n)/2`. The checked generic
divisor-square damped floor transfer gives the second result.

## Lean audit

`UniformLogarithmicCancellationInTruncatedMobiusReceivers.lean` proves:

- `exists_uniform_sum_truncatedMoebius_log_rate`
- `exists_uniform_patternPrefix_truncatedMoebius_log_rate`

Both corrected scratch transitive axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Producing and final direct
`lake --old env lean` checks passed. The module is wired into the BVI
umbrella, and its scratch file was removed. No limits were raised.

The full uniform Gram and endpoint mixed-pairing consequences remain under
formalization. These logarithmic rates do not give a fixed power saving
or resolve Q-I.
