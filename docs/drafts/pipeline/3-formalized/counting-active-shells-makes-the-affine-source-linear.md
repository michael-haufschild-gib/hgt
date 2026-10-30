# Counting active shells makes the affine source linear

- **ID:** active-affine-shell-count
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For every conductor `q`, shift family, `c>0`, and `X≥1`, the literal affine shell source has absolute value at most `2(log 4+4)φ(q)c`. Its signed mean has the same bound, and its error is at most twice this quantity.

## Paper proof

Let `G` be the autocorrelation of the supported profile and `M=∫φ²>0`. Interchange the finite prime-power and shell sums before taking absolute values. For a fixed prime-power index `k≤X`, support forces `h<ck/X`. There are at most `ck/X` positive integers satisfying this inequality. Each term has absolute value at most `φ(q)MΛ(k)/k`, so their sum is at most `φ(q)McΛ(k)/X`.

Sum over every `1≤k≤⌊X⌋`, use `ψ(X)≤(log 4+4)X`, and multiply by the exact normalization `2/M`. This gives the stated linear bound, uniformly in all shifts and affine multipliers. The signed mean inherits it from the already formalized source convergence. The error bound follows by the triangle inequality.

## Relevance

The previous quadratic estimate bounded each shell separately and counted all shells at every prime-power index. Counting only active shells removes one overlap factor. This theorem is uniform in the conductor and retains every prime power; quantitative residue equidistribution and negative-eigenvector confinement remain separate gaps.

## Lean proof

`CriticalArithmeticCorrelationTheory/CountingActiveShellsMakesTheAffineSourceLinear.lean`:

- `sum_abs_shellAutocorr_samples_le`
- `abs_affinePrimeShellCorrectionOfShift_le_linear`
- `abs_shellCorrectionOfShift_mean_le_linear`
- `abs_affineShellCorrection_error_le_linear`

Final `lake --old env lean` check passes. All four declarations use only `propext`, `Classical.choice`, `Quot.sound`.
