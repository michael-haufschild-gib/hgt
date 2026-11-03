# F2 — finite harmonic transport through the actual Hecke bases

- **Stage:** 3-formalized
- **Result:** For `n>0`, summation over the actual Hecke bases converts left-generator harmonicity into right-generator harmonicity.
- **Dependency:** [Unique source-matrix normal forms and suffix partitions](f2-hecke-positive-word-reduction.md).

Let `H` be a complex-valued function on nonnegative matrices of determinant `n`, satisfying

`H(A)=H(LA)+H(RA)`.

The exact finite identity is

`Σ_(B∈heckeSet n) [H(BL)+H(BR)] = Σ_(B∈heckeSet n) H(B)`.

Here matrices are identified with the integral quadruples in the literal source Hecke operator.

## Finite proof

Iteration of the binary identity gives `Σ_(|W|=N) H(M(W)A)=H(A)` for every `N`.

For any finite suffix partition with words `u_i` of length at most `N`, each length-`N` word is uniquely `v u_i`. Expanding `H(M(u_i)A)` by words `v` of length `N−|u_i|` and reindexing the finite sum gives

`Σ_i H(M(u_i)A)=H(A)`.

For each source branch `(B,b)`, take its unique normal form `B b=M(u)C`. The audited matrix reduction gives `|u|≤8n`. Fix a target `C` and choose `N=8n+1`. The exact suffix partition theorem applies, so the sum of `H(B b)` over branches targeting `C` is `H(C)`.

Sum over terminal targets. Every source branch has exactly one target, giving the asserted finite identity. All sums are finite; no limiting measure, convergence premise, or spectral eigenfunction equation enters.

## Scope

The harmonicity condition is the binary functional equation to be transported. Applying this identity to physical Lewis periods requires proving it for the literal homogeneous period and identifying the resulting weighted source sums. The identity does not imply boundary eigenvalues or positivity.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/HeckeWordHarmonicTransport`:

- `sum_heckeWords_of_harmonic`
- `sum_heckeSuffixPartition`
- `hecke_sum_right_harmonic`

Individual final `lake --old env lean` audit passed without warnings. All three declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.
