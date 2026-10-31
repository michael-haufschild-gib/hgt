# Finite-index Haar carriers split modulo polynomial kernels

- **ID:** HAAR-RELATIVE-PONTRYAGIN-SPLITTING
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** Every Hermitian finite-index kernel `k` on `Aff(ℚ)` with integer Haar successor has a unique decomposition `k=p+ψ∘slope+Q`, where `p` is positive definite with the same successor, `ψ` is Hermitian with `ψ(1)=0`, and `Q` is Hermitian, has finite column rank and polynomial translation fibres, and vanishes on both translations and dilations. Its index is exactly `κ(k)=κ(ψ∘slope+Q)≥κ(ψ)`.

## Canonical decomposition

The [finite affine orbit of period defects](haar-period-defects-have-a-finite-affine-orbit.md)
provides a finite-dimensional covariant correction space. Its
[canonical polynomial primitive](finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md)
gives `Q`, with both axis readings zero, and leaves a bi-integer-invariant
finite-index remainder.

The [invariant factorial moving-form limit](bi-integer-invariant-haar-kernels-split-into-positive-and-slope-parts.md)
splits this remainder into a positive Haar kernel and a Hermitian slope kernel.
The construction uses the actual column representation. Evaluation at identity
gives `ψ(1)=0`.

## Uniqueness

Finite column rank gives polynomial translation fibres. The positive Haar and
slope terms are integer-invariant, so the translation difference and zero
dilation reading determine `Q` uniquely.

After fixing `Q`, suppose `p+ψ∘slope=p′+ψ′∘slope`. Applying exact Haar slope-index
preservation to `p′=p+(ψ−ψ′)∘slope` makes `ψ−ψ′` positive definite, since `p′`
has index zero. Both positive Haar kernels equal one at identity, so
`(ψ−ψ′)(1)=0`. The positive-kernel norm bound forces `ψ=ψ′`, and then `p=p′`.

## Exact index and converse

[Polynomial quadrature](haar-addition-preserves-index-on-polynomial-translation-fibres.md)
removes the positive Haar part without changing negative index:

`κ(k)=κ(ψ∘slope+Q)`.

Restriction to dilations and subadditivity give
`κ(ψ)≤κ(k)≤κ(ψ)+κ(Q)`. No additivity between `ψ` and `Q` is asserted.
For `d=dim(columnSpan Q)`, finite-rank perturbation also gives
`κ(k−Q)≤κ(k)+d` and `κ(k)≤κ(k−Q)+d`. Since `κ(k−Q)=κ(ψ)`,
finite index of `k` is equivalent to finite index of `ψ`.

Conversely, any sum with the stated positive, Hermitian, finite-rank and
zero-axis properties, together with `ψ(1)=0` and finite `κ(ψ)`, is Hermitian,
has the Haar successor, and has finite index. These conditions therefore give
a complete classification.

## Lean formalization

- `Haar/RelativeSplit.lean`: `exists_unique_haar_relative_split` and `haar_split_correction_unique`.
- `Haar/Classification.lean`: `finite_index_haar_iff_relative_split`, `haar_relative_split_index_eq_polynomial_residual`, `haar_relative_split_slope_index_le`, `haar_relative_split_finite_index_iff`, and `haar_relative_split_index_bounds`.
- `HeckeKreinToeplitz/Index/FiniteRankStability.lean`: both rank-perturbation bounds and preservation of finite index.

The `Haar/` paths are under `AdelicKreinGeometry/`. All listed modules passed
direct `lake --old env lean` audits. Printed endpoint axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
