# Finite-index Mautner rigidity for the Haar successor

- **ID:** HAAR-FINITE-INDEX-MAUTNER
- **Stage:** 1-in-progress
- **Type:** THEOREM
- **Parent:** [O5](weil-positivity-five-structural-mechanisms.md)
- **Statement:** A Hermitian kernel on `Aff(ℚ)` with nonzero Haar successor `c·1_ℤ` and dilation correlation continuous at identity has infinite negative index.

## Obstruction

The [cyclic Haar argument](cyclic-haar-averages-force-infinite-index-at-continuous-dilations.md)
proves the statement without Hecke support or an integer-invariance premise.
Translation-period defects have finite affine orbit; their canonical polynomial
primitive vanishes on both axes and restores integer invariance. Nonnegative
moving subspaces and cyclic averaging make fixed-projection Grams converge to
`J−I`, contradicting every finite index bound.

Hermitian symmetry makes `c` real. Negative `c` already gives arbitrarily large
negative translation Grams; positive `c` reduces to the normalized Haar case.
Extension from positive slopes and rational-affine restriction give the same
obstruction on `Aff⁺(ℚ)` and on `ℚ⁺ ⋉ (ℝ × 𝔸_f)` with diagonal scalar action.
The actual finite-adelic Haar overlap integral equals the integral-adele indicator.

`Haar/ScaledHaarObstruction.lean`, `PositiveAffineObstruction.lean`,
`FiniteAdelicReading.lean`, and `AdelicObstruction.lean`, under
`AdelicKreinGeometry/`, passed direct Lean audits with transitive axioms exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Positive structure

Every finite-index integer-Haar kernel has a
[unique relative split](../3-formalized/finite-index-haar-carriers-split-modulo-polynomial-kernels.md)
`k=p+ψ∘slope+Q`: positive Haar `p`, Hermitian slope `ψ`, and a finite-rank
Hermitian polynomial correction `Q` vanishing on both axes. Its exact index is
`κ(k)=κ(ψ∘slope+Q)≥κ(ψ)`. The construction uses the actual column representation;
no boundedness or topological representation hypothesis is added.

The [logarithmic carrier](../3-formalized/the-haar-successor-admits-one-negative-square.md)
has index one. [Mixed polynomial carriers](../3-formalized/axis-invisible-affine-polynomials-realize-arbitrary-finite-index.md)
preserve both Haar axis readings and realize every index at least two. Their
dilation readings are discontinuous. The
[quadratic example](../3-formalized/mixed-polynomial-affine-perturbations-preserve-both-axis-readings.md)
shows why the finite-rank term cannot be omitted.

The [sharp punctured-limit classification](../3-formalized/finite-index-haar-dilation-limits-are-exactly-nonpositive.md)
gives exactly real limits `L≤0`, with minimum index zero at `L=0` and one at `L<0`.
The [subgroup-indicator classification](../3-formalized/continuous-affine-dilations-classify-subgroup-indicator-successors.md)
gives finite-index continuous-dilation carriers exactly for `H={0}` and `H=ℚ`,
with positive carriers at both endpoints. These results are formalized.
The completed paper proof of
[proper-subgroup polynomial index preservation](proper-subgroup-carriers-preserve-polynomial-fibre-indices.md)
still awaits its Lean audit.
