# Spectrum of the weighted torsion limit

- **ID:** hhac-weighted-torsion-spectrum
- **Stage:** 1-in-progress
- **Type:** SPECTRAL CLASSIFICATION
- **Status:** Compact self-adjoint representation formalized; sign and Hilbert–Schmidt classification open

## Target

For every `δ>0`, the actual torsion-limit form on `Hδ` should represent a
compact self-adjoint operator with infinitely many positive and negative
directions. Its Hilbert–Schmidt threshold should be exactly `δ>1/2`.

This would distinguish infinite arithmetic rank from positivity and show
whether finitely many correction directions could repair the torsion limit.
It depends on the actual operator construction in
[weighted torsion completion](../3-formalized/hhac-weighted-torsion-form-completion.md).

## Mathematical mechanisms

The limit is bounded for every positive conductor weight. For `0<β<δ`,
the coefficient-preserving inclusion `J:Hδ→Hβ` multiplies normalized conductor
coordinates by `n^((β−δ)/2)`. Its finite-coordinate truncations have finite rank,
and their operator-norm error is bounded by `(N+1)^((β−δ)/2)→0`.
Thus `J` is compact. The original absolutely convergent series gives
`Lδ(u,v)=Lβ(Ju,Jv)`, so the limit map into the continuous dual is compact.
Riesz representation then gives the self-adjoint Hilbert operator. This factorization and the compact self-adjoint representation are formalized
for the actual coefficient maps.

For distinct sufficiently large odd primes `q`, restrict to the arithmetic
coefficients supported on `{q,2q}`. Verify the exact matrix

`[[d(q), −log(2)/√2], [−log(2)/√2, d(q)+log(2)]]`,

where `d(q)=log(q)/(q−1)`. Different prime pairs have zero mixed entries.
The vector `(1,1)` then has value
`2d(q)−(√2−1)log(2)`, negative for all sufficiently large `q`, since `d(q)→0`.
The second coordinate has positive value. Finite linear combinations of
distinct negative pair vectors give negative definite subspaces of arbitrarily
large dimension. Any map to a fixed finite-dimensional correction space has
a nonzero kernel on a sufficiently large such subspace. These are compressions; invariance
of their span under the full operator is not asserted.

In normalized Hilbert coordinates the prime entries are
`−P(m,n)/(mn)^(δ/2)`. Divisibility suggests the exact square-sum decomposition

`Σ_{m≠n} P(m,n)²/(mn)^δ`
`=2(Σ_m m^(−2δ))(Σ_{t≥2} Λ(t)²/t^(1+δ))`.

The diagonal contributes `Σ_n d(n)²/n^(2δ)`. Even conductors satisfy `d(2k)≥log 2`, so their diagonal squares alone
should force divergence at `δ≤1/2`. The logarithmic envelopes should give
convergence above that boundary. Reindexing, summability and the operator interpretation
all require proofs.

## Established input and distinction

`weightedProbeInclusion_coefficients` and `weightedProbeInclusion_compact`
formalize the coefficient-preserving compact inclusion for every `β<δ`.
`spacingLimitOperator_factor` proves the actual form factorization.
`spacingLimitHilbertOperator_inner`, `_selfAdjoint` and `_compact` identify
the original pair series with a compact self-adjoint Hilbert operator for
every positive weight. Infinite sign directions and the Hilbert–Schmidt classification remain open.

The existing `ArithmeticIntersectionTheory.spacingLimit_not_nonneg` already
refutes positivity on `{1,2}`. The stronger target here concerns arbitrarily
large positive and negative subspaces on the completed carrier, including
negative vectors annihilating any fixed finite family of linear constraints.
Its positive content includes exact prime-pair compressions, compactness and
the sharp Hilbert–Schmidt boundary.

## Positive survivor required for any sign obstruction

If finite-rank sign repair fails, retain the exact arithmetic compressions,
compactness and sharp Hilbert–Schmidt classification, with their Lean status.
A renamed assertion of infinite negative index is not sufficient salvage.
No conclusion about the full Weil form or its archimedean payment follows
from the torsion limit alone.

## Existing spectral background

[Hilberdink–Pushnitski](https://arxiv.org/abs/2110.14323) prove compactness and
power eigenvalue asymptotics for the LCM matrices
`E(σ,τ)_(m,n)=(mn)^σ/lcm(m,n)^τ` in their stated parameter range.
Substitution `τ=1`, `σ=(1−δ)/2` identifies the positively weighted normalized
gcd majorant with this family, with exponent `τ−2σ=δ`. This algebraic
identification locates the compactness mechanism in established arithmetic
operator theory. The further novelty audit concerns the actual torsion
kernel, its prime-pair compressions and regulated comparison; no priority
claim follows from the preliminary search.

The related [indefinite LCM-matrix family](https://arxiv.org/abs/2401.06892)
of Hilberdink–Pushnitski also has compactness and infinitely many eigenvalues
of each sign in its parameter range. Neither that theorem nor the earlier
positive LCM family identifies this variable-diagonal torsion kernel.
Existing corpus constant-counterterm index theorems likewise use a different
diagonal. No novelty priority is claimed for compactness or orthogonal
negative-vector arguments themselves.
