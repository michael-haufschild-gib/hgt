# Anticommuting Pauli observer-rank dominance

- **ID:** `anticommuting-pauli-observer-rank-dominance-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / noncommuting exceptional-carrier exclusion
- **Date:** 2026-08-05
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/AnticommutingPauliObserverRankDominance.lean`
- **Paper proof:** `anticommuting-pauli-observer-rank-dominance.md`

## Exact theorem

Every finite pairwise anticommuting family `A` of `n`-qubit Pauli words obeys

\[
 |A|\leq2n+1.
\]

For `n>=2` and locality order `q>=2`, its cardinality plus the exact
product-input observer rank is at most the number of nonidentity
weight-at-most-`q` Pauli directions:

\[
 |A|+2\sum_{k=1}^{q}{n\choose k}
 \leq\sum_{k=1}^{q}3^k{n\choose k}.
\]

Thus every canonical anticommuting spherical exact-return carrier has
transverse coefficient codimension at least observer rank.

## Formal declarations

The symplectic and counting half, in
`HTGeometry/AnticommutingPauliObserverRankDominance.lean`:

- `Quantum.augmentedPauliVector_linearIndependent`;
- `Quantum.card_pairwiseAnticommutingPauli_le`;
- `Quantum.two_mul_add_one_le_commutingPauliCapacity`;
- `Quantum.pairwiseAnticommutingPauli_card_add_observerRank_le_pauliWeightCount`.

The carrier half.  `HTGeometry/ScalarSquareExponential.lean` proves that in a complete
normed complex algebra an element with `M * M = -(r^2) . 1` has
`exp M = cos r . 1 + sinc r . M`, by splitting the exponential series into its even and odd
halves; the odd half is the sine series divided by its argument, so `Real.sinc` makes the
statement uniform at the origin.  `HTGeometry/AnticommutingInvolutionCarrier.lean` proves that a
real combination of pairwise anticommuting involutions squares to the sum of the squared
coefficients — every cross term is cancelled by its transpose — and composes the two into the
cosine–sine law.

The Pauli instantiation, in `HTGeometry/AnticommutingPauliCarrierExponential.lean`:

- `Quantum.toMatrix_mul_self` — a Pauli word is an involution;
- `Quantum.toMatrix_add_toMatrix_swap_eq_zero` — symplectically paired words anticommute as
  matrices;
- `Quantum.star_toMatrix` — a Pauli word is Hermitian, being unitary and an involution;
- `Quantum.pauliCarrier_mul_self` — equation `(13)`;
- `Quantum.exp_neg_I_smul_pauliCarrier` — equation `(14)`;
- `Quantum.exp_neg_I_smul_pauliCarrier_eq_one` — every sphere of radius in `2πℕ` is an exact
  identity-return set;
- `Quantum.observerRank_le_pauliWeightCount_sub_card` — equation `(4)`.

## Verification

Foreground target compilation passed with:

```text
lake env lean GaloisForLFunctions/HTGeometry/AnticommutingPauliObserverRankDominance.lean
```

Cached foreground compilation passed. Project lint passed. Axiom audit of
the load-bearing declarations reports only `propext`, `Classical.choice`,
and `Quot.sound`.

## Boundary

This closes pairwise anticommuting Pauli carriers only. It does not classify
arbitrary noncommuting Lie closures, nonlinear fast-forwardable components,
or circuit-selected unions, and therefore does not prove the parent
fixed-time shortcut-action conjecture.
