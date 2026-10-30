# Macroscopic complete Weil index ceiling

- **ID:** completed-arithmetic-forms-weil-index
- **Stage:** 3-formalized
- **Type:** THEOREM

## Statement

There is a prefix horizon `M₀` such that, for every `M≥M₀`, `N≥M`, and `c>0` with
`cM≤N`, every subspace strictly negative for the actual complete plateau Weil matrix
at length `N` and overlap `c` has dimension at most `N−M`.

In particular, at overlap `3/2` and length `3K`, every strictly negative subspace has
dimension at most `K` for all sufficiently large `K`.

## Proof

The actual principal prefix is the complete length-`M` matrix at overlap `cM/N`.
The unconditional uniform touching theorem makes it positive definite for all sufficiently
large `M`, simultaneously whenever `0<cM/N≤1`.

Restrict a negative subspace to its tail coordinates `M<n≤N`. The restriction is injective:
a vector in its kernel is supported on the prefix, where its complete quadratic form is
nonnegative, contradicting strict negativity unless the vector vanishes. The tail has
exactly `N−M` coordinates, which proves the dimension bound.

Set `M=2K`, `N=3K`, `c=3/2` to obtain the explicit one-third ceiling. Every prime,
Gamma, polar, and mixed entry remains in the original form. The ceiling grows with the
horizon and therefore does not supply a finite limiting index or positivity of the tail Schur form.

## Dependencies

- `eventually_plateauPrefixBlock_posDef`.
- `horizonPrefixSplit` and `plateauPrefixBlock`.
- Dimension monotonicity for an injective linear map.

## Lean declarations

- `CompletedArithmeticForms.eventually_completeWeil_negative_subspace_dim_le_tail`.
- `CompletedArithmeticForms.eventually_three_halves_negative_subspace_dim_le`.

Module: `GaloisForLFunctions/CompletedArithmeticForms/WeilPrefixIndex.lean`.
The final `lake --old env lean` audit passes without output files. The transitive
axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
