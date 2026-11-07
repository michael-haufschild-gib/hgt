# Cubic reciprocity from Frobenius

- **ID:** cubic-reciprocity-frobenius
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Canonical primary generators at Eisenstein primes of distinct residue characteristics satisfy cubic reciprocity.

## Statement and proof

Let `P,Q` be primes away from three, of distinct residue characteristics,
with canonical primary generators `p,q`. Then `(q/P)₃=(p/Q)₃`.

Reduction modulo `Q` is injective on cubic roots of unity. In an extension of
`O/Q` containing a primitive additive character of `O/P`, the cubic Gauss
identity remains `G³=−p N(P)`. Frobenius to the power `N(Q)` fixes the cubic
character values and shifts the additive character by `N(Q)`. Comparing this
with `G^(N(Q))=(G³)^((N(Q)−1)/3) G` and cancelling the nonzero Gauss sum gives

`(N(Q)/P)₃ (p N(P)/Q)₃ = 1`.

The analogous identity with `P,Q` exchanged has the same nonzero norm-symbol
factor. Cancelling it proves reciprocity. The minus sign disappears because
a cubic character takes value one at minus one. Distinct characteristics
ensure all cardinalities being cancelled remain nonzero after reduction.

## Lean and scope

Module: `MetaplecticMobiusDescent/CubicReciprocityFromFrobenius.lean`.

- `CubicFrobenius.gauss_cube_residue_relation`
- `Eisenstein.cubic_reciprocity_distinct_residue_char`
- `Eisenstein.primaryGenerator_reciprocity`

Direct `lake --old env lean` passed; three endpoint axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella import wired. Argument
adapted from the external OpenAI development; attribution and license accompany
the module. This is classical cubic reciprocity, not a new cancellation bound.
Equal residue characteristics are outside this theorem's scope.
