# Hecke harmonic sums satisfy the ideal hyperbola identity

- **ID:** hecke-harmonic-sums-satisfy-the-ideal-hyperbola-identity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Mertens programme](../1-in-progress/hecke-character-mertens-via-ideal-hyperbola.md)
- **Lean:** `GaloisForLFunctions/HeckeLFunctions/HeckeHarmonicSumsSatisfyTheIdealHyperbolaIdentity.lean`
- **Statement:** The actual logarithmic harmonic sum equals `sum_(N(p)^k<=N) psi(p)^k log N(p)/N(p)^k * Spsi(floor(N/N(p)^k))`.

## Proof

Multiplication by a nonzero ideal `Q` bijects ideals of norm at most
`floor(N/N(Q))` with multiples of `Q` having norm at most `N`. Applying
this bijection to arbitrary complex weights proves
`ArtinMertens.sum_filter_dvd_idealsLe_eq`.

Insert the existing ideal von Mangoldt identity into a finite weighted
ideal sum and interchange the two finite sums. Reindex the inner sum by
the multiplication bijection. This proves
`ArtinMertens.sum_weight_mul_log_absNorm_idealsLe_eq` before any
multiplicativity assumption.

The ideals of norms in `[1,N]` form a disjoint partition of `idealsLe K N`.
Consequently norm grouping commutes with every norm weight, by
`sum_heckeCoeff_mul_eq_sum_idealsLe`. The harmonic ideal weight
`psi(I)/N(I)` is multiplicative, including all noncoprime zeros.
Substituting this actual weight in the preceding identity gives
`heckeLogarithmicHarmonicSum_eq_hyperbola`.

`heckePrimePowerMertensWeight` and `heckePrimePowerMertensSum` define the
actual finite prime-power terms and their sum. Their absolute values
satisfy the untwisted logarithmic norm bound by `norm_heckeValue_le_one`.

## Audit

The complete scratch passes without warnings. The weighted von Mangoldt
identity, norm regrouping, and actual hyperbola theorem have transitive
axiom sets `[propext, Classical.choice, Quot.sound]`.
The module is wired into the Hecke umbrella. Its final direct source audit
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeHarmonicSumsSatisfyTheIdealHyperbolaIdentity.lean`
passes without warnings. Both nontrivial and trivial Mertens consumers
are written; its required olean is not built yet.
