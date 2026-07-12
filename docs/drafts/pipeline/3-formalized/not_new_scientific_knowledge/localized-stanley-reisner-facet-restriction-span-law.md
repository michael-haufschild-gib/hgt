# Localized Stanley--Reisner facet-restriction span law

- **ID:** `localized-stanley-reisner-facet-restriction-span-law`
- **Stage:** 3-formalized
- **Type:** COMMUTATIVE-ALGEBRAIC ASSEMBLY BRIDGE
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [STANDARD PARENT THEORY]`
- **Statement:** The quotient by a localized finite Stanley--Reisner ideal embeds in the product of
  its localized facet quotients, and a family of quotient classes is linearly independent over any
  coefficient field acting on the localization if and only if its complete family of facet
  restrictions is linearly independent.

## Exact law

For a family of ideals `J_s` in a commutative algebra `A`, simultaneous reduction

```text
A -> product_s A/J_s
```

has kernel `intersection_s J_s`.  Therefore

```text
A/(intersection_s J_s) -> product_s A/J_s
```

is injective.  Its underlying linear map preserves and reflects linear independence.  Applying the
formal localized facet decomposition of a Stanley--Reisner ideal gives the same conclusion for the
global localized Stanley--Reisner quotient and its facet restrictions.

## Lean realization

`GaloisForLFunctions.HTGeometry.FacetRestrictionEmbedding` proves:

- `ker_facetQuotientMap`;
- `facetQuotientEmbedding_injective`;
- `linearIndependent_facetQuotientEmbedding_iff`;
- `localizedStanleyReisnerIdeal_eq_iInf_localizedFacetIdeal`;
- `localizedStanleyReisnerFacetEmbedding_injective`;
- `linearIndependent_localizedStanleyReisnerFacetEmbedding_iff`.

The module builds unconditionally in the project toolchain.

## Boundary

This closes the commutative-algebraic identification between global localized classes and complete
facet restriction rows.  The remaining facet-sewn obligation is analytic-algebraic assembly:
encode each finite structural operator family as those restriction rows acting on a finite packet
of the formally free upper-end prime-log orbit, then apply the exact differential-operator matroid
law.

## Gates

- [x] complete paper proof
- [x] complete unconditional Lean formalization
- [x] preservation and reflection of linear independence
- [x] no independent novelty claim
