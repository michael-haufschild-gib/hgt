# Bordered extended real line and product enhanced space

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Topological bordered-space infrastructure.

## Claim

The inclusion `Real → EReal` is an open embedding with image the complement of `{-∞,+∞}`.
For every topological space `X`, the product inclusion
`X × Real → X × EReal` is an open embedding. These data define the bordered extended real line
and its product with `X`; product boundary is exactly `X × {-∞,+∞}`.

## Paper proof

`EReal` is the order-topological two-point compactification of `Real`; its finite-point inclusion is
an open embedding and has range `{-∞,+∞}ᶜ`. Products of open embeddings are open embeddings.
Taking the product with the identity of `X` gives the asserted product pair and boundary formula.

## Lean artifact

`formal/GaloisForLFunctions/HTGeometry/StokesBorderedEReal.lean` defines `BorderedSpace`, its
boundary, bordered extended real line, product enhanced bordered space, and exact boundary
identifications.

Direct Lean elaboration and targeted build
`lake build GaloisForLFunctions.HTGeometry.StokesBorderedEReal` pass. Axiom audit of every new
declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Dependency audit

- Mathlib `EReal.isOpenEmbedding_coe` and `EReal.range_coe`.
- Mathlib product stability of open embeddings.
- `StokesERealEnhancedProjection.EnhancedCompactification` for ambient product notation.
- No sheaf, ind-, derived, Stokes, arithmetic, or RH hypothesis.

## Hostile audit

- A bordered space is recorded as interior, ambient, inclusion, and open-embedding proof. No proper
  map, sheaf quotient, or six-functor package is smuggled into this structure.
- `EReal` is used as compact ambient line; interior remains `Real`, so endpoints are not treated as
  physical enhanced-time points.
- Product inclusion does not by itself identify categories of bordered-space sheaves.

## Next step

Use ambient projection and interior inclusion when specifying the enhanced quotient.
