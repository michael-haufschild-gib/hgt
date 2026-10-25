# The actual cofactor action has a complete graph domain

- **ID:** biarithmetic-complete-cofactor-graph
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; closed graph construction)
- **Parent:** [Payment graph norm](../1-in-progress/biarithmetic-payment-graph-norm.md)
- **Statement:** For every complex arithmetic row, its finite cofactor coordinates define a closed graph in the product of the critical Wiener algebra and complex square-summable pronic coordinates. The graph is complete, its input projection is injective, and its Wiener image is exactly the total-energy domain.

## Proof

The positive cell `n+1` has normalized output

`sum_(1<=j<=n+1) k(j)v(floor((n+1)/j))/sqrt((n+1)(n+2))`.

This is a finite continuous linear combination of actual Wiener coefficient
evaluations. Equality with the corresponding `ell2` coordinate is therefore
a closed linear condition on a pair `(k,w)`. Intersecting these conditions
over all cells produces a closed submodule of two Banach spaces. The
inherited maximum norm is complete.

The input kernel determines each output coordinate, so its projection is
injective. Existence of an output is exactly square summability of the
displayed coordinate sequence. No source growth condition is used, and
the source's value at the origin is never read.

## Scope and verification

Graph completeness does not imply that its Wiener image is closed.
Identification with the actual paid ideal, the ideal action, and the
uniform-bound characterization of ambient closedness remain separate
formal statements. The construction uses AOT's coefficient functionals
and Mathlib's existing square-summable sequence space.

Lean: `BiarithmeticGeometry/CofactorGraphDomain.lean`.
Main declarations: `cofactorPronicCoordinate_apply`,
`isClosed_cofactorGraphDomain`, `cofactorGraphDomain_completeSpace`,
`cofactorGraphInput_injective`, `mem_range_cofactorGraphInput_iff`.

- [x] Dependency-closed paper proof.
- [x] Direct repository source check; umbrella import wired.
- [x] Five transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
