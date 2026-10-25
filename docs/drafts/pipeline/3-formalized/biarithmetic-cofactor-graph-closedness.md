# Wiener closedness is a uniform cofactor-energy bound

- **ID:** biarithmetic-cofactor-graph-closedness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Payment graph norm](../1-in-progress/biarithmetic-payment-graph-norm.md)
- **Statement:** For every complex arithmetic row, the complete cofactor graph has maximum norm. Its input image is Wiener closed exactly when its total output norm is bounded uniformly by a constant times the input norm.

The graph is complete and its input projection injective. The Banach
closed-range theorem identifies closedness with an inverse norm bound.
For the maximum norm, an output bound `C` gives inverse bound `max(1,C)`;
any inverse bound controls the output. No Hilbert structure on the Wiener
input space is required.

Lean: `BiarithmeticGeometry/CofactorGraphClosedness.lean`.
Audited declarations: `norm_cofactorGraphDomain` and
`isClosed_range_cofactorGraphInput_iff`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CofactorGraphClosedness.lean`.
- [x] Both transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

This is an exact criterion, not an assertion that every source satisfies
the uniform energy bound. The graph action and source-specific Fredholm
classification remain separate obligations.
