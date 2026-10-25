# Exact arithmetic coordinates of the completed Wiener action

- **ID:** biarithmetic-pronic-wiener-coordinates
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Payment graph norm](../1-in-progress/biarithmetic-payment-graph-norm.md)
- **Statement:** Each integer coordinate of the completed pronic dilation is exact floor division. The full critical Wiener action at that coordinate is exactly its finite arithmetic cofactor sum.

Undoing the positive-cell normalization defines a continuous linear
functional. Passing that functional through the absolutely convergent
operator series removes every index above the observed cell: its floor
quotient is zero, where the extended row vanishes. The remaining finite
sum is the arithmetic cofactor formula.

Lean: `BiarithmeticGeometry/PronicWienerCoordinates.lean`.
Audited declarations: `pronicRowCoordinate_dilation` and
`pronicRowCoordinate_wiener`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/PronicWienerCoordinates.lean`.
- [x] Both transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

This theorem concerns vectors in the completed pronic space. Extending
the resulting finite identities to arbitrary formal source rows is a
separate finite-extension obligation.
