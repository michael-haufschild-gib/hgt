# Finite source extensions give exact formal cofactor composition

- **ID:** biarithmetic-pronic-finite-extension
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Payment graph norm](../1-in-progress/biarithmetic-payment-graph-norm.md)
- **Statement:** Every finite complex source horizon extends to the completed pronic Hilbert space. Its integrated Wiener action agrees with the formal finite cofactor action at every prescribed coordinate. Consequently `P_a(P_b v)=P_(a*b)v` holds for every source row, without a growth premise.

Normalize the prescribed positive cells by their pronic square roots and
extend by zero. Finite support supplies square summability. The existing
positive-coordinate isometry places this vector in the completed dilation
representation. At horizon `n`, each cofactor reads only cells through `n`,
so representation composition gives the formal identity at that horizon.

Lean: `BiarithmeticGeometry/PronicFiniteExtension.lean`.
Audited declarations: `pronicPositiveCoordinates`,
`pronicFiniteExtension_coordinate`, `pronicFiniteExtension_wiener`,
and `formalWienerCofactor_comp`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/PronicFiniteExtension.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

The extension is chosen separately for each finite horizon. No membership
of the original infinite source row in the pronic Hilbert space is asserted.
