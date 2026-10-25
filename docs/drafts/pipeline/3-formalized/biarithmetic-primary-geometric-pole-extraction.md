# Primary geometric pole extraction with a convergent remainder

- **ID:** biarithmetic-primary-geometric-pole-extraction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Intrinsic golden module](../1-in-progress/biarithmetic-intrinsic-golden-module.md)
- **Statement:** For a polynomial numerator and distinct primary root `a` away from zero and one, reciprocal evaluation extracts the primary geometric coefficient exactly. The remainder retains the double pole at one and the secondary geometric factor; it converges absolutely wherever both retained factors do.

Let `S_b(X)=(1-X)²(1-bX)` and `C=P(1/a)/S_b(1/a)`.
Then `P-C S_b` vanishes at `1/a`, so polynomial division gives
`P-C S_b=(1-aX)Q`. Multiplying by the formal geometric inverses
proves the exact series decomposition. If `deg P<=3`, then `deg Q<=2`.
Absolute summability of the remainder holds at every `u` with `|u|<1`
and `|bu|<1`; no separation between `b` and one is needed.

Lean: `BiarithmeticGeometry/GeometricPoleExtraction.lean`.
Audited declarations: `geometricPoleRemainderPolynomial_factorization`,
`geometricPoleRemainderPolynomial_natDegree_le`, `geometricPole_extraction`,
and `geometricPole_remainder_absoluteSummableAt`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/GeometricPoleExtraction.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

The actual intrinsic golden specialization remains a separate dependent proof.
