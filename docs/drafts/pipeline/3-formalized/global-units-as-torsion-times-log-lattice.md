# Global units as torsion times their logarithm lattice

- **ID:** global-units-as-torsion-times-log-lattice
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Hecke theta Mellin unfolding](../1-in-progress/hecke-theta-mellin-continuation-and-unit-unfolding.md)
- **Lean:** `HTGeometry/NumberFieldUnitsAreTorsionTimesLogLattice.lean`

`numberFieldUnitsEquivTorsionLogLattice` identifies the actual global unit
group with the product of its torsion subgroup and its actual logarithmic
lattice. The inverse is the torsion unit times the product of fundamental
units with integer exponents given by the lattice basis coordinates.

## Proof and exact identities

Mathlib's `NumberField.Units.exist_unique_eq_mul_prod` proves bijectivity
of the torsion/exponent product map. Composing with
`(Units.basisUnitLattice K).equivFun` gives the actual lattice coordinates.

`logEmbedding_numberFieldUnitsEquivTorsionLogLattice_symm` proves the
logarithm of the inverse pair is exactly its lattice point. Torsion maps to
zero; powers of fundamental units map to integer multiples of the actual
lattice basis; the basis reconstruction identity closes the sum.

`numberFieldUnitsEquivTorsionLogLattice_logEmbedding` identifies the second
coordinate of every unit's decomposition with its logarithm.
`numberFieldWeightedLogProfile_unitLatticeCoordinate` recovers the full
place-logarithm profile from that coordinate.

## Verification

The full scratch and final direct source audit passed. All three transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The module is wired into the HTGeometry umbrella; the umbrella was not
compiled. No unit theorem, kernel assertion, or basis property is assumed.

The subsequent theta-periodization construction imports this module and
proves convergence from the actual ideal Gaussian series before exchanging
unit and lattice sums.
