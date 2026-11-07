# Completed cubic quotient energy graph

- **ID:** cubic-quotient-energy-graph
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The closure of actual smooth mass-gradient pairs is a complete Hilbert graph with dense smooth core and dense mass range. Its norm squared is the sum of mass and gradient norm squares.

The height-weighted gradient of a compact smooth quotient test is square
integrable on the actual measurable fundamental domain: its squared norm
integrates to the descended Dirichlet energy. Pairing gradients gives the
Dirichlet form. Close these pairs in the Hilbert product of quotient `L²`
and fundamental-domain gradient `L²`; closedness gives completeness and
the product projections give continuous mass and gradient maps.

Lean: `MetaplecticMobiusDescent/TheCubicEnergyGraph.lean`,
`kernelGradientToL2_norm_sq`, `kernelEnergyGraphCore_dense`,
`kernelEnergyGraphCore_norm_sq`, and `kernelEnergyMass_dense`.
Transitive axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

Mass injectivity on the completion is not asserted here; it requires
gradient closability. Adapted from OpenAI `CubicSieve/RadialWindows.lean`
and `CubicSieve/PaddedPassage.lean`.
