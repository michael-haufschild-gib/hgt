# Route L — original-Green coordinate completion: facts

- `DeningerOriginalGreenZeroDampingGerm` proves that each native original-prime Green continuation has pole order `-2 * xiSupportMultiplicity rho` at zero damping, with a nonzero coefficient retaining the original prime and both native zeta jets.
- A literal, unnormalised Xi-Hilbert zero-damping lift is formally impossible; a single scalar normalization is finite at every coordinate exactly when it dominates twice every native multiplicity.
- No existing corpus declaration matched a multiplicity-adaptive product-coordinate completion (`research` deep search plus direct Lean-source search).
- `DeningerOriginalGreenCoordinateCompletion` proves an unconditional product-topology limit of the field normalized coordinatewise by `2 * xiSupportMultiplicity`; every limit coordinate is nonzero, and on `a > 1` it is exactly the literal original Green Mellin source times that forced coordinate normalization.
- Audit: source check and exact module build pass; the two principal theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- Not proved: a zero-damping Green/BV source-domain object, product-to-fixed-physical-reader comparison, any normed completion, or RH.
