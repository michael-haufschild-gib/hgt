# Termwise two-local Gaussian one-draw growth law

- **ID:** inverse-square-local-gaussian-one-draw-growth-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A centered product Gaussian over individual matching terms, bridge terms, and every Pauli word of weight at most two has an explicit positive-probability event on which one sampled static Hamiltonian obeys linear complexity growth throughout the full laboratory interval.

## Result

Independent standard Gaussian coordinates are drawn once and held fixed. The reference coefficient vector uses inverse-square matching weights, the common inverse-cube bridge weight, and zero Pauli perturbations; its sup norm is at most one and its Hamiltonian is exactly the inverse-square chain. A radius-`ρ` coefficient cap has mass at least

`ofReal((2 gaussianFloorTwo ρ)^m)`

and lies inside the uniform growth event whenever
`T ρ M ≤ ε`, where `M` is the total operator norm of the finite generator dictionary. For `ρ>0`, the growth event therefore has strictly positive probability.

## Gates

- [x] 0 → 1  explicit termwise dictionary, cap, norm transfer, Gaussian bound
- [x] 1 → 2  dependency-closed proof
- [x] 2 → 3  Lean source check, targeted build, axiom audit
- [ ] 3 → 4  blocked on typical-draw growth and first-return laws

## Conjecture loop record

1. Initial version put the entire inverse-square Hamiltonian in one Gaussian coordinate.
2. Hostile review: that creates a correlated global coupling and does not earn “ordinary termwise local ensemble.”
3. Pivot: enumerate each matching projector and bridge projector separately, then add every weight-at-most-two Pauli word as an independent coordinate.
4. The pivot passed Lean and retains the explicit positive small-ball probability.

## Lean certificate

- Intermediate module: `GaloisForLFunctions.HTGeometry.InverseSquareLocalGaussianOneDrawGrowthLaw`
- Termwise module: `GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianOneDrawGrowthLaw`
- Capstones: `measure_ordinaryTwoLocalGaussianUniformGrowthEvent_lower`, `measure_ordinaryTwoLocalGaussianUniformGrowthEvent_pos`
- Exact centre: `ordinaryTwoLocalGaussianHamiltonian_center`
- Verification: source `lake env lean` checks; targeted `lake build GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianOneDrawGrowthLaw`
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`

## Honest boundary

This closes a positive-probability one-draw laboratory-time theorem. It does not prove high-probability/typical growth, an exponential plateau, or first return to the full polynomial-circuit set. Those remain the live Brown–Susskind core.

## Novelty label

Internal bridge theorem, not the Brown–Susskind capstone. Positive probability must not be described as typicality.

## Log

- 2026-08-21 — conjecture opened after robust tube theorem.
- 2026-08-21 — correlated-coordinate version proved, rejected as insufficiently ordinary, replaced by termwise centered Gaussian law, formalized and audited.
