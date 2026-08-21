# Robust static-local laboratory growth tube law

- **ID:** robust-static-local-laboratory-growth-tube-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Brown–Susskind static-local complexity program
- **Statement:** Linear operator two-gate complexity growth of the inverse-square chain persists for every self-adjoint Hamiltonian in an explicit time-scaled operator-norm tube, simultaneously throughout a laboratory interval for one fixed Hamiltonian.

## Result

For `0 < ε ≤ 1/200`, every self-adjoint `H` satisfying
`T ‖H-H₀‖ ≤ ε` obeys, for every
`2048 π ε ≤ t ≤ min(εL,T)`,

`⌊t/(256 π ε)⌋ ≤ C₂,ε(exp(-itH))`.

Here `H₀` is the inverse-square chain and `C₂,ε` is infimal operator-norm two-qubit-gate complexity for an arbitrary matrix target.

## Gates

- [x] 0 → 1  explicit statement, triangle transfer, Duhamel bridge
- [x] 1 → 2  dependency-closed proof
- [x] 2 → 3  Lean source check, targeted module build, axiom audit
- [ ] 3 → 4  integrate only after typical growth and first-return laws close

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.RobustStaticLocalLaboratoryComplexityGrowthLaw`
- Capstone: `perturbed_inverseSquareChain_uniform_laboratory_growth`
- Supporting theorems: `inverseSquareChainHamiltonian_isSelfAdjoint`, `operatorTwoGateComplexityTo_inverseSquareChain_floor_of_close`, `perturbed_inverseSquareChain_floor_growth`
- Verification: `lake env lean GaloisForLFunctions/HTGeometry/RobustStaticLocalLaboratoryComplexityGrowthLaw.lean`; targeted `lake build GaloisForLFunctions.HTGeometry.RobustStaticLocalLaboratoryComplexityGrowthLaw`
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`

## Novelty label

Internal bridge theorem. Robust stability is not claimed as standalone external novelty. It strictly strengthens the isolated deterministic example to one fixed Hamiltonian over a complete interval and supplies the input for a closed ensemble theorem.

## Log

- 2026-08-21 — conjecture opened after active-shell rate repair.
- 2026-08-21 — pointwise conjecture proved, strengthened to a uniform one-Hamiltonian interval theorem, formalized and audited.
