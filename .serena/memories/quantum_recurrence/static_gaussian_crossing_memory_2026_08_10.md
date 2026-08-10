# Static Gaussian crossing-memory law (2026-08-10)

## Why this was needed
A concurrent corpus branch proved atomlessness and Fourier/operator-norm decay for a free-Fock matrix-semicircle surrogate of the one-replica local-Pauli pencil. Hostile audit: ordinary time-independent local Hamiltonians have classical static random coefficients, not freely independent semicircular coefficients. Free-Fock decay therefore needs a transfer theorem.

## Conjecture loop
1. Conjecture: Hall fullness + free-Fock atomlessness transfers directly to the static Gaussian pencil.
2. Failure: classical Gaussian Wick calculus has all three fourth pairings; the free/Fock moment has only two noncrossing pairings.
3. Surviving invariant: the omitted crossing contraction.
4. Exact proof: for Hermitian coefficient matrices A_i,
   crossing memory
   = sum_ij tr(A_i A_j A_i A_j)
   = square fourth energy - (1/2) total Hilbert--Schmidt commutator energy.
5. Exact transfer criterion at fourth order:
   classical fourth Wick = noncrossing fourth Wick iff
   commutator energy = 2 * square fourth energy.
6. For any commuting family, commutator energy is zero and the crossing defect is the full square energy; when nonzero, classical and free fourth moments differ.

This shows direct free-Fock-to-quenched-static transfer is invalid already at order four and names the first correct transfer invariant. It does not prove Brown growth.

## Lean
Module:
`formal/GaloisForLFunctions/HTGeometry/StaticGaussianCrossingMemoryLaw.lean`
Umbrella import added.

Key theorems:
- `trace_crossing_eq_square_sub_half_commutatorEnergy`
- `matrixFamilyCrossingMemory_eq_square_sub_half_commutatorEnergy`
- `matrixFamilyClassicalWickFourth_eq_three_square_sub_half_commutatorEnergy`
- `matrixFamilyClassicalWickFourth_eq_noncrossing_iff_energy_balance`
- `matrixFamilyClassicalWickFourth_ne_noncrossing_of_commute`

Verification:
- `lake env lean .../StaticGaussianCrossingMemoryLaw.lean` green.
- final targeted `lake build GaloisForLFunctions.HTGeometry.StaticGaussianCrossingMemoryLaw` green.
- audited capstones use only `propext`, `Classical.choice`, `Quot.sound`.
- no forbidden declarations in module.
- generated indexes refreshed.
- global lint reached only two unrelated concurrently added modules unreachable from the umbrella: `ConstitutiveComposedFailureGenesis`, `ConstitutiveVisibleKernelPurificationGauge`.

## Correct next frontier
Do not pursue free-Fock decay as if it were physical quenched decay. Need an all-orders static crossing/traffic hierarchy or a direct nonlinear estimate controlling the killed gate-walk/complete-incidence observable. First concrete next test: calculate/bound normalized crossing memory for the actual connected local-Pauli adjoint family. Disjoint commuting local terms suggest the fourth crossing survives at leading order, so a semicircular approximation is likely the wrong physical limit; any useful resummation must retain extensive commuting memory.