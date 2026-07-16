# Relational clock observable values

- **ID:** relational-clock-observable-values
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [BRIDGE] stationary relational clocks, periodic-clock group averaging, and observer-algebra zero modes
- **Statement:** A finite cyclic observable twirl is an idempotent projection onto the constraint commutant, preserves every physical matrix element and conditional value, and forces a uniform raw clock marginal whenever one clock effect resolves the identity over its orbit.

## Goal

Give the general HTGeometry corpus an exact clock-observability theorem which uses a static
constraint rather than a time flow. The theorem applies to arbitrary Hilbert spaces, constraints,
observables, and hypertranscendental sources; RHTower is only a downstream consumer.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, exact finite identity, general and RHTower consumers identified
- [x] 1 → 2 fully-proven: complete recursive proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: theorem names and targeted Lean checks are green; targeted axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics relation

Page--Wootters stationary clocks encode time in conditional correlations, not in evolution of the
global constrained state. The Dirac/Page--Wootters/relational-Heisenberg trinity identifies the
physical matrix elements of group-averaged observables with the corresponding conditional values.
For periodic clocks, the relational observable is obtained by partial group averaging over one
clock cycle. Finite clock POVMs additionally give a uniform raw time marginal on a stationary
constraint state. Holographic modular zero modes use the same projection onto a commutant.

Primary sources:

- D. N. Page and W. K. Wootters, *Evolution without evolution: Dynamics described by stationary observables*, Phys. Rev. D 27 (1983), 2885, DOI 10.1103/PhysRevD.27.2885.
- P. A. Höhn, A. R. H. Smith, and M. P. E. Lock, *The Trinity of Relational Quantum Dynamics*, arXiv:1912.00033.
- L. Chataignier, P. A. Höhn, M. P. E. Lock, and F. M. Mele, *Relational Dynamics with Periodic Clocks*, arXiv:2409.06479, New J. Phys. 28 (2026) 034504.
- D. Cafasso et al., *Quantum Time and the Time-Dilation induced Interaction Transfer mechanism*, arXiv:2407.00161, Phys. Rev. D 110 (2024) 106014.
- T. Faulkner and A. Lewkowycz, *Bulk locality from modular flow*, arXiv:1704.05464, JHEP 07 (2017) 151.

## Exact theorem family

For a bounded gauge step `U`, seed observable `A`, nonzero orbit length `N`, left stationary state
`U† φ = φ`, and right stationary state `U ψ = ψ`, the recursive twirl numerator obeys

`<φ, T_N(A) ψ> = N <φ, A ψ>`.

After normalization,

`<φ, Twirl_N(A) ψ> = <φ, A ψ>`.

Applying this to two observables preserves their conditional ratio. If a clock effect `e`
satisfies `Twirl_N(e) = N⁻¹ 1`, then

`<φ, e ψ> = N⁻¹ <φ, ψ>`.

Hence the raw clock marginal is uniform while its nontrivial information remains in conditional
correlations. Independently, finite periodicity makes the twirl idempotent on observables, so it
is a genuine commutant-valued conditional expectation.

## Corpus application

General HTGeometry declarations in
`formal/GaloisForLFunctions/HTGeometry/FiniteConstraintGroupAverage.lean`:

- `finiteCyclicObservableTwirl_eq_self_of_commutes`
- `finiteCyclicObservableTwirl_idempotent`
- `inner_finiteCyclicObservableTwirlNumerator_of_fixed`
- `inner_finiteCyclicObservableTwirl_of_fixed`
- `physicalMatrixElement_finiteCyclicObservableTwirl_eq`
- `physicalConditionalValue_finiteCyclicObservableTwirl_eq`
- `stationaryClockEffect_matrixElement_eq_uniform`

These results require no zeta specialization, Gamma specialization, Hamiltonian, or temporal flow.
They apply to the free-jet, quantum-Fisher, projection-survival, pinching/Kadison, KMS, and
master-constraint surfaces whenever an observable is passed through a finite clock constraint.

The direct RHTower instance in
`formal/GaloisForLFunctions/RHTower/SoninLogCoordinateScattering.lean` proves that logarithmic
Fourier scattering gives a `Z₂` observer-algebra projection, preserves arbitrary Sonin conditional
values on the invariant sector, and assigns half the raw weight to a complementary two-reading
clock effect.

## Verification boundary

- `lake build +GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage` passed with only the exact touched module rebuilt.
- `lake env lean GaloisForLFunctions/HTGeometry/FiniteConstraintGroupAverage.lean` passed.
- `lake env lean GaloisForLFunctions/RHTower/SoninLogCoordinateScattering.lean` passed.
- No full build, concurrent Lean process, numerical experiment, or broad lint was run.
