# Finite cyclic constraint group average

- **ID:** finite-cyclic-constraint-group-average
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN
- **Source:** physics-first bridge from finite group averaging / refined algebraic quantization
- **Statement:** If a bounded gauge step `U` satisfies `U^N = 1`, then its finite orbit average `P_N = N⁻¹ ∑_{k<N} U^k` maps every vector into `ker (U - 1)`, fixes exactly that kernel for `N ≠ 0`, and is idempotent.  The corresponding observable twirl `Φ_N` is a bimodule projection onto the clock commutant and obeys the exact conditional-variance identity `Φ_N(X²)-Φ_N(X)² = Φ_N((X-Φ_N(X))²)`.

## Goal

Discharge the assumed `PhysicalState (U - 1)` hypotheses in the existing static constraint and Ward-value corpus, and expose what an arbitrary finite clock can observe.  The average has direct theorem consumers: Ward values for averaged arbitrary vectors, constraint-ideal representative independence, conditional values, and a positive-variance precursor for the sharper involutive-clock energy law.  This is a finite gauge-orbit construction, not a time flow.

## Gates

- [x] 0 → 1 in-progress: exact finite identity, corpus gap located, direct consumers named
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem surface, direct module check, axiom audit
- [ ] 3 → 4 publication-ready: standalone note with Lean certificate and physics interpretation

## Physics source

- D. Giulini, “Group Averaging and Refined Algebraic Quantization,” arXiv:gr-qc/0003040.  Group averaging is presented as a method for quantizing systems with first-class constraints.
- A. Held and H. Maxfield, “The Hilbert space of de Sitter JT: a case study for canonical quantum gravity,” arXiv:2410.14824.  Group averaging is used in an explicit canonical-gravity setting.
- C.-Y. Lin, “Quantum Cauchy Surfaces in Canonical Quantum Gravity,” arXiv:1508.02537.  Refined algebraic quantization and group averaging are applied to Hamiltonian constraints.
- P.-O. Löwdin, “Group Algebra, Convolution Algebra, and Applications to Quantum Mechanics,” Rev. Mod. Phys. 39 (1967), 259.  Finite-group convolution constructs projection operators resolving the Hilbert space into symmetry sectors.
- J. Helsen et al., *Real Randomized Benchmarking*, arXiv:1801.06121.  A finite-group observable twirl is the Hilbert--Schmidt orthogonal projection onto the group commutant.
- P. A. Höhn, A. R. H. Smith, and M. P. E. Lock, *The Trinity of Relational Quantum Dynamics*, arXiv:1912.00033.  Group-averaged relational observables have the same physical conditional values as their gauge-fixed representatives.

## Exact relation

For `S_N = ∑_{k=0}^{N-1} U^k`, the geometric-sum telescope gives

`(U - 1) S_N = U^N - 1`.

Hence `U^N = 1` implies `(U - 1) S_N ψ = 0` for every kinematic vector `ψ`.  When `N ≠ 0`, the normalized average `P_N = N⁻¹ S_N` fixes every vector already satisfying `(U - 1) ψ = 0`; consequently

`PhysicalState (U - 1) ψ ↔ P_N ψ = ψ`

and `P_N² = P_N`.

For the observable twirl `Φ_N`, additivity, idempotence, and the left/right module laws over
the commutant give, with `M=Φ_N(X)`,

`Φ_N((X-M)²)
  = Φ_N(X²) - Φ_N(X)M - MΦ_N(X) + Φ_N(M²)
  = Φ_N(X²) - M²`.

Hence

`Φ_N(X²)-Φ_N(X)² = Φ_N((X-Φ_N(X))²)`.

Between invariant left/right states, twirling preserves matrix elements, so the defect value is
exactly the matrix element of `(X-Φ_N(X))²`.  This is the arbitrary-period static variance law.
For `N=2`, involutive unitarity and self-adjointness sharpen it to a master constraint and the
quarter-commutator norm law recorded in `involutive-clock-observability-energy`.

## Corpus applications required for promotion

1. Instantiate `constraintWardValue_eq_zero` on `P_N ψ`, eliminating its physical-state premise for an arbitrary input `ψ`.
2. Instantiate `physicalMatrixElement_congr_mod_constraintTwoSidedIdeal` between `P_N φ` and `P_N ψ`, eliminating both physical-state premises.
3. Keep the theorem generic over real or complex Hilbert spaces and bounded linear gauge steps; do not specialize it to zeta.
4. Compose the average with the master constraint `(U - 1)†(U - 1)` so the Ward consumers require neither assumed physicality nor assumed self-adjointness.
5. Make observable twirling additive and a bimodule map over its commutant, then identify its full multiplicativity defect with the twirled square of the erased observable component.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/FiniteConstraintGroupAverage.lean` proves the telescope,
physicality, fixed-space equivalence, and idempotence of the normalized average.  Its terminal
theorems instantiate the existing Ward and two-sided-ideal consumers on averaged arbitrary
vectors and then compose the average with the master constraint, removing both assumed
physicality and assumed self-adjointness.  It also proves:

- `finiteCyclicObservableTwirl_add` and `finiteCyclicObservableTwirl_sub`;
- `finiteCyclicObservableTwirl_mul_right_of_commutes` and
  `finiteCyclicObservableTwirl_mul_left_of_commutes`;
- `finiteCyclicObservableTwirlKadisonDefect`;
- `finiteCyclicObservableTwirlKadisonDefect_eq_twirl_disturbance_sq`;
- `inner_finiteCyclicObservableTwirlKadisonDefect_of_fixed`.

## Status

[PROVED IN LEAN] `lake build +GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage` and the
single-file direct Lean check pass.  The exported theorem audit reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.  No full project build, numerical experiment,
or concurrent Lean process was run.
