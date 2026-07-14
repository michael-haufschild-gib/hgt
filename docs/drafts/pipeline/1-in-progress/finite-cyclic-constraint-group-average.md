# Finite cyclic constraint group average

- **ID:** finite-cyclic-constraint-group-average
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** physics-first bridge from finite group averaging / refined algebraic quantization
- **Statement:** If a bounded gauge step `U` satisfies `U^N = 1`, then its finite orbit average `P_N = N⁻¹ ∑_{k<N} U^k` maps every vector into `ker (U - 1)`, fixes exactly that kernel for `N ≠ 0`, and is idempotent.

## Goal

Discharge the assumed `PhysicalState (U - 1)` hypotheses in the existing static constraint and Ward-value corpus.  The average must have direct theorem consumers: a Ward value for averaged arbitrary vectors and constraint-ideal representative independence between averaged arbitrary vectors.  This is a finite gauge-orbit construction, not a time flow.

## Gates

- [x] 0 → 1 in-progress: exact finite identity, corpus gap located, direct consumers named
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem surface, direct module check, axiom audit
- [ ] 3 → 4 publication-ready: standalone note with Lean certificate and physics interpretation

## Physics source

- D. Giulini, “Group Averaging and Refined Algebraic Quantization,” arXiv:gr-qc/0003040.  Group averaging is presented as a method for quantizing systems with first-class constraints.
- A. Held and H. Maxfield, “The Hilbert space of de Sitter JT: a case study for canonical quantum gravity,” arXiv:2410.14824.  Group averaging is used in an explicit canonical-gravity setting.
- C.-Y. Lin, “Quantum Cauchy Surfaces in Canonical Quantum Gravity,” arXiv:1508.02537.  Refined algebraic quantization and group averaging are applied to Hamiltonian constraints.
- P.-O. Löwdin, “Group Algebra, Convolution Algebra, and Applications to Quantum Mechanics,” Rev. Mod. Phys. 39 (1967), 259.  Finite-group convolution constructs projection operators resolving the Hilbert space into symmetry sectors.

## Exact relation

For `S_N = ∑_{k=0}^{N-1} U^k`, the geometric-sum telescope gives

`(U - 1) S_N = U^N - 1`.

Hence `U^N = 1` implies `(U - 1) S_N ψ = 0` for every kinematic vector `ψ`.  When `N ≠ 0`, the normalized average `P_N = N⁻¹ S_N` fixes every vector already satisfying `(U - 1) ψ = 0`; consequently

`PhysicalState (U - 1) ψ ↔ P_N ψ = ψ`

and `P_N² = P_N`.

## Corpus applications required for promotion

1. Instantiate `constraintWardValue_eq_zero` on `P_N ψ`, eliminating its physical-state premise for an arbitrary input `ψ`.
2. Instantiate `physicalMatrixElement_congr_mod_constraintTwoSidedIdeal` between `P_N φ` and `P_N ψ`, eliminating both physical-state premises.
3. Keep the theorem generic over real or complex Hilbert spaces and bounded linear gauge steps; do not specialize it to zeta.
4. Compose the average with the master constraint `(U - 1)†(U - 1)` so the Ward consumers require neither assumed physicality nor assumed self-adjointness.

## Status

[CONJECTURE] The Lean statements above should follow from the noncommutative geometric-sum identity already present in mathlib.  No claim is promoted until the direct consumers compile and the axiom audit is clean.
