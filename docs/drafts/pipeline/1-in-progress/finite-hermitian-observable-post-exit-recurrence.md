# Finite Hermitian observable post-exit recurrence

- **ID:** `finite-hermitian-observable-post-exit-recurrence`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Frontier comparison: Kotowski--Oszmaniec, *Tight bounds on recurrence time in closed quantum systems*, arXiv:2601.10409v3, Proposition 1 and open problems; Gimeno--Sotoca, *Upper Bounds for the Poincare Recurrence Time in Quantum Mixed States*, J. Phys. A 50 (2017), arXiv:1607.00881.
- **Statement:** For every finite Hermitian Hamiltonian, finite family of density-matrix/effect pairs, nonnegative observation weights, positive tolerance, and positive guard time, the weighted Born histories either never exit the tolerance or return strictly after an exit. The certified deadline is the least graph--resolution clock determined by the visible energy-sector coefficients.

## Goal

Turn the abstract observable coefficient law into an unconditional physical quantum theorem: derive the energy sectors from the Hamiltonian, prove exact unitary evolution, identify the coefficient histories with Born expectation histories, and eliminate user-chosen graph and resolution by finite optimization.

## Literature frontier audit

- Kotowski--Oszmaniec prove deterministic post-exit recurrence for pure states by metric packing and explicitly leave expectation-value dynamics as an open direction.
- Gimeno--Sotoca treat mixed-state recurrence in state-space norms, including infinite discrete spectra through finite relevant-state truncation. They do not give observer-specific post-exit deadlines or graph rate--distortion capacity.
- The candidate must therefore contain all three strict additions simultaneously: actual observable histories, post-exit semantics, and an observer-dependent optimal capacity. Countable spectrum alone is not novel.

## Gates

- [x] 0 -> 1: current primary literature checked; exact published metric frontier formalized in `PublishedRecurrencePackingFrontier.lean`; physical statement and proof route fixed
- [ ] 1 -> 2: complete paper proof closed, including spectral and Born-history identities
- [ ] 2 -> 3: Lean theorem, targeted build, lint, and axiom audit pass
- [ ] 3 -> 4: external novelty audit and standalone paper integration

## Paper proof

Let `H` be Hermitian. Its finite-dimensional spectral theorem supplies a unitary `V` and real energies `E_i` with `H = V diag(E) V*`. Therefore

`exp(-itH) = V diag(exp(-it E_i)) V*`.

For each density matrix `rho_a` and effect `A_a`, move both into the energy basis. The Born history is then

`tr(diag(exp(-itE)) rho_a diag(exp(itE)) A_a)`.

Its displacement from time zero is the finite sum over ordered energy pairs

`sum_{i,j} (rho_a)_{ij} (A_a)_{ji} (exp(-it(E_i-E_j)) - 1)`.

Thus the physical weighted Born deviation is exactly the previously proved sector-history deviation with energy list `-E` and coefficients `(rho_a)_{ij}(A_a)_{ji}`. For any synchronization graph, simultaneous Dirichlet approximation on one vertex per connected component gives a positive sampled return by `(Q+1)^(|V|-components)`. Omitted coefficients pay the exact `l1` distortion remainder; retained coefficients pay the phase-resolution term. Finite minimization over graphs and resolutions attains the least certified deadline. Resampling at `exitTime + guardTime` makes every positive sampled return strictly later than the witnessed exit. If no exit exists, the complementary never-exits branch holds.

No simple spectrum, distinct-gap, noncancellation, randomness, chaos, or genericity premise is used.

## Lean attack

1. Prove diagonal unitary conjugation equals the entrywise phase evolution used by the coefficient law.
2. Prove exact equality between physical trace-expectation deviation and sector total deviation.
3. Instantiate `finiteQuantumExpectationSector_positiveTarget_optimal_neverExits_or_postExit`.
4. Lift from diagonal energy coordinates to arbitrary Hermitian `H` using `unitaryEvolution_spectral` and trace cyclicity.

## Log

- 2026-08-17 -- literature-first conjecture opened after formalizing the 2026 metric-packing frontier.
