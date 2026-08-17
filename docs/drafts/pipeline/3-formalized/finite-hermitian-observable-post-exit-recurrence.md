# Finite Hermitian observable post-exit recurrence

- **ID:** `finite-hermitian-observable-post-exit-recurrence`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Frontier comparison: Kotowski--Oszmaniec, *Tight bounds on recurrence time in closed quantum systems*, arXiv:2601.10409v3, Proposition 1 and open problems; Gimeno--Sotoca, *Upper Bounds for the Poincare Recurrence Time in Quantum Mixed States*, J. Phys. A 50 (2017), arXiv:1607.00881.
- **Statement:** For every finite Hermitian Hamiltonian, finite family of density-matrix/effect pairs, nonnegative observation weights, positive tolerance, and positive guard time, the weighted Born histories either never exit the tolerance or return strictly after an exit. The certified deadline is the least graph--resolution clock determined by the visible energy-sector coefficients.

## Goal

Turn the abstract observable coefficient law into an unconditional physical quantum theorem: derive the energy sectors from the Hamiltonian, prove exact unitary evolution, identify the coefficient histories with Born expectation histories, and eliminate user-chosen graph and resolution by finite optimization.

## Literature frontier audit

- Kotowski--Oszmaniec prove deterministic post-exit recurrence for pure states by metric packing and explicitly leave expectation-value dynamics as an open direction.
- Gimeno--Sotoca treat mixed-state recurrence in state-space norms, including infinite discrete spectra through finite relevant-state truncation. They do not give observer-specific post-exit deadlines or graph rate--distortion capacity.
- Gupta--Short prove uniform finite-system recurrence for all states, with a deadline controlled by the number of distinct energies. Their theorem implies coarse observable return through trace-distance duality, but its nontrivial-exit witness may be a different state and need not be visible to a supplied observable family.
- Freedman studies algorithms detecting low-volume recurrent unitary dynamics; the recurrent object remains the state orbit rather than a deterministic post-exit theorem for a prescribed Born record.
- The surviving frontier claim therefore contains all three additions simultaneously: actual finite families of Born histories, nontrivial exit witnessed by that same observed deviation, and a least deadline inside the proved graph--resolution certificate family. Countable spectrum or generic orbit-hull packing alone is not novel.
- **Novelty status:** strong candidate, not a priority claim. The theorem directly answers the expectation-value direction named open by Kotowski--Oszmaniec, but literature search cannot prove absence. The defensible advance is the conjunction above, not existence of expectation recurrence by itself.

## Gates

- [x] 0 -> 1: current primary literature checked; exact published metric frontier formalized in `PublishedRecurrencePackingFrontier.lean`; physical statement and proof route fixed
- [x] 1 -> 2: complete paper proof closed, including spectral, density-preservation, and Born-history identities
- [x] 2 -> 3: Lean theorems, targeted builds, lint ownership check, and axiom audits pass
- [ ] 3 -> 4: external novelty audit and standalone paper integration

## Paper proof

Let `H` be Hermitian. Its finite-dimensional spectral theorem supplies a unitary `V` and real energies `E_i` with `H = V diag(E) V*`. Therefore

`exp(-itH) = V diag(exp(-it E_i)) V*`.

Unitary conjugation preserves positivity and trace one, so the evolved `rho_a(t)` is again a density matrix. For positive semidefinite `rho` and `A`, trace conjugation and cyclicity show `tr(rho A)` is real and equals the Born probability `tr(A rho).re`.

For each density matrix `rho_a` and effect `A_a`, move both into the energy basis. The Born history is then

`tr(diag(exp(-itE)) rho_a diag(exp(itE)) A_a)`.

Its displacement from time zero is the finite sum over ordered energy pairs

`sum_{i,j} (rho_a)_{ij} (A_a)_{ji} (exp(-it(E_i-E_j)) - 1)`.

Thus the physical weighted Born deviation is exactly the previously proved sector-history deviation with energy list `-E` and coefficients `(rho_a)_{ij}(A_a)_{ji}`. For any synchronization graph, simultaneous Dirichlet approximation on one vertex per connected component gives a positive sampled return by `(Q+1)^(|V|-components)`. Omitted coefficients pay the exact `l1` distortion remainder; retained coefficients pay the phase-resolution term. Finite minimization over graphs and resolutions attains the least certified deadline. Resampling at `exitTime + guardTime` makes every positive sampled return strictly later than the witnessed exit. If no exit exists, the complementary never-exits branch holds.

No simple spectrum, distinct-gap, noncancellation, randomness, chaos, or genericity premise is used.

The result is finite-dimensional and closed-system. It does not establish a tight lower bound, an inverse speed limit for observed exit, thermodynamic-limit recurrence, open-system recurrence, or a local noncommuting many-body law. “Least” refers exactly to the proved finite graph--resolution certificate family; it is not a claim that the resulting deadline equals the first physical recurrence time.

## Lean realization

Core physical lift: `formal/GaloisForLFunctions/RHTower/FiniteHermitianExpectationPostExitRecurrenceLaw.lean`.

- Diagonal unitary conjugation equals the entrywise phase evolution.
- Arbitrary Hermitian dynamics is reduced by the finite spectral theorem and trace cyclicity.
- Physical trace-expectation deviation equals sector total deviation.
- `finiteHermitianQuantumExpectation_positiveTarget_optimal_neverExits_or_postExit` supplies the matrix-level capstone.

Born specialization: `formal/GaloisForLFunctions/RHTower/FiniteHermitianBornPostExitRecurrenceLaw.lean`.

- `finiteHermitianEvolvedDensityMatrix` proves positivity and trace-one preservation.
- `finiteHermitian_traceExpectationNorm_eq_bornAbs` proves exact equality of trace norm displacement and absolute Born-probability displacement.
- `finiteHermitianBorn_positiveTarget_optimal_neverExits_or_postExit` is the physical capstone for genuine density matrices and quantum effects.

Verification on 2026-08-17:

- Direct Lean checks passed for both modules without warnings.
- Targeted module builds passed; no umbrella build was run.
- Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint finds neither new module unreachable and reports no forbidden declaration in them. Six unrelated pre-existing HTGeometry reachability failures remain.

## Log

- 2026-08-17 -- literature-first conjecture opened after formalizing the 2026 metric-packing frontier.
- 2026-08-17 -- `[CONJECTURE A]` proved for arbitrary finite Hermitian matrix dynamics and arbitrary finite matrix record families.
- 2026-08-17 -- physical closure proved for density matrices, quantum effects, and exact Born probabilities; targeted build and axiom audit passed.
