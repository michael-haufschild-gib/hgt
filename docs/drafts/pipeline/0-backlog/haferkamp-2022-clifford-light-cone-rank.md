# Haferkamp et al. 2022: Clifford light-cone high-rank point

- **ID:** haferkamp-2022-clifford-light-cone-rank
- **Stage:** 0-backlog
- **Type:** THEOREM (paper)
- **Source:** Attached supplement, Appendix B, Lemma 4
- **Statement:** For an architecture of `T < 4^n - 1` backwards-light-cone blocks, its contraction map attains differential rank at least `T`.

## Goal

Formalize the exact Pauli/Clifford induction which transports an arbitrary nontrivial Pauli string to a selected output qubit along each block's backwards light cone.

## Gates

- [ ] 0 -> 1 in-progress: exact source and primary proof route audited.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency.
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, targeted audit green.
- [ ] 3 -> 4 publication-ready: standalone proof and certificate.

## Approach

First prove the graph-path/Clifford transport statement exactly; then connect its independent Pauli directions to the contraction-map derivative.

## Paper-proof audit

For each block independently, choose a merging family of backward paths from all qubits to its designated output qubit.  A nonidentity Pauli string is reduced along these paths: a two-qubit Clifford first maps every nontrivial adjacent pair to an identity tensored with `Z`, then further two-qubit Cliffords move that `Z` one edge toward the output.  Merging paths are processed once after their merge.  This yields a block Clifford mapping the chosen nonidentity string to a single-site `Z`.

Inductively select the next Pauli string outside the span of the already obtained conjugated strings.  At step `j`, that span has dimension at most `j - 1`, while the nonidentity Pauli-string basis has cardinality `4^n - 1`; hence a choice exists for every `j ≤ T` when `T < 4^n - 1`.  The derivative-insertion formula then places the resulting `T` independent Pauli directions in the contraction differential, proving rank at least `T`.

Two source repairs are required in the formal statement: the transport claim requires a *nonidentity* Pauli string (the supplement says this later, although an earlier sentence says “every Pauli string”), and its “without loss of generality identical blocks” is only notational—each block may have its own transport construction.  Also formalize phase normalization: a Clifford representative may have determinant different from one, but multiplying by a scalar fourth root of the inverse determinant preserves conjugation and places it in `SU(4)`.

`[OPEN CORE]` Define the paper’s time-ordered backwards-light-cone block, prove its merging-path extraction, construct determinant-one two-qubit Clifford transports symbolically, then formalize the Pauli-basis linear-independence induction and derivative-insertion identity.

## Log

- 2026-08-21 -- Extracted from attached supplement; paper range resolved as `T < 4^n - 1`.
- 2026-08-21 -- Full Appendix-B proof audited against source text. Identified nonidentity and per-block corrections required for an exact theorem statement; no formal theorem claimed yet.
- 2026-08-21 -- Closed the finite Pauli-direction selection layer in `formal/GaloisForLFunctions/HTGeometry/HaferkampPauliDirectionSelection.lean`: exact cardinality `4^n - 1`, a fresh nonidentity-label choice below that threshold, and its literal matrix outside the complex span of all predecessors. Target `lake env lean`, target build, and `#print axioms` audits passed; module wired into `HTGeometry` without building the umbrella.
- 2026-08-21 -- Closed the determinant-one phase repair in `formal/GaloisForLFunctions/HTGeometry/HaferkampSpecialUnitaryPhase.lean`: every finite nonempty unitary has a scalar `SU(d)` representative, including `SU(4)`, and the scalar is proved to cancel exactly in conjugation. Target `lake env lean`, target build, and `#print axioms` audits passed; module wired into `HTGeometry` without building the umbrella.
- 2026-08-21 -- Strengthened the phase repair with a canonical chosen `SU(d)` representative and an exact conjugation-equality theorem, so later Clifford constructions can supply literal `SU(4)` gates rather than existential phases. Re-audited target build and axioms.
- 2026-08-21 -- Closed the first literal local transport seed in `formal/GaloisForLFunctions/HTGeometry/HaferkampTwoQubitCliffordSeeds.lean`: Boolean CNOT is unitary, its canonical `SU(4)` phase representative is defined, and target `Z` transports exactly to `Z ⊗ Z`. Target `lake env lean`, target build, and `#print axioms` audits passed; module wired into `HTGeometry` without building its umbrella.
- 2026-08-21 -- Added the Boolean Hadamard seed to the same module: it is unitary and conjugates `X` exactly to `Z`. Re-audited target build and axioms; this supplies the first local axis-normalization step for the Appendix-B transport induction.
- 2026-08-21 -- Added the Boolean phase seed and exact product-conjugation law: `S` sends `Y` to `-X`, and `H*S` sends `Y` to `-Z`. This completes literal one-qubit normalization of every nonidentity Pauli axis to a nonzero multiple of `Z`; target `lake env lean`, target build, and `#print axioms` audits passed.
- 2026-08-21 -- Added the second CNOT transport direction: literal CNOT and its canonical `SU(4)` representative send `Z ⊗ Z` exactly to `I ⊗ Z`. Together with the existing reverse equality and one-qubit normalizers, this closes the nontrivial two-site support-merging seed. Target `lake env lean`, target build, and axiom audit passed.
- 2026-08-21 -- Added literal Boolean SWAP and its canonical `SU(4)` representative, both moving source `Z` to target `Z`. This closes the remaining singleton-on-source branch of the local support-merging construction; target checks and axiom audit passed.
- 2026-08-21 -- Closed the full local transport classification in `formal/GaloisForLFunctions/HTGeometry/HaferkampTwoQubitPauliTransport.lean`: every nonidentity Boolean two-qubit Pauli label has an explicit determinant-one `SU(4)` transport to a nonzero multiple of target `Z`. Tensorized axis normalization, SWAP, CNOT, and scalar phase normalization are all exact. Target `lake env lean`, target build, and `#print axioms` audits passed; module wired into `HTGeometry` without building its umbrella.
- 2026-08-21 -- Closed the full-register lifting layer in `formal/GaloisForLFunctions/HTGeometry/HaferkampLiftedPauliTransport.lean`: the two addressed qubits are separated exactly from a finite Pauli matrix, every local `SU(4)` conjugation lifts over that factorization, and any Pauli string nontrivial on the selected pair has an explicit lifted `SU(4)` gate merging that local support to the second selected qubit without changing the rest. Target checks and axiom audit passed; module wired into `HTGeometry` without building its umbrella.
- 2026-08-21 -- Closed certified single-path transport in `formal/GaloisForLFunctions/HTGeometry/HaferkampQubitPathTransport.lean`: a nontrivial inductive path has a product of lifted local gates transporting source nonidentity support to its endpoint, and the endpoint label is exactly `Z`. Target `lake env lean`, target build, and axiom audit passed; module wired into `HTGeometry` without building its umbrella.
