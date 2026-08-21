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
