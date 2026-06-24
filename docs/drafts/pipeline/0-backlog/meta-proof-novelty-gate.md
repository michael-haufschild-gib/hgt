# Proof Novelty Gate

- **ID:** meta-proof-novelty-gate
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** user correction and agent-team meta discussion, 2026-06-23
- **Statement:** A known conclusion can still support novel and significant knowledge when the proof method is new, checkable, and transferable.

## Goal

Prevent the team from falsely killing artifacts whose statement is known but whose proof, method, or transfer mechanism may be new. The motivating example is RH: the conclusion may already have a truth value, but a proof can still be the novel object.

## Gates

- [ ] 0 -> 1 in-progress: define statement-promptability, proof-promptability, method-promptability, transfer-promptability, and proof equivalence
- [ ] 1 -> 2 fully-proven: apply the gate to one known HT/M+ result and either kill or promote the proof method
- [ ] 2 -> 3 formalized: optional formal proof-object comparison only if the definitions become stable
- [ ] 3 -> 4 publication-ready: method note showing why known-conclusion artifacts are not automatically dead

## Approach

The artifact under evaluation is not only a statement `S`. It is a tuple:

`(S, P, M, T)`

where `P` is the proof, `M` is the proof method, and `T` is a transfer of that method to a second nontrivial target.

A promptable or known `S` is not a kill. It becomes a kill only if `P`, `M`, and `T` reduce to standard routes after labels are stripped.

The theatre-test therefore splits:

1. Statement-promptability: can a warm prompt recover `S`?
2. Proof-promptability: can a warm prompt recover essentially `P`?
3. Method-promptability: can a warm prompt recover `M` as a reusable technique?
4. Transfer-promptability: can a model apply `M` to `T` without seeing the transcript?
5. Source reduction: does the literature already contain `P`, `M`, or an equivalent transfer?

## Failure Modes

1. Decorative proof: a standard proof with new vocabulary.
2. Single-use trick: a proof that does not transfer to a second target.
3. Hidden source: the proof is known under another name.
4. Statement-only novelty error: the team promotes a known conclusion without a new method.
5. Statement-only kill error: the team kills a potentially novel proof because its conclusion is known.

## Log

- 2026-06-23 - created after the user corrected the team: "rh is known, the novelty is the proof." This card records the corrected evaluation target without promoting the gate itself as new knowledge.
