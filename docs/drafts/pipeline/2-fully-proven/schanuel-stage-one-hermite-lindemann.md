# Schanuel extraction stage one from Hermite--Lindemann

- **ID:** schanuel-stage-one-hermite-lindemann
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `formal/GaloisForLFunctions/RHTower/SchanuelStageWitnesses.lean`
- **Statement:** `SchanuelExtractionAt 1` holds unconditionally.

## Goal

Correct the project frontier.  Stage zero and stage one are unconditional; the first open finite
stage of the extraction form of Schanuel's conjecture is stage two.  This is a project correction,
not a claim of new external mathematics.

## Gates

- [x] 0 -> 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3  formalized: Lean theorem `schanuelExtractionAt_one` and targeted build green; global
  formal lint is blocked by unrelated pre-existing unreachable modules
- [ ] 3 -> 4  publication-ready: not applicable; classical theorem/project frontier correction

## Approach

Use the already-proved equivalence

\[
  \operatorname{SchanuelExtractionAt}(1)
  \iff
  \forall z\ne 0,\quad z\text{ is transcendental}\ \lor\ e^z\text{ is transcendental}.
\]

Fix nonzero `z`.  If `z` is transcendental, take the left disjunct.  Otherwise `z` is algebraic
over `Q`, equivalently over `Z`; Hermite--Lindemann says that the exponential of every nonzero
algebraic complex number is transcendental.  Hence the right disjunct holds.

**[PROVED HERE]** This proves `SchanuelExtractionAt 1` with no conjectural input.

## Hostile audit

- The proof does not assume the project `SchanuelConjecture` interface.
- `exp_algebraic_transcendental` is an unconditional theorem already proved in
  `RHTower/ExpAlgebraicTranscendental.lean`; its axiom audit is part of the formal gate.
- The zero exponent is excluded exactly by linear independence of a one-element family.
- The result gives no information at stage two.  It relocates, rather than weakens, the genuine
  frontier.

## Novelty audit

Hermite--Lindemann and the fact that Schanuel's conjecture is known for `n = 1` are classical.
Novelty status: **not externally novel**.  The contribution is a verified correction to this
repository's stated/formal frontier and removal of a false open dependency.

## Log

- 2026-08-14 -- paper proof closed; queued exact Lean discharge and stale-frontier corrections.
- 2026-08-14 -- `schanuelExtractionAt_one` added and checked with
  `lake env lean GaloisForLFunctions/RHTower/SchanuelStageWitnesses.lean`; targeted
  `lake build GaloisForLFunctions.RHTower.SchanuelStageWitnesses` passed. Axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`. Global lint reached unrelated unreachable modules
  (`FieldOne*`, `Suzuki*`, and several `HTGeometry` files); this module is already reachable from
  `RHTower.lean` and contains no forbidden declaration.
