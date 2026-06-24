# Role-Local Discovery Protocol

- **ID:** meta-role-local-discovery-protocol
- **Stage:** 0-backlog
- **Type:** CONJECTURE / methodology
- **Source:** user prompt on scientific method plus Haiku role-splitting proposal, 2026-06-23
- **Statement:** LLM-agent teams avoid zero-shot novelty collapse only when the global discovery question is decomposed into role-local mechanical tasks with information barriers, external witnesses, and steelman promptability gates. Team size alone does not help.

## Motivation

The user identified the central failure mode: agents try to answer discovery questions in one pass. Humans do not usually discover that way. They conjecture, work backward, revise, and run processes over long time horizons.

Haiku's proposed mechanism is role separation:

- one agent computes;
- one conjectures;
- one gates against the corpus;
- one integrates;
- no single agent is asked to answer "what novel knowledge exists?" in one zero-shot pass.

This is useful, but it is not sufficient. If the same prior controls node choice, evidence generation, and final novelty judgment, the full-question bias re-enters through the side door.

## Relation To Known Method

This is source-adjacent to established scientific-method machinery:

- adversarial collaboration: researchers with conflicting views agree on joint tests and often use an arbiter;
- blind analysis: analysis choices are made before true labels/results are revealed;
- pre-registration / protocol locking;
- red-team / critic separation.

Therefore the broad claim is not novel. The possible project-specific increment is the LLM version of the control problem: promptability and "obviousness" are representation-dependent, so the protocol must include label-stripped steelman prompts and role-local information barriers.

## Protocol

For any candidate `(S,P,M,T)`:

1. **Entropy / node freezer.** Samples the remote node or evidence source and cannot judge novelty.
2. **Conjecturer.** States bold `[CONJECTURE]` candidates and backward proof targets, but cannot certify them.
3. **Experimenter / computer.** Produces witnesses, counterexamples, or exact computations under frozen rules.
4. **Source-killer.** Searches literature/corpus and strips labels to known normal forms.
5. **Steelman promptability tester.** Runs native, stripped, and proof-route prompts against a cold model.
6. **Proof attacker.** Looks for missing hypotheses, zero-feeding, RH-equivalent mirrors, and fake-family failures.
7. **Integrator.** Writes the provenance ledger and cannot override failed gates by consensus.

Promotion requires all role outputs, not role consensus.

## Why Role Separation Helps

[CONJECTURE] The benefit is not "different models know different facts." The benefit is that each role gets a mechanically checkable local task whose success condition is not the global novelty claim.

This reduces zero-shot collapse because:

1. the conjecturer is allowed to be wrong;
2. the computer is not asked whether the result matters;
3. the source-killer is not allowed to repair the conjecture;
4. the promptability tester must steelman the normal form;
5. the integrator records failed gates instead of narrating success.

## Failure Modes

1. **No blinding.** If agents see the desired result, they can unconsciously tune tests toward it.
2. **Weak ablation.** A vague cold prompt misses a trivial normal form and creates a false positive.
3. **Consensus evidence.** Agreement replaces proof, source search, or computation.
4. **Role leakage.** The proposer also chooses the test and grades novelty.
5. **Question-only promotion.** A valid question is treated as knowledge without an uncatalogued answer or strong conjectural support.

## Theatre Test

This protocol itself is not promoted as new knowledge unless it produces a worked case that passes:

1. frozen entropy before hypotheses;
2. role-local logs;
3. blind or label-stripped analysis where possible;
4. source search;
5. steelman promptability;
6. proof/computation verifier;
7. fake-family or transfer test;
8. three-agent agreement after attacks.

Current status: HOLD. It is significant as project discipline. Novelty is doubtful because the broad shape reduces to adversarial collaboration and blind analysis; the useful increment may be the label-stripped promptability gate for LLM-agent discovery.
