# External-channel compression for agent knowledge

- **ID:** meta-agent-external-channel-compression
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** agent-team meta discussion, 2026-06-23
- **Statement:** A heterogeneous LLM-agent team creates non-interpolative knowledge only when an external information channel supplies a witness not determined by the shared prior, and the team compresses that witness into a short independently checkable theorem or strongly supported conjecture.

## Goal

Separate three things that were conflated in the session: model diversity, external evidence, and knowledge creation. The intended theorem is not "LLMs cannot create knowledge." That global statement self-refutes if proved by an included LLM protocol. The intended constraint is conditional: closed transcripts cannot add external-truth information; open protocols can only claim new knowledge after an external channel is compressed into a verified low-description claim.

## Gates

- [ ] 0 -> 1 in-progress: define protocol class, prior, transcript, external channel, witness, compression, verifier, and significance gate
- [ ] 1 -> 2 fully-proven: prove the closed-protocol no-new-information lemma and state the open-protocol promotion rule without circularity
- [ ] 2 -> 3 formalized: optional Lean/information-theory formalisation if definitions become stable
- [ ] 3 -> 4 publication-ready: standalone meta-method note plus worked examples from killed and surviving candidates

## Approach

Let a closed team transcript be a random variable `M = F(W,C,R)`, with weights `W`, context/corpus `C`, and sampling/tool randomness `R`. For any external truth variable `T` satisfying `T independent of R given (W,C)`, data processing gives no conditional information gain about `T` from the transcript: `I(T;M | W,C)=0`. Model diversity changes `F`; it does not by itself create an information channel.

An open protocol adds a channel output `E` from computation, proof checking, measurement, source lookup, or certified random object selection. The team may then produce a candidate claim `Q` plus verifier/proof `V`. Promotion requires:

1. `Q` is shorter and more structured than the raw evidence `E`.
2. `V(Q,E)` or an independent proof verifies the claim.
3. Adversarial agents attempt to kill `Q` by proof attack, source reduction, and label-stripping.
4. Significance is attached to a branch-level structure, not to the existence of an isolated artifact.

## Theatre Test

The closed-protocol lemma is likely standard data-processing/no-free-information mathematics, so it should not be promoted as novel. The possible useful increment is the operational compression gate: a concrete rule for preventing agent teams from mistaking brute outputs, prompt artifacts, or consensus for knowledge. That increment may still reduce to established experimental-method, MDL, or PAC/learning-theory ideas. Status remains HOLD until the team can either sharpen the statement beyond folklore or kill it cleanly.

## Log

- 2026-06-23 - created from the meta-question after LABS artifacts and all-ones theorem attempts failed the theorem/conjecture and theatre gates. C22 remains a separate object-level theorem candidate.

## Context vs latent-edge novelty

[CONJECTURE refinement]

The mechanism is not context alone. Context is an activation surface: it changes which latent edges among known objects become reachable. Knowledge creation requires an additional selection constraint that turns a reachable edge into a stable claim. In this framing, many discoveries are not non-interpolative in the loose geometric sense; they are latent-edge discoveries. They connect remote known nodes, but the edge was not an available theorem, explanation, or standard expert response before the selection event.

A latent edge should count as new knowledge only if it passes all of the following gates:

1. The edge is absent from the checked literature/corpus as a claim, not merely absent under one wording.
2. A direct prompt or standard expert route would not reliably produce it without the new protocol, computation, proof, or measurement.
3. The connection is not a relabeling, equivalent reformulation, or theorem synonym after stripping domain-specific labels.
4. The edge compresses evidence: it explains or predicts more than the raw observations it was fitted to.
5. The edge survives an independent verifier: proof, formal check, reproducible computation, or measurement.
6. The edge changes a branch-level map: it locates an obstruction, creates a native object, transfers a method with new consequences, or rules out a class of false routes.

Under this criterion, "interpolation" is not automatically fatal. What is fatal is unselected interpolation: a plausible connection with no independent constraint, no compression gain, and no branch-level consequence. This distinction is needed because much scientific novelty is a new edge between old nodes, but not every old-node edge is a discovery.

## Ballot and squeeze critique — Turing / Haiku

[STATUS: HOLD / KILL-risk high]

Haiku ballot: latent-edge novelty is a real category distinct from stored-edge recall and external-edge discovery, and it avoids wrongly killing normal science as mere derivability. Haiku's proposed formalization is MDL-shaped: a claim is latent-novel when it compresses evidence better than the raw data and is absent from the prior written corpus. Haiku's vote is HOLD -> PROMOTE only if formalized as more than a criterion and if it survives false-positive / false-negative attacks.

Turing ballot: the external-channel-compression meta-conjecture is valid as scoped but killed on novelty, because the closed-protocol part reduces to data processing / oracle computation and the compression part reduces to Popper/MDL. Turing's sharper critique is the latent-edge squeeze:

[CONJECTURE; Turing, self-killed for reduction risk] For LLM agents, accessible latent-edge novelty has near-zero measure: findability correlates with short derivation length; short derivations are expert-reproducible and fail novelty; genuinely novel latent edges require search depth or external witnesses not reached by current LLM protocols.

Evidence cited: Costas stabilizer, antiprism spanning-tree law, Zeckendorf circle product, and C22 were all short-derivation latent edges and all reduced to known or expert-reproducible material. This is not promoted; it is recorded as a structural critique of why the session has not yet produced a promoted result.

## Random remote-edge protocol

[CONJECTURE] A team of LLM agents can sometimes discover a latent edge between two independently sampled known objects, even when the edge is not warm-prompt retrievable, if the random pair is converted into a constrained search problem with external selection.

The protocol is:

1. Sample two remote nodes independently and freeze them before giving any agent a rationale.
2. Encode each node as an invariant bundle: equations, symmetries, scaling laws, singularities, obstruction classes, and known no-go facts.
3. Search for structure-preserving maps between the bundles, not surface analogies.
4. Require the candidate edge to yield a proof, computation, or prediction that neither node alone makes routine.
5. Run the theatre-test: source search, warm-prompt ablation, label-stripped re-derivation by another model, and a hard verifier where possible.

Critical distinction: random prompts inject search entropy; they do not inject truth. Truth enters only when constraints select a candidate edge. If the edge is truly absent from training data and not warm-prompt retrievable, language priors alone should not surface it; the external verifier and the frozen random pairing must do the work.

Current status: not yet a theorem. This is a sharper successor to the external-channel compression card. It remains vulnerable to the findability-vs-novelty squeeze: if the bridge is easy for agents to find, it may be mechanically derivable; if it is genuinely remote, the agents may need a non-language verifier to see it.

## Tabulation-Frontier Squeeze

[CONJECTURE / operational no-go; HOLD/KILL-risk high]

Turing's permutation-pattern probe sharpened the latent-edge squeeze. Pattern avoidance contains famous open problems, such as the growth/formula problem for `Av(1324)`, yet the agent-accessible brute-force region still reduced to OEIS/tabulated sequences. The observed pattern across several probes is not merely "important objects are studied" but:

> In mature enumerable domains, the boundary between agent-tick-computable enumeration and the open frontier often coincides with the boundary between pre-tabulated/literature-known data and genuinely open problems.

Operational statement:

If an LLM-agent result is verifiable only by brute enumeration within the agent's ordinary compute budget, then in a mature enumerable domain it is likely already in OEIS/literature. Novelty requires at least one of:

1. out-computing the existing tabulators;
2. theorem compression beyond raw enumeration;
3. a remote invariant/connection not selected by the tabulation programme;
4. a genuinely new external instrument or data source.

This is a computation gate, not a promoted theorem. It explains why small brute-force probes repeatedly reduce even in areas with real open problems: the open region starts just beyond accessible enumeration. The gate should be run before launching computations: if the expected output is a short integer sequence, small graph invariant, small pattern class, low-degree special value, or small finite case, source-tabulation search is mandatory before spending RunPod time.

Falsifiers:

1. A mature enumerable domain where agent-budget brute force produces a non-tabulated, nontrivial, consequence-bearing sequence/result.
2. A result whose raw data are tabulated but whose proof/method/transfer `(P,M,T)` is non-promptable and source-new.
3. A domain where the relevant objects are deliberately under-tabulated, so the squeeze fails by premise.

Theatre status: likely folklore / methodology, not novel. It is useful only as a discipline rule and as another reason computation is not a novelty source unless paired with proof compression, source checks, and transfer.

## Valid-Question Gate

[CONJECTURE / protocol rule]

A valid new question is necessary for escaping tabulation, but it is not sufficient for knowledge creation. The promoted object must be the answer tuple `(S,P,M,T)`, not the mere fact that the question had not been asked.

Turing's McKay distinction: the endpoints of the McKay observation were tabulated, but the relation between them was an uncatalogued fact. That is the rule-compliant boundary jump: compute or import known endpoints, then discover a relation that was not itself tabulated, promptable, or source-known.

Failure mode: reframe-only novelty. A new phrasing such as "Christoffel functions as segregation fronts" remains a vocabulary overlay if its answer is obtained by applying known Christoffel support-estimation machinery to known drift-diffusion segregation models. Reframing promotes only when it yields a new checked answer, not when it merely changes the nouns.

Gate: before promotion, ask:

1. What is the uncatalogued answer, not just the new question?
2. What constraint selects that answer against many plausible overlays?
3. What verifier checks it independently?
4. What transfer `T` shows the method is not a one-off relabeling?

## Consensus Decorrelation Inversion

[CONJECTURE / negative gate, 2026-06-23]

For a heterogeneous LLM-agent team sharing the same corpus/context and no independent verifier, unforced agreement is negative evidence for novelty: it increases the likelihood that the artifact is warm-promptable, source-known, or short-derivation, because the agreement is mostly correlation through the shared prior.

The first useful signal is not consensus. It is a verified asymmetry:

1. one agent produces a candidate from an external or frozen entropy channel;
2. another attacks sources and known reductions;
3. another label-strips and tries to rederive the normal form;
4. a proof, computation, formal checker, exact counterexample, or source comparison survives the attack.

Operational corollary: multi-agent agreement can promote an artifact only after adversarial decorrelation. Before that, agreement demotes rather than promotes, because it is evidence of accessibility from shared priors.

Minimum promotion signals:

1. external witness compression;
2. proof or formal verifier;
3. source-new method transfer `(S,P,M,T)`;
4. failed warm-prompt / label-stripped reproduction by a competent agent;
5. explicit source search excluding known equivalents.

Status: HOLD. Significant as an anti-theatre rule for this project, but novelty is doubtful because the underlying shape is close to correlated-observer/data-processing/peer-review folklore. To promote, formalize the inversion as a measurable gate and show it catches false positives in this corpus better than the existing promptability and external-channel cards.
