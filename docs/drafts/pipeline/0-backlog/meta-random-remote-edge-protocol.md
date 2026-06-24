# Random Remote-Edge Protocol

- **ID:** meta-random-remote-edge-protocol
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** agent-team meta discussion, 2026-06-23
- **Statement:** A heterogeneous LLM-agent team can generate non-interpolative knowledge only when independent entropy is converted into a constrained search problem whose candidate edge is selected by an external verifier.

## Goal

Answer the meta question directly: when can a team of different LLM models produce knowledge that is not mere interpolation of shared training data? The target is not a global claim that LLM teams can or cannot create knowledge. The target is an operational protocol that separates search theatre from actual discovery.

## Gates

- [ ] 0 -> 1 in-progress: define remote node, invariant bundle, candidate edge, consequence-bearing edge, external verifier, warm-prompt ablation, and source gate
- [ ] 1 -> 2 fully-proven: execute at least one worked instance or prove a no-go result for the protocol class
- [ ] 2 -> 3 formalized: optional Lean or information-theory formalisation if definitions stabilize
- [ ] 3 -> 4 publication-ready: standalone method note with killed examples, one surviving example, and a reproducible protocol transcript

## Approach

[CONJECTURE] Random prompts can inject entropy, but they cannot inject truth. Truth enters only when constraints select a candidate edge.

Protocol:

1. Sample two remote nodes independently and freeze them before giving agents a rationale.
2. Encode each node as an invariant bundle: equations, symmetries, scaling laws, singularities, obstruction classes, and known no-go facts.
3. Search for structure-preserving maps between the bundles, not semantic resemblance.
4. Require the proposed edge to be consequence-bearing: theorem, computation, prediction, obstruction, or method transfer with a non-routine output.
5. Run the theatre-test: source search, warm-prompt ablation, label-stripped re-derivation by another model, and a hard verifier where possible.

If the edge is absent from training data and not warm-prompt retrievable, language priors alone should not surface it. The random pair creates a new constrained search problem; an external verifier selects among candidate bridges. The LLM team acts as mapper, critic, compressor, and proof-search coordinator, not as the source of truth.

## Failure Modes

1. Surface analogy: the bridge preserves no invariant.
2. Prompt artifact: a direct warm prompt produces the same edge.
3. Literature reduction: the edge is already known under different terminology.
4. Short-derivation reduction: an expert can reproduce the edge mechanically from the two nodes.
5. No consequence: the bridge is descriptive but proves, predicts, or obstructs nothing.
6. Verifier absence: the team cannot tell whether the bridge is true except by consensus.

## Theatre Test

The protocol succeeds only if a worked instance survives all of the following:

1. The nodes were independently frozen before bridge proposals.
2. The invariant bundles were recorded before bridge proposals.
3. The final edge preserves a named invariant or explains an invariant mismatch.
4. The edge produces a checkable consequence.
5. A direct warm prompt does not recover the same edge reliably.
6. Source search does not find the claim or a trivial equivalent.
7. At least one other model can verify the result after labels are stripped.

## Log

- 2026-06-23 - created after the session killed C22, C24, GAF-HT, H2-bounded, all-ones, constraint-forcing, Markov, and the first external-channel-compression formulation as promoted-result candidates. This card preserves the strongest surviving protocol-level conjecture without counting prior failures as a theorem.

## Theatre-Test Pivot: Mixed-Model Team Knowledge

[CONJECTURE refinement]

The useful meta question is not whether a heterogeneous LLM team can create truth by discussion. In a closed protocol it cannot: model diversity changes the search function, but without an external channel the transcript adds no independent information about an external truth variable beyond weights, context, and sampling randomness. That part is data-processing / oracle-computation folklore and should not be promoted.

The live question is narrower and falsifiable: can a mixed-model team reliably turn independent entropy plus hard verification into a non-promptable, consequence-bearing edge? The team is useful only if it changes the search distribution in ways that survive the theatre-test.

A result from such a team counts only as the tuple `(S, P, M, T)`:

1. `S` - statement or conjecture.
2. `P` - proof, computation, or reproducible witness.
3. `M` - reusable method that found or verified it.
4. `T` - transfer to a second nontrivial target, or a principled reason transfer is impossible.

Mixed models help only through decorrelation of failure modes: one model proposes, one source-kills, one label-strips, one formalizes or computes, and one tries to reproduce from a warm prompt. Consensus is not evidence. Disagreement is useful only when it exposes a missing invariant, hidden source, or verifier gap.

Operational promotion gate:

1. Freeze the entropy source before hypotheses: random remote nodes, source documents, formal goals, or computation targets.
2. Encode invariant bundles before proposing bridges.
3. Produce a candidate edge with a checkable consequence.
4. Run source search and warm-prompt ablation.
5. Strip domain labels and ask another model to rederive the proof or method.
6. Require an independent verifier: proof checker, reproducible computation, exact source comparison, or hand-checkable derivation.
7. Promote only if `(S, P, M, T)` is novel and significant, not merely the wording of `S`.

Failure criterion: if the team can state the expected qualitative answer before the computation or source check, then the computation is theatre unless it can falsify, calibrate, or certify a claim that was genuinely uncertain. This is why many RunPod branches are useful as kill/verification tools but not as the source of novelty.

Current status: HOLD. This is a work protocol, not new knowledge. The open empirical claim is whether the protocol can produce one surviving `(S, P, M, T)` in this programme that Turing, Wheeler, and Professor agree is novel and significant after source-kill, promptability, and verification attacks.

## Frozen Remote-Edge Run R1: Granular Segregation x Christoffel Functions

[RUN STARTED / HOLD, 2026-06-23]

Entropy source: `scripts/rng`.

- seed recorded separately by `scripts/rng seed`: `123726412554433721`
- physical node: `granular segregation`
- mathematical node: `orthogonal polynomial Christoffel functions`

Invariant bundles before bridge:

1. Granular segregation: driven binary mixture; nonlinear segregation flux; diffusion/mixing counterterm; concentration fronts or shocks; boundary accumulation; saturation when local composition is exhausted; Peclet-like ratio between segregation and diffusion.
2. Christoffel functions: `lambda_n(x)=1/K_n(x,x)=min integral |p|^2 dmu` subject to `p(x)=1`; local leverage/effective mass; exponential exterior sensitivity; hard-edge behavior; Uvarov rank-one point-mass update; support/anomaly detection.

Vulnerable bridge candidate:

[CONJECTURE] A segregation front can be represented as a moving level set of a species-wise Christoffel leverage ratio, for example `log lambda_n^small(x)-log lambda_n^large(x)`, with Uvarov point-mass updates modeling saturation under local accumulation.

Immediate self-kill risks:

1. This may reduce to standard Christoffel support/anomaly estimation plus standard drift-diffusion segregation PDEs.
2. The bridge may preserve no invariant beyond the word "local concentration".
3. The Uvarov update is a known rank-one kernel identity, not a new saturation law.
4. The candidate has no consequence until it predicts a measurable front speed, shock location, stability criterion, or theorem about empirical measures.

Required to survive: produce a concrete `(S,P,M,T)` where `S` is a theorem or prediction, `P` is a proof/computation/experiment, `M` is a reusable method, and `T` transfers to a second nontrivial mixture or measure problem. Until then R1 is only a frozen protocol run, not knowledge.

### R1 Source/Formula Check

[HOLD -> KILL-risk high, 2026-06-23]

First source check found that both sides of the proposed bridge are already mature in the relevant direction:

1. Christoffel functions / empirical inverse Christoffel functions are already used for support estimation, density/leverage interpretation, outlier detection, and finite-sample geometric inference. Sources checked: Lasserre-Pauwels `arXiv:1701.02886`; Pauwels-Bach-Vert `arXiv:1805.07943`; Vu-Bachoc-Pauwels, ESAIM Probability and Statistics 26 (2022), 171-207, DOI `10.1051/ps/2022003`.
2. Granular segregation already has continuum advection/segregation/diffusion models and shock/front laws. Sources checked: Shearer-May-Giffen-Daniels, *The Gray-Thornton Model of Granular Segregation*; Fan-Schlick-Umbanhowar-Ottino-Lueptow, *Modeling size segregation of granular materials: the roles of segregation, advection, and diffusion*.

Exact bridge formula:

Let `K_n` be the degree-`n` Christoffel-Darboux kernel for a measure `mu`, and let `lambda_n(x)=1/K_n(x,x)`. For the rank-one update `mu_tau=mu+tau delta_a`, Sherman-Morrison/Uvarov gives

`K_tau(x,x)=K(x,x)- tau K(x,a)^2/(1+tau K(a,a))`.

At the accumulation point this becomes

`lambda_tau(a)=lambda(a)+tau`.

Interpretation: local accumulation of one species increases that species' Christoffel mass linearly at the pile-up point, while off-point effects saturate to a rank-one shadow. A species-wise Christoffel leverage-ratio front therefore has an exact estimator update law under point-mass accumulation.

Theatre verdict: this is probably not novel. The proof is a standard Uvarov/Sherman-Morrison identity, and the physical interpretation appears to be Christoffel support estimation applied to a standard segregation concentration field. R1 survives only if another agent extracts a nonstandard `(S,P,M,T)`: a front-speed prediction, shock-stability criterion, saturation law, or experimental classifier not reducible to Christoffel support estimation plus Gray-Thornton/Fan-style drift-diffusion.

### R1 Ballot Update: Question-Validity Is Not Enough

[STATUS: KILL unless rescued by a concrete transfer]

Turing's ballot: R1 is a vocabulary overlay unless it produces an uncatalogued fact. The question "Christoffel functions as segregation fronts" is valid, but a valid new question is only a search direction. It is not knowledge by itself. The answer must contain a new constraint-bearing fact, prediction, proof, or transferable method.

Therefore R1 currently fails `(S,P,M,T)`:

1. `S`: point-mass accumulation linearly increases Christoffel mass at the point.
2. `P`: Uvarov/Sherman-Morrison proof.
3. `M`: reframe physical accumulation as empirical-measure update.
4. `T`: missing. No front-speed law, shock-stability criterion, saturation prediction, or cross-mixture classifier has survived as nonstandard.

Current verdict: KILL as novel unless Wheeler or another agent supplies a concrete `T` that is not reducible to Christoffel support estimation plus granular segregation continuum theory.

## Workflow-General Run W1: Zero-Wealth Absorbing Boundary

[DEAD END / REDUCES, 2026-06-23]

After the user pointed to `logs/experiments/workflow-general.md`, Professor reran the protocol in its stronger form rather than relying on R1's preselected deck.

- Last RandomNode seed topic: `granular segregation`.
- Entropy seed: `3845766000613800379`.
- Step 1 cold prompt list, Step 2 RNG: item 13, `Wealth condensation in econophysics models`.
- Step 3 cold prompt list, Step 4 RNG: item 2, `The zero-wealth absorbing boundary`.
- Step 9 scientific-method RNG: method 10, `Test extreme cases`.

NODE constraint: in a yard-sale wealth-exchange model where the stake is proportional to `min(w_i,w_j)`, exact zero wealth is absorbing. Floors or redistribution make the boundary nonabsorbing.

RunPod NODE results:

Baseline (`n=1200`, `steps=300000`):

- absorbing: zero revivals `0/24`, near-zero fraction `0.104167`, Gini `0.891822`.
- tiny floor `1e-4`: zero revivals `24/24`, near-zero fraction `0`, Gini `0.884606`.
- redistribution `1e-4`: zero revivals `24/24`, near-zero fraction `0`, Gini `0.256065`.
- redistribution `1e-3`: zero revivals `24/24`, near-zero fraction `0`, Gini `0.0928939`.

Extreme cases:

- no exchange: zero revivals `0/24`, but no condensation (`Gini 0.02`).
- aggressive exchange: zero revivals `0/24`, near-zero fraction `0.925`, `Gini 0.990637`.
- floor `1e-2`: zero revivals `24/24`, Gini still high (`0.866297`).
- redistribution `1e-2`: zero revivals `24/24`, condensation suppressed (`Gini 0.0234919`).

Interpretation: the experiment confirms the NODE constraint and boundary cases, but it is not surprising. Transfer back to R1 remains a dead end unless a nonstandard `T` appears: identifying Uvarov point-mass update with discrete grain/floor corrections is testable, but currently reduces to known boundary regularization plus Uvarov/Christoffel support-estimation machinery.

## Workflow-General Run W2: Pre-Crisis Shadow Of Escape Channel

[DEAD END / REDUCES, 2026-06-23]

Workflow continued from last RandomNode `zero-wealth absorbing boundary`.

- Entropy seed: `691829661222804965`.
- Step 1 cold prompt list, Step 2 RNG: item 10, `Basin-boundary crises in chaotic dynamical systems`.
- Step 3 cold prompt list, Step 4 RNG: item 1, `Pre-crisis chaotic transients that already shadow the post-crisis escape route`.

NODE constraint: in a boundary crisis, the post-crisis escape channel is already present as near-hit geometry in pre-crisis bounded dynamics.

Experiment: logistic map near the `r=4` invariant-interval edge. For `r_post=4.01`, the escape hole is the interval around `x=1/2` whose image leaves `[0,1]`; for `r_pre=3.99`, bounded pre-crisis orbits can approach this would-be hole. Measured whether pre-crisis minimum distance to the post-crisis hole predicts post-crisis escape time better than a same-width control interval.

RunPod result:

- `escaped_within_max=8000/8000`, mean escape time `27.9394`.
- Spearman correlation of pre-crisis min-distance-to-hole vs post-crisis escape time: `0.207839`.
- Same-width control interval correlation: `-0.0406032`.
- Hole-distance quantile bins showed mean escape time rising from about `25` to about `33`; control bins lacked this monotone structure.

Transfer attempts:

1. de Bruijn-Newman heat flow: pre-critical zero geometry shadows post-flow off-line escape. Reduces to classical de Bruijn-Newman / Newman constant work.
2. Jensen/Laguerre hyperbolicity deformation: pre-failure root geometry shadows later nonreal-root escape. Reduces to known Jensen/de Bruijn picture.
3. Reciprocal Hankel/Krein index crossing: pre-crossing small Weyl margin shadows later negative-index escape. Reduces to existing `s_d`/Krein wall.

Verdict: workflow-faithful dead end. W2 confirms the NODE constraint and produces a clean control comparison, but no non-reducing transfer was found.

## Workflow-General Run W3: Noise-Induced Premature Escape

[DEAD END / REDUCES, 2026-06-23]

Workflow continued from last RandomNode `pre-crisis chaotic transients that already shadow the post-crisis escape route`.

- Entropy seed: `2735874861708935950`.
- Step 1 cold prompt list, Step 2 RNG: item 2, `Canard explosions in slow-fast biochemical oscillators`.
- Step 3 cold prompt list, Step 4 RNG: item 17, `Noise-induced premature escape from repelling slow manifolds`.

NODE constraint: noise causes trajectories to leave a repelling slow manifold earlier, with escape location controlled by accumulated repulsion and the logarithm of the noise scale.

Experiment: canonical normal model `dy/dt=eps`, `dX=y X dt + sigma dW`, escape at `|X|>=threshold`. The rough asymptotic is `y_escape ~ sqrt(2 eps log(threshold/sigma))`.

RunPod result:

- `sigma=1e-4`: median escape `0.356`, predicted `0.3824453`.
- `sigma=3e-4`: median `0.3214`, predicted `0.35255094`.
- `sigma=1e-3`: median `0.282`, predicted `0.3165639`.
- `sigma=3e-3`: median `0.24`, predicted `0.27971496`.
- `sigma=1e-2`: median `0.1828`, predicted `0.23272517`.
- `sigma=3e-2`: median `0.0684`, predicted `0.17941226`.

Transfer attempts:

1. de Bruijn-Newman: coefficient/model noise causes premature hyperbolicity loss near tiny margins. Known no-margin/dBN stability territory.
2. Jensen/Laguerre: coefficient noise near a root-collision boundary causes early nonreal-root escape. Known hyperbolicity-condition-number story.
3. Krein/Hankel: moment noise crosses the scalar Weyl gap early, governed by a standard perturbation ratio such as `s_d/(sigma ||grad s_d||)`.

Verdict: workflow-faithful dead end. W3 confirms the NODE but no non-reducing transfer was found.

## Theatre-Test Answer: Team Novelty Is A Protocol, Not A Vibe

[CONJECTURE refinement / user-prompted pivot, 2026-06-23]

The user is right to demote computations when the qualitative answer is already known before running them. In that case computation is only a witness, falsifier, or calibration device. It is not the novelty source.

The meta question should be stated with the theatre-test inside it:

> How can a heterogeneous LLM-agent team produce a checked artifact whose statement, proof, method, or transfer was not already recoverable by ordinary prompt interpolation from its training/context prior?

The easy answer is already known and should not be promoted: a closed transcript among models adds no independent truth channel. Model diversity changes the search distribution; it does not by itself create evidence. This reduces to data-processing/oracle-computation/common scientific-method folklore.

The live, nontrivial object is an executable protocol that prevents false novelty claims. The team should not ask whether a result feels surprising. It should require a provenance ledger for the artifact `(S,P,M,T)`:

1. `S` - statement/conjecture: was it source-known, warm-promptable, or merely a relabeling?
2. `P` - proof/witness: is the proof route itself new, or a standard proof with new nouns?
3. `M` - method: did the team introduce a reusable search/verification move that is not just brute force or consensus?
4. `T` - transfer: does the method change a second nontrivial target, or is there a principled obstruction to transfer?

Operational answer:

1. Freeze an external entropy source before hypotheses are generated.
2. Translate the random material into invariant bundles before any bridge is proposed.
3. Force role separation: proposer, source-killer, proof attacker, label-stripper, verifier/formalizer, and transfer attacker.
4. Attach every claim to a hard verifier where possible: proof checker, reproducible computation, source comparison, exact counterexample, or hand-checkable derivation.
5. Run warm-prompt ablation: if a normal direct prompt recovers the same `(S,P,M,T)`, demote the result to reachable interpolation unless the proof/witness has independent value.
6. Promote only compression: the final artifact must explain, prove, or predict more than the external witness it came from.

Critical consequence: `interpolation` is the wrong kill word when used loosely. Many real discoveries are new edges between old nodes. The actual kill condition is unselected interpolation: a plausible edge with no frozen entropy, no invariant preservation, no verifier, no compression gain, and no transfer consequence.

Current status: HOLD. The protocol is useful and significant for project conduct, but its components are close to established MDL, Popperian testing, adversarial collaboration, ablation, and data-processing ideas. The novelty target is therefore not the slogan, but one worked instance where this protocol yields a non-promptable, source-new, verified `(S,P,M,T)` in the HGT programme.

## Workflow-General Run W4: Nonhyperbolic Escape Tail

[DEAD END / REDUCES, 2026-06-23]

A further frozen-entropy tick was run after W3.

- Seed: `279994678386043821`.
- Random topic: `Escape from chaotic saddles in transient chaos`.
- NODE: `Escape dynamics may be nonhyperbolic, producing algebraic rather than exponential lifetime distributions`.
- Method: `Use a minimal counterexample`.

The NODE test cleanly separated exponential survival in a leaking mixing logistic-map control (`exp R^2=0.999717`) from algebraic survival in a leaking intermittent neutral-fixed-point map (`power R^2=0.998907`). This validates the random NODE but is source-known transient-chaos theory.

The minimal HT transfer, `nonhyperbolic phase defect escape has algebraic lifetime tail`, failed the theatre-test. The right-strip true and finite-Euler results almost coincide, so the statistic is not a native hypertranscendence or landscape invariant. Verdict: dead end; useful as another kill against recurrence/lifetime skeletons as novelty sources.

## Workflow-General Run W5: Tail-Index Uncertainty

[DEAD END / HYGIENE GATE, 2026-06-23]

A further frozen-entropy tick was run after W4.

- Seed: `3142228065337374667`.
- Random topic: `Heavy-tailed financial drawdown durations`.
- NODE: `Underestimated uncertainty in tail-index estimates due to few extreme durations`.
- Method: `Test small cases`.

The NODE test confirms a standard extreme-value warning: high log-log tail-fit `R^2` and tiny OLS slope SE can coexist with much larger repeated-sample variability. Example mixture case `k=20`: OLS empirical SD `0.2211`, naive SE `0.0374`, mean `R^2=0.9415`.

The minimal HT transfer failed as a novelty source. Phase-defect run-length tail estimates are dominated by a handful of runs; right-strip true and finite Euler nearly coincide. Verdict: dead end; keep only as a tail-exponent hygiene gate for future claims.

## Workflow-General Run W6: Road-Hierarchy Fractal Confound

[DEAD END / HYGIENE GATE, 2026-06-23]

- Seed: `1096590896978984582`.
- Random topic: `Fractal urban morphology`.
- NODE: `How road hierarchy can mimic fractal branching without reflecting self-organized urban growth`.
- Method: `Split it into subclaims`.

The NODE test confirmed that high box-count fractal `R^2` does not determine mechanism: deterministic hierarchy, stochastic growth, and random occupancy all showed strong scaling fits. The HT transfer likewise failed; in the right strip true and finite Euler were essentially identical on dimension, scaling fit, occupancy variability, and anisotropy.

Verdict: dead end for novelty. Keep only as a morphology hygiene gate against overreading fractal-looking phase/zero-shadow maps.

## Workflow-General Run W7: Multilayer Coupling

[DEAD END / HYGIENE GATE, 2026-06-23]

- Seed: `3677919641956617035`.
- Random topic: `Scale-free transport networks`.
- NODE: `Multilayer structure, where transport depends on interactions between roads, rail, air, power, or data layers`.
- Method: `Attack it as false`.

The NODE test confirmed that single-layer degree metrics can miss inter-layer dependency failures: low-degree dependency removals nearly collapsed the other layer. The HT transfer, `gamma prime weld coupling missed by single layer metrics`, did not produce a non-reducing invariant; right-strip true and finite Euler controls were nearly identical.

Verdict: dead end for novelty; keep as a hygiene gate against promoting separate Gamma/prime diagnostics without coupled-control separation.

## Workflow-General Run W8: Spin-Orbit Matrix Boundary Conditions

[DEAD END / HYGIENE GATE, 2026-06-23]

- Seed: `492832716409134168`.
- Random topic: `Quantum graph transport`.
- NODE: `Spin-orbit coupling requires matrix-valued boundary conditions and changes the scattering symmetry class`.
- Method: `Change representation`.

The NODE test confirmed the scalar/matrix distinction: spin rotation changes interference visibility and spin polarization in ways scalar phases cannot encode. The HT transfer, `gamma prime coupling needs matrix valued boundary diagnostics`, failed as novelty: the matrix lift was representation-dependent and did not separate right-strip true from finite/random controls.

Verdict: dead end for novelty; keep as a hygiene gate against arbitrary matrix-valued weld diagnostics.
