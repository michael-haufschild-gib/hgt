# CHMD exact algebraic spectral inverse — 2026-10-16

RH goal ACTIVE, unbounded, unproved. Continue the original goal; do not mark complete. Read goal attachment on each new turn: /Users/michael/.codex/attachments/2c5020c9-b71c-40b8-ba6c-e8fb1100e229/pasted-text-1.txt. User forbids web/external novelty audits, numerical experiments, old research Markdown; use corpus search and actual Lean source. One owned foreground Lean/build process at a time; targeted --old builds and final plain lake env lean; no full/umbrella builds. No subagents, commits, pushes, or heartbeat increases.

Card completed and moved to docs/drafts/pipeline/3-formalized/chmd-finite-sample-operator-action-2026-10-16.md. This turn is structural progress: exact algebraic inverse and automatic finite-sample classification, not another bound or RH criterion. External scientific novelty not assessed.

## Seven completed root-wired leaves (namespace RHTower.CHMDDoobGraph)
1. CHMDMassWeakGenerator (109 lines, 8 decls): compact-core weak pairing gives R(2w+b)=w, actual maximal-domain membership, Lw=w+b, exact graph lift/pair/energy.
2. CHMDMassWeightedKernels (91,12): literal weighted real/imag Fourier kernels, polar image pairing, translated cosine phase kernels.
3. CHMDFiniteSampleGenerator (159,18): FiniteMassSampleSupport S w means both samples at +/-gamma(rho) vanish outside finite S. Explicit massFiniteImage S w retains all actual multiplicities and polar corrections. finite_samples_resolvent_identity, finite_samples_mem_arithmetic_domain, arithmeticGenerator_finite_samples, exact graph pairing/energy/divisor formula, support independence.
4. CHMDCardinalOperatorAction (180,22): actual cardinal frame source readouts and finite orbit support, explicit operator/resolvent images; exists_translatedCardinalOperatorFrame and premise-free exists_positive_cardinal_operator_packet.
5. CHMDFiniteSampleRange (166,16): finite-support mass vectors stable under sums/scalars; finiteSampleImageSpace submodule defined by actual resolvent witnesses. Image contained in massSamplingSpan; translated phase kernels are actual finite-support images.
6. CHMDPhaseKernelSynthesis (149,13): small-shift phase span lies in four-kernel span, hence finite-dimensional and closed. Orthogonality + existing exponential_pair_separation gives both +/-a Fourier values zero. Double orthogonal complement gives exact algebraic membership of literal kernels in phase span. Every Xi real/imag kernel is a finite-support image.
7. CHMDAlgebraicSpectralInverse (229,15): polar kernels from ground/odd images, imaginary polar kernels zero; all sampling kernels belong to finiteSampleImageSpace. Capstones:
- finiteSampleImageSpace_eq_samplingSpan, line93: exact (L-1)(V_fin)=algebraic sampling span.
- finite_sample_generator_image_iff, line199: for every u in actual arithmeticGenerator.domain, (Lu-u) belongs to massSamplingSpan iff u has finite Xi-sample support.
- exists_unique_reduced_generator_inverse, line217: every b in algebraic sampling span has a unique actual maximal-domain preimage orthogonal to critical eigenspace; no finite-support restriction on competitors. Its finite support follows automatically.
No RH, zero simplicity, finite number of off-line zeros, closed-range, or convergent infinite expansion assumption. Vector-class hypotheses are explicit.

## Proof closure
The arbitrary-mass mixed formula reduces to a literal finite kernel sum under finite sample support. Compact C2 operator core extends weak pairing to the maximal domain, then resolvent symmetry gives explicit R(2w+b)=w. Translated cardinal images span phase kernels; finite-dimensional closedness and exponential separation recover all divisor kernels algebraically. Ground and odd polar sources recover remaining two polar real kernels. Remove critical projection to choose reduced preimage. Any two same-forcing preimages differ by a critical vector (critical_difference_of_resolvent_preimages), so samples agree (samples_eq_of_resolvent_preimages). Thus any maximal-domain solution with algebraic forcing inherits finite sample support, proving the converse and uniqueness among all reduced domain vectors.

## Corpus overlap audit requested by user
CHMDBirmanSchwingerBound.lean:471 already proves CHMDPolar.orthonormal_primitive_bound_states_le under offLineZeros.Finite: k <= 2*offLineZeros.ncard for an orthonormal primitive family with resolvent eigenvalues >1/2. Compact-test negative-index rank argument at382, finite-rank defect nonnegativity at98. These are existing results, not reproduced or claimed new. They do not exclude bound states or prove the new maximal-domain inverse classification. Existing theorem was directly Lean/axiom audited in preceding part of this session; see mem:rh/chmd-mass-spectral-admission-2026-10-16.

Six discovery queries completed partial=false, errors/unfinished empty, inventories72875-72885 complete. Repeated broad Birman hybrid query useful but partial with text/source retrieval interrupted, inventory72890/72890 pending0; exact lexical orthonormal_primitive_bound_states_le returned one exact declaration. Compiler metadata mostly pending/stale; do not claim global absence from retrieval. Concurrent CHMDBoundStateInertia source was inspected at425-482: negative compact-test subspace injects into bound-state space and a separated deep-zero finite-level lower bound. Other writer completed/wired it; not owned or audited by this lane. Do not propose that lower bridge as new.

## Verification and cleanup
All seven targeted --old leaf builds passed. All seven final plain lake env lean checks exit0, empty logs. All104 declarations audited through /tmp #print axioms, names matched exhaustively, only propext/Classical.choice/Quot.sound. API probes passed, including add_sub_cancel_left.{0}; explicit universes required in generic have probes. Root imports each leaf exactly once; final source hashes matched audit snapshot. formal_tools.py index exit0; formal_tools.py lint --check-generated exit0, only existing large-file warnings. git diff --check passed. Card moved3-formalized. All34 owned /tmp search/API/axiom/build/final/index/lint files removed with explicit apply_patch Delete File and absence verified. Every owned tool process terminal, no owned Lean/build process remains.

Serena ignores Lean paths: find_symbol returned explicit ignored-path error; use rg + apply_patch fallback. Preserve concurrent unrelated changes in docs/reports/STATUS.md, rh-current-frontier-map.md, rh100-021 card, and CHMDBoundStateInertia leaf/card/memory/import.

## Audited SHA256
CHMDMassWeakGenerator ee2a8ebef54cab58565e8155048a04435216f6aee89e5e60fe98a5b59c5a78f3
CHMDMassWeightedKernels edf445ebd66d469c21dd7d802c9f1396b90ef1ad62c23a3c53d72e1c86805288
CHMDFiniteSampleGenerator 0dcafe09ada4440a25a132016e60da6a1c65047f1c9b6ee3c9e471dc8f4fc657
CHMDCardinalOperatorAction dcd20e4f0cb98c74fb070eb525164ba8463fb52edad0fd847ca5b7fb4f07c104
CHMDFiniteSampleRange a9272684f1a50e33e4846fd6dc2577dd46c63bc41a3ea3b221145d2ff89457e1
CHMDPhaseKernelSynthesis c274e981cc90f762ea3758ab492d09b27d63b5b4b723a13b2253820c73dd24f7
CHMDAlgebraicSpectralInverse da6911aa177624f31a4ead8575de9ab01623e791d6d95cd118b6c53067a90af7

## Remaining hard frontier
Primitive bound-state exclusion remains open. Algebraic sampling inverse does not provide a bounded inverse, closed range, an infinite cardinal series, or exclusion. Next research must attack actual sign/exclusion or an indispensable completion theorem with a dependency-closed proof; avoid routine repackaging of the present range identity and existing inertia/parity criteria.