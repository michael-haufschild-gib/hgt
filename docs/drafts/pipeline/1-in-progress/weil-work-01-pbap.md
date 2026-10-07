# WP01 — Full PBAP existence research loop

- **ID:** weil-work-01-pbap
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / open target
- **Objective:** prove `RHTower.WeilOneSided.PrimeBlindPositive` without unproved mathematical inputs, then compile its application to full-positive existence.
- **Owned Lean scope:** `RHTower/WeilWorkPBAP*.lean`.
- **Result directory:** `docs/reports/weil-work/results/01-pbap/`.

## Current frontier

Exact full PBAP is finite nonnegative mixtures of compactly supported complex C² tests whose **symmetric** log-values cancel at every integer ≥ 2. Pole terms remain present. Full separation and realization already exist. No unconditional closing theorem found in exact lexical search (seven declarations, two modules).

Read: assigned package, shared contract, 7 October audit, relevant HF frontier and STATUS entries, two-walls and certified-pinning cards, full PBAP definitions. The earlier nonnegative/dilation-free paper claims do not settle signed mixtures; finite pinning does not settle all constraints. Existing tree has unrelated changes; preserve them.

## Working plan

1. Refresh internal and external frontier, inspect exact mixed-test and archimedean identities.
2. State an exact conjecture for a nontrivial mixed-cancellation class; attack falsity, circularity, parent-theory overlap, novelty.
3. Close paper proof before any Lean implementation. For failed conjectures, extract strongest positive survivor.
4. Formalize only proved statements; validate names and axioms in `/tmp`; foreground target compilation, targeted `--old` dependency builds only, no full builds or heartbeat changes.
5. Wire finished modules into umbrella as explicitly requested by user. Record exact evidence, limits and next conjecture; repeat.

`update_plan` and `multi_tool_use.parallel` are not exposed in this session; this file tracks plan, and independent reads use `Promise.allSettled`.

## Cycle 1 — contextualization / audit

- 2026-10-07: active goal already exists; preserve it. hgtl7 read and applied.
- Exact query: `research 'PrimeBlindPositive' --mode lexical --exact --per-module 0 --explore 0`, exit 0. Full target at `WeilFullConeOneSidedCriterion.lean:431`; existence equivalence at 451.
- Deep query in flight: `research 'prime blind signed mixtures archimedean pole positivity' --mode deep --module Weil --budget-seconds 300 --json`, output `/tmp/wp01-pbap-search.json`.
- External starting audit: Connes–Consani arXiv:2006.13771; Suzuki arXiv:2606.09096 v3 (23 September 2026); compact-window arXiv:2608.24827. No inference of a global PBAP theorem from abstracts.
- Next: inspect signed dilation-free exchange and exact full mixed energy before choosing conjecture. No new proof claimed.

## Cycle 1 attack outcomes

- Deep initial search completed, `partial=false`, 68,275 indexed files; compiler metadata mostly source-only/pending. Inspected both candidate lemmas and source arguments. No unconditional full PBAP theorem found.
- Scalarization candidate killed as **REDISCOVERED**: classical Boas–Kac–Krein factorization, already explicitly in corpus L248 (`krein-producer-loops.md:4968`). Later L382's rank-gap remark conflicts with that earlier result unless regularity is left unpaid. Wrote precise smooth-approximation/repair argument in `PROOF.md`; no new scientific claim.
- Positive atom repair is **BRIDGE**: mechanism already inside polar duality. Extracting a full-functional quantitative repair bound because exact preservation of all nodes matters for approximation. Module `WeilWorkPBAPNullRepair.lean`; first compile failed only because `Zeta23` namespace was not opened; fixed. Final audit pending.
- Polar-to-full conjecture remains unproved; conditional positive type alone leaves exponential homogeneous terms. Do not assume their normalization.
- Existing L390 already rejects total-mass-only use of the log-lattice estimate; meaningful two-cluster positivity needs frequency-resolved absorption.
- Serena `find_symbol` rejects the Lean path as ignored (project language is Python). Used exact `rg` and bounded source reads instead.

## Next sign conjecture to interrogate

Seek a genuine analytic lower bound for the full form on signed two-interval tests, extending to positive mixtures with aggregate cancellation. Earlier L369/L370 use only the minimum killing weight and lose the boundary variation. Candidate mechanism: retain the spatially varying killing weight plus the internal exchange operator, and bound its rank-one negative part through a resolvent integral instead of replacing the killing weight by its minimum. First audit must determine whether this is already a classical logarithmic-Laplacian estimate and whether it can reach the exact cross-block threshold. No numerical experiment or unproved lower bound is being used.

External parent theory located: Laptev–Weth, *Spectral properties of the logarithmic Laplacian* (2021), especially Theorem 4.1 and its one-dimensional limitation. This is a parent-theory audit, not yet a new positivity theorem.

## Cycle 2 — novelty failure and completed repair bridge

- The proposed small two-window positivity sector is **REDISCOVERED / INSIGNIFICANT** as a frontier target. Zhu, arXiv:2608.24827 v2, proves full complex-test positivity for support in `[−0.8,0.8]` (length 1.6). On an aggregate integer-null mixture, the prime term cancels. The initially contemplated two-window diameters are already covered. Do not mistake the half-width 0.8 for the full supported interval length.
- Retaining the boundary killing weight gives a weighted Cauchy–Schwarz / rank-one resolvent estimate, but no new sign theorem was closed. Its missing step is an exact lower bound at the relevant cross-block threshold. Do not formalize the generic rank-one inequality as a PBAP advance.
- Deep co-Poisson and divisibility searches returned partial results; inspected candidate lemmas and source arguments. Neither supplies the missing positivity input. The short-window search completed but its archimedean results did not establish the needed lower bound.
- `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPNullRepair`: exit 0. This targeted build compiled the new leaf; existing dependency diagnostics were replayed. The intermediate smoothness addition needed `open scoped ContDiff`, now fixed.
- Required direct audit `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPNullRepair.lean`: exit 0. No diagnostics.
- Wired exactly one import into `RHTower.lean`; did not build the umbrella. `scripts/formal_tools.py index`: exit 0. No numerical experiments, new assumptions, heartbeat changes, commits, or pushes.
- `scripts/formal_tools.py lint`: exit 1, eight unrelated modules unreachable from their umbrellas. No error identifies the owned PBAP module. Exact paths recorded in `EVIDENCE.md`; do not modify other agents' work to hide the global failure.
- Axiom/name audit in `/tmp/wp01-audit.lean`: exit 0. All eight capstones use only `propext`, `Classical.choice`, `Quot.sound`. Final source hash `00d96a1f5d99637bd6731d1c3b18ef249255a3b9`. Owned Lean processes have exited. Goal remains open.

## Cycle 3 — exact candidate, not yet an accepted route

Corpus L353 identifies integer-null spectra as representing measures for evaluation at the origin of the prime polydisc: after symmetrizing the spectrum, every nonconstant holomorphic monomial has mean zero. A possible stronger conjecture is:

> For every nonzero smooth compactly supported integer-null test, let `nu` be the probability measure obtained by pushing its normalized even spectral density to `(p^(it))_p`. Then, for every polynomial `P` in finitely many prime coordinates with `P(0) != 0`, `integral log|P| dnu >= log|P(0)|` (extended integral).

This is a Jensen-measure assertion, **not** a consequence of the moment identities. No implication from it to PBAP has been proved. Kill tests before adopting it: (1) examine the actual representing-measure/Jensen distinction for the polydisc; (2) determine whether positive exact repair makes all representing measures weak limits of these spectra, without any energy bound; (3) if so, algebraic prime-torus constraints cannot supply an extra Jensen property absent in general representing measures. Height/energy control would remain essential.

Internal exact text search across owned Lean source and research docs found no `Jensen measure` terminology; the broader corpus search also surfaced unrelated Bohr-lift and moment material. External parent theory: Cole–Gamelin (1986), *Representing Measures and Hardy Spaces for the Infinite Polydisk Algebra*, DOI 10.1112/plms/s3-53.1.112. Only its abstract was accessible; no precise theorem imported. Nilsson (2026), arXiv:2602.10853, proves representing/Jensen noncoincidence for smooth strictly pseudoconvex domains; this does **not** by itself settle the polydisc or this spectral subclass. Candidate status: UNDECIDED; not Lean code and not a claimed advance.

### Cycle 3 progress / next continuation

A concrete bidisc representing measure violating Jensen is now derived on paper: transfer a small amount of Poisson measure from the diagonal disc to a Blaschke graph passing through `(a,a)`. Both represent `(a,a)`, so the difference preserves representation at the origin; a polynomial vanishes on the graph but not at the origin. This adapts the classical representing/Jensen distinction, not a claimed new general counterexample.

The proposed positive survivor is stronger than the initial repair-based sketch: **all representing measures on the prime torus are weak limits of normalized smooth, exact integer-null finite mixtures**. Fejer smoothing has an explicit finite Gram sum of squares, and multiplying its pullback by a broad Fourier envelope yields exact nulls via finite frequency separation. No scalar factorization or numerical search is needed. Full paper construction and the bidisc formulas are in `results/01-pbap/TORUS-DENSITY.md`.

Next continuation must adversarially audit this construction, judge novelty, and formalize the surviving exact finite-moment realization before retiring the Jensen route. Source-checked starting lemmas: `RHTower.weilTest_translates_log`, `RHTower.weilTest_translates_neg_log`, and `RHTower.weilTest_sum_translates` in `WeilPositivityMultiplicativeToeplitzBound.lean`. They already select the divisibility diagonal for sufficiently narrow common packets. No need to repeat the scalar translate proof. A new result must retain actual test functions, not merely an abstract assumed moment functional.

Crucial limit: compact-torus weak convergence forgets absolute frequency height. Neither density nor the Jensen counterexample says the full Weil energy is negative. A future positive argument still needs control of that energy. The Jensen no-go is not marked closed or Lean-proved.

## Self-audit

- Anti-theatre: the new Lean result repairs constraints and bounds energy change. It does not prove the repaired energy nonnegative. Verdict BRIDGE, not significant PBAP progress.
- Anti-laziness: checked scalarization against both classical factorization and prior L248; checked the proposed window sector against the current full-window result; inspected full integer cancellation and retained both pole terms. Next work must attack a new sign mechanism or kill the Jensen candidate with a precise counterexample/closure argument, not add wrappers around PBAP.

## Continuation — finite Gram realization

- Previous turn classification: **progress** (new compiled bridge, source/axiom audits and exact next paper construction), not completion of PBAP.
- hgtl7 applied again. Current source and task checked. Verdict for the finite Gram realization: **BRIDGE**; no novelty claim. It is needed to certify actual test mixtures in the proposed Jensen no-go's positive survivor.
- Complete finite-subtheorem paper proof appended to `TORUS-DENSITY.md`: every PSD matrix on labels 1..N yields smooth compact tests with exact rational-log sample formula for all numerators and denominators <=L. The common bump discharges the analytic support condition; integer separation selects `a*k=b*j`. Only finitely many divisibility-diagonal identities are needed for all integer nulls.
- New source `WeilWorkPBAPGramPackets.lean` implements this finite realization. First direct compile in flight; do not yet cite it as verified.
- `/tmp/wp01-gram-names.lean`: exit 0. Verified Gram factorization and all initially needed mathlib names; complex matrix positivity needs scoped `ComplexOrder`, `MatrixOrder`, and `Matrix.Norms.L2Operator`.
- Refreshed deep `prime blind finite moment torus realization` search was partial and mostly unhelpful. Inspected candidates/source arguments; suggested Weil-positivity implication is circular for PBAP. External audit found classical parent approximation/representing-measure theory, not a demonstrated novelty claim for this application.
- Full weak-density theorem, Jensen obstruction transfer, and full Weil-energy control remain unformalized. Goal remains the unconditional full PBAP theorem, not completion of these bridges.

### Finite realization verified; audits complete

- `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPGramPackets.lean`: exit 0, no diagnostics. `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPGramPackets`: exit 0; only requested leaf built, dependencies reused. The unchanged source hash is `0647ce6d3dfb8abb197616fe3f575c5999128ca5`.
- Capstone `exists_nullPacket_mixture` constructs actual nonnegative Finsupp weights with every WP01 null constraint, exact mass and rational samples. It does not assume or prove the energy sign. Empty and zero matrices remain covered; positive trace is visible through the mass identity.
- Explicit existing import supplies `weilTest_self_neg`; scratch API/bridge checks both exit 0. Fixed local compact-support extensionality and cast/simplifier issues. No new assumptions or heartbeat changes.
- Added the GramPackets import beside this agent's earlier NullRepair import. No umbrella build. Index refresh and owned diff check exit 0. Final ten-capstone axiom audit exit 0: only `propext`, `Classical.choice`, `Quot.sound`. Global lint exit 1 on nine unrelated umbrella-reachability errors, listed in `EVIDENCE.md`; neither owned PBAP leaf is flagged. All owned commands exited.
- Energy search found `WeilWorkExposingRayPacketCoercivity`; its polar compact-primitive mechanism does not automatically extend to the present nonpolar packets. `HTGeometry/BohrMultiFejerMultiplier` already contains the exact coordinate fibre count and product multiplier. Reuse those for the larger density proof.
- A uniform positive logarithmic frequency moment prevents torus approximation to Haar by tightness; the prime orbit has Haar measure zero in a two-prime torus. This is a classical compactness observation, recorded without claiming novelty. A bound on full Weil energy does not itself give that moment bound: negative pole terms are an unpaid issue.
- Posted all five anti-theatre and four anti-laziness answers in chat. Verdict remains **BRIDGE**. PBAP sign frontier has not moved; no scientific novelty claim. Do not let finite matrix wrappers replace the actual sign problem.

### Exact next continuation

Connect the representing measure to the now-verified packet theorem: form its finite holomorphic-monomial moment Gram matrix, prove PSD and zero pure-sign entries, and use finite prime-exponent boxes to obtain trace one and the exact product Fejér multiplier at each rational observation. This must include actual normalization of the packet mixture, then the convergence argument, before retiring the Jensen route. The existing Fejér counting API is source-checked but not yet name-checked in a new scratch import. Keep the full-energy issue separate: no topology or weak-density argument currently controls both the gamma term and the potentially negative pole term. The paper bidisc counterexample and the exact finite subtheorem are in `TORUS-DENSITY.md`.

## Continuation — representing-measure moment matrices

- Previous turn: **progress**. Rechecked current GramPackets source hash; unchanged from the passing audits. hgtl7 reread, relevant memory read, architecture/testing docs absent. Main objective remains full unconditional PBAP.
- Complete deep search `representing measure monomial Gram positive semidefinite torus Fejer` returned `partial=false`, 68,336 files. Candidate lemmas and source arguments inspected. Exact text search found the existing complex integral-Gram positivity theorem in `HTGeometry/ComplexIntegralGram.lean`; it directly matches the required orientation and avoids reproving generic positivity.
- External audit revisited Cole–Gamelin's infinite-polydisk representing/Jensen theory and the primary several-variable positive-kernel literature. Neither is being cited as the desired spectral density theorem. Verdict for the next connecting theorem: **BRIDGE**, with no novelty claim.
- Closed paper theorem appended to `TORUS-DENSITY.md`: any representing probability measure yields an actual weighted monomial Gram matrix with individually zero nontrivial divisibility entries, exact trace, and rational-fibre factorization. Composition with GramPackets gives actual smooth null tests and an explicit target-moment multiplier. Normalization and exponent-box convergence remain required.
- Scratch `/tmp/wp01-moment-names.lean` now checks prime-phase definitions, multiplicativity, continuity, measure structures, and existing Gram/integrability APIs before source implementation. One foreground Lean process; no new leaf written yet.

### Representing-measure realization compiled

- Discarded the custom circle-coordinate prototype after source search found `InfiniteTorusCharacter`, its character-density theorem, and `SmoothNumbers.primeExponentVector`. Reused the corpus's additive prime torus, integer characters, and complex integral Gram positivity. Revised scratch `/tmp/wp01-torus-names.lean`: exit 0.
- New owned leaf `WeilWorkPBAPMomentPackets.lean` proves character arithmetic, moment-matrix positivity from the actual measure, individually zero divisible entries, exact trace, and rational-fibre factorization. `exists_normalized_representing_mixture` constructs actual smooth compact tests and nonnegative Finsupp weights with mass exactly one, every integer-null constraint, and sample `M_mu(a,b) * packetCoeffCorrelation(d,a,b)` for all positive numerators and bounded denominators. Representation and unit coefficient normalization specify the input objects; no energy positivity premise is introduced.
- Direct source compile after normalization: exit 0, no diagnostics. Added the leaf's umbrella import; targeted `--old` leaf build now in progress. Final direct-source and axiom audits remain pending. No umbrella build.
- Deep box-overlap search completed with `partial=true`, 68,348 indexed files, reranking deadline, and a running background indexer. Candidate lemmas and source arguments inspected. Most hits concern unrelated additive correlations; none closes the desired multiplicative box overlap. Existing `BoundedSmoothWitnesses.card_isBoundedSmooth`, `BohrMultiFejerMultiplier.card_fejerFibre`, and `InfiniteTorusCharacter.span_torusCharacter_closure_eq_top` remain the relevant source-checked ingredients.
- Remaining construction: choose normalized prime-exponent-box coefficients, prove their exact multiplier and convergence, connect actual spectral probabilities to the prime torus, then transfer the paper non-Jensen witness. Full Weil-energy sign remains open. This leaf is a **BRIDGE**, not a scientific novelty claim or PBAP solution.

### Next obligations fixed on paper

- Source-checked `WeilRegularDeviationRigidity.pairTransform_ofReal`, `weilTest_eq_integral`, and `exists_norm_pairTransform_le` provide literal C² Fourier inversion and integrability. Use these to build the nonnegative density of the actual test mixture, normalize it by its verified mass, and push forward along `clockPhasePoint (log p) (2*pi*xi)`. Avoid producer spectral-measure theorems with `WeilPositiveFull` as an input. The Schwartz inversion route is also available in `ConstrainedWeilFourierMultiplier`, but is unnecessary for C² tests.
- `TORUS-DENSITY.md` now records the complete next paper argument: box coefficients of norm one; multiplicative fibre count; exact product multiplier; error at most `sum |v_p|/(K+1)`; all characters represented by positive/negative prime products; character-density extension to weak convergence. Source-checked APIs still need a fresh `/tmp` Lean name check before implementation.
- Direct energy audit revisited L178, L259, L260, and L353 in `krein-producer-loops.md`. Primitive-set narrow-packet positivity already has a mean-value mechanism in L353; do not present it as new. Positivity of the newly constructed moment matrix does not bound its signed pole energy against gamma. No sign theorem or rate has been extracted. External integral comparisons of doubly positive functions impose pointwise nonnegativity absent here and cannot supply the missing estimate.
- hgtl7 self-audit posted in chat: no scientific novelty or PBAP sign advance; no difficulty-based skipped step; reuse existing mechanisms and finish the concrete no-go survivor rather than count interfaces as discoveries. After density/Jensen closure, return to the actual signed pole-versus-gamma estimate. An approximation usable for that purpose must control full energy; torus weak convergence alone cannot pay it.

### Final validation of the normalized realization

- Targeted leaf `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPMomentPackets`: exit 0. Only this leaf was built; dependencies reused. Final direct `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPMomentPackets.lean`: exit 0, no diagnostics.
- Ten-declaration `/tmp/wp01-moment-audit.lean`: exit 0, only `propext`, `Classical.choice`, `Quot.sound`. Source hash unchanged: `7f77ab2fbe9632cca6aae99daf0eec2ee4699172`.
- Umbrella import added, no umbrella build. Index refresh and owned diff check passed. Global lint failed on eight unrelated reachability errors, recorded in `EVIDENCE.md`; no PBAP leaf flagged. All owned commands exited. Abandoned custom-coordinate scratch removed. No commits or pushes. Goal remains active and unsolved.

## Continuation — actual spectral probabilities

- Previous turn classified **progress**: normalized realization compiled and audited. Revalidated current source hash, unchanged. hgtl7 applied; relevant memory read; architecture/testing docs absent. Full PBAP remains the objective.
- Refreshed deep corpus search for actual Fourier-square probability measures started. Source inspection identifies existing literal C² inversion (`WeilRegular.weilTest_eq_integral`), square-transform integrability (`integrable_normSq_paperFT`), torus character evaluation along `clockPhasePoint`, and probability pushforward APIs. The paper construction is already dependency-closed in `TORUS-DENSITY.md`.
- External audit again finds classical representing-measure parent theory; no novelty established for this probability connection. Verdict **BRIDGE**. Its purpose is to complete the actual-measure density survivor, not to replace the energy-sign problem.
- Plan: verify names/normalizations in `/tmp`; construct the actual spectral probability and rational-character identity; compose it with the verified normalized packet realization; complete targeted/source/axiom audits and wire the leaf. Then advance the exponent-box multiplier and limit, preserving the full original goal.

### Spectral probability leaf built

- `/tmp/wp01-spectral-names.lean` passed. It verifies integrability under the signed Fourier rescaling, prime-log character detuning, continuity of the phase flow, and the measure APIs. Corrected a namespace mismatch and an explicit nonzero proof in scratch.
- `WeilWorkPBAPSpectralMeasure.lean` now defines the actual Fourier-square density for every C² Weil test and its finite mixtures, proves inversion and mass, constructs the spectral probability, and pushes it to the prime torus. `phaseMoment_spectralTorusProbability` identifies every positive rational character moment exactly with `mixtureSample`.
- The complex-null subclass gives `spectralRepresentingMeasure`; `exists_spectral_representing_mixture` composes the actual measure with the earlier smooth, normalized packet construction and retains the exact coefficient multiplier. The real WP01 constraints need the separate symmetrization already recorded on paper; no equivalence with that broader cone is claimed by this leaf.
- Targeted `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPSpectralMeasure`: exit 0. Added its umbrella import; no umbrella build. Axiom and final direct-source audits pending. Repaired norm/absolute-value simplification, beta reduction in integral rewrites, and a real-to-complex subtraction cast. No heartbeat changes.
- Refreshed spectral-measure deep search: `partial=false`, 68,352 files; candidate lemmas and source arguments inspected. Generic measure hits did not replace the actual Fourier construction. Further lexical box API search located the expected bounded-vector equivalence and one-coordinate fibre theorem. A divisor-overlap search is checking whether a stronger existing counting interface can shorten the next proof.
