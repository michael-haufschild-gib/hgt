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

### Active checkpoint — many-node certificate, 8 October 2026

`WeilWorkPBAPJointFixedCutoff.lean` implements the literal even plateau
and normalized cosh weight from MC6. Targeted build PASS226.30s,
final direct-source PASS116.70s with empty diagnostics, all 28 public
standard-only axiom audits PASS80.67s. Wired and indexed. Seven supporting
leaves now have 67 public audits; MC6/MC8 and full PBAP remain OPEN. The bounds use one
constant C for `|v|<=C`, `|v'|<=C/W`, `|v''|<=C/W^2`, uniformly in every
real center L and `0<W<=1`. Preserve the exact leading mass
`W*integral(psi)` with error at most `4e W^2`, and uniform inverse-square
complex Fourier decay. No new positivity capstone is claimed. The growing-order hybrid query
returned partial=false (68,839 indexed files), compiler freshness pending;
all 20 candidate lemmas and 20 source arguments were inspected. A narrower
lexical Sieve query found `log_factorial_le` and the existing blockLambda
schedule interfaces. Their fixed dyadic saving window does not discharge
the short-window MC6 budgets; reuse the factorial estimate, retain the
actual short length, and prove the growing-order budgets explicitly.
The paper now gives a shorter MC6 schedule proof using the corpus
window-landing theorem with `mu_k=4^k*lambda_k`; three eventual inequalities
replace individual frequency bands. The explicit floor/ceiling geometry
uses `Cgeo=4e+3`, paying BOTH roundings and the padded endpoint. Next scratch
`WeilWorkPBAPJointGridGeometry.lean` now proves the actual growing width,
integer endpoints, dyadic containment, short length and logarithmic coverage.
Targeted build PASS8.18s; final direct-source PASS4.39s, empty log; six public
standard-only axiom checks PASS2.04s. Wired and indexed. Eight supporting
leaves now have 73 public audits. Latest index PASS15.94s; lint EXIT1 12.21s
on eleven unrelated reachability errors, no WP01 finding. The next scratch
is `/tmp/wp01-growing-order.lean`: actual ceiling order, power and factorial
budgets. Only one owned foreground Lean process runs.

Paper proof: `results/01-pbap/JOINT-MANY-NODE-CERTIFICATE.md` (relative to
the Weil work report directory). MC2 uses ALL actual active integer nodes
at W=kappa L exp(-L/2), for arbitrary fixed kappa>0. It gives an explicit
cosine certificate and L/4 physical-mass margin, with NO correction-mass
cap. Paper proof is closed; Lean implementation remains OPEN. Full PBAP
and broad-profile MH2 remain OPEN. No novelty claim from formalization.

Key discovery: `Sieve.phase_prefix_bound` retains H=M-N. Its normalized
error is `(4^k lambda)^(1/(2^k-2))+(H^2 lambda)^(-2/2^k)`. For H~L sqrt N,
bands `[N^(k-1)/sqrt L,N^k/sqrt L]` have both errors tending to zero and
meet without gaps. This supports a many-node certificate beyond the
nearest-node boundary. A continuous certificate first cancels the exact
leading pole through the existing positive modulation kernel; integer
quadrature transfers it at low heights. Intermediate heights use the
short-prefix estimate; high heights use exact-mass Gamma coercivity.

Implementation plan: continuous modulation certificate; normalized short
prefix bounds; actual smooth integer quadrature and Abel bound; finite-band
gluing; all-frequency and actual-prime/null capstones. No conditional
positivity premise. Finish targeted source/axiom audits, wire leaves, then
attack growing kappa (candidate log log L) with a fresh uniform-order audit.

Further paper audit closed MC3 and MC4 in the same certificate document:
W=(m0/J)b L log log L exp(-L/2), 0<b<1/log2, for ANY fixed nonzero smooth
complex profile supported in [0,1], J=integral |Re autocorr|. Signed node
coefficients are allowed, so no nonnegative-autocorrelation assumption is
needed in MC4. Its separate proof uses the exact density mass and L1 density
bound to prove a uniform Gamma floor, and an absolute cosh pole remainder.
No division by the possibly zero source integral occurs. These stronger
statements are PAPER PROVED, LEAN OPEN, not full PBAP.

`WeilWorkPBAPJointContinuousCertificate.lean` is wired and fully audited.
Its nine public theorems include nonnegativity/dilation of
the actual cosine integral, the nonnegative-correlation continuous energy
certificate, and the literal unit-bump quantitative bound. Targeted
`--old` build (79.05s), final direct-source (93.31s) and all nine standard-
axiom checks (227.82s) pass; chain exited 0. This leaf proves the MC2/3
continuous component; it does not yet formalize discrete MC2, MC3 or MC4.

`WeilWorkPBAPJointShortPrefix.lean` is audited and wired: targeted125.40s,
final direct100.73s, two standard-only axiom checks11.04s, chain exit0.
It retains the explicit derivative-order budget and signed finite
Abel variation. Its numerical hypotheses still need discharge on the actual
logarithmic intervals; this technical bridge is not a positivity capstone.

`WeilWorkPBAPJointGammaFloor.lean` is audited and wired: targeted67.36s,
final direct25.16s empty, six standard-only axiom checks96.68s. The Gamma
proof retains coefficient two using exact density mass and the fixed
integrable log deficit.

`WeilWorkPBAPJointSignedCertificate.lean` is audited and wired:
targeted77.82s, final direct63.46s empty, seven standard-only axiom
checks65.09s. Positive absolute correlation mass, exact pole identity,
quartic dilation remainder and arbitrary-complex continuous certificate
are complete. All four new leaves (24 public checks) have unchanged audited
SHA256 hashes and pass whitespace checks. No discrete MC4 capstone is claimed.

MC5 in the certificate paper proposes one common derivative schedule for
ALL widths between kappa0 L exp(-L/2) and (m0/J)b L log log L exp(-L/2).
The uniform-quantifier paper argument is closed; internal overlap search
completed (partial=false,68,806 files, stale coverage snapshot and pending
compiler metadata). All candidate/argument/idea sets inspected; no closing
prior capstone found, no novelty inferred. Lean is OPEN. Prefer this signed, unnormalized discrete
certificate when formalizing, avoiding division by the source integral.

Concrete discrete implementation: take n=floor(exp(L-W)),
m=ceil(exp(L+W))+1 and weights rho((log j-L)/W)/j. On [n,m], use fixed
global bounds for rho and rho' to bound the derivative by
4/N^2*(A1/W+A0*(1+abs T)). Length is O(NW) uniformly once NW>=2.
Existing right-endpoint BV quadrature applies after translating [n,m] to
[0,m-n]; left-versus-right endpoints add only O(1/N), so no endpoint-zero
lemma is needed. The same derivative bound with T=0 pays signed Abel
variation. Real-valued cosine quadrature plus real-part extraction from
`Sieve.natCast_cpow_neg_I_mul` suffices; no new complex substitution theorem.
Pay the log change of variable with `intervalIntegral.integral_comp_mul_deriv`.
All sums and integrals must stay on positive x; Real.log on negative x must
not create a spurious second support interval.

MC6 supersedes the fixed-profile implementation target: see
`JOINT-UNIFORM-PROFILE-CERTIFICATE.md`. With one fixed smooth plateau cutoff
of integral A, b>0 and A*b*log2<1, every sufficiently large L and ALL smooth
complex f,g supported in [0,b L log log L exp(-L/2)] satisfy
Q_lambdaStar(f+translate_L g)>=(L/4)*(mass f+mass g), lambdaStar(n)=1+1/n.
The threshold is independent of source derivatives, phases and mass ratio.
Its dependency-closed paper proof moves quadrature derivatives onto the
fixed cutoff. Unlike the earlier cosine family, this needs COMPLEX
quadrature and the cross Fourier density. Lean remains OPEN.

The tempting global lambdaStar completion is FALSE: corpus theorem
`not_weilPositiveFull_of_nonneg_semiprime_floor` applies with p=2,c=1.
Exact scratch application and standard-only axiom audit PASS60.53s, exit0.
This is REDISCOVERED, not a new obstruction. The positive MC6 survivor must
be formalized before closing `weil-work-01-pbap-global-pole-grid.md`.
Latest successful obstruction search: partial=false,68,814 indexed files;
background refresh and compiler metadata pending, all candidate/argument/
ingredient outputs inspected and the decisive theorem source checked.

Next implementation: source-uniform Fourier/Gamma budget, complex BV/FTC
quadrature and Abel transfer, growing-order band gluing, exact two-profile
pole/atom identity and literal null transfer. Existing quadrature theorem:
`HTGeometry.norm_rightEndpoint_riemannSum_sub_integral_le_eVariationOn`
in `HTGeometry/BoundedVariationRiemannSum.lean`; source inspected.
Latest index EXIT0 (15.91s); lint EXIT1 (17.70s) lists five unrelated
HTGeometry reachability errors and no owned WP01 finding. Full PBAP OPEN.

MC7 now extends the paper survivor to r arbitrary source windows in [0,D],
successive starts at least 6 log D apart, each width
b D log log D exp(-D/2). It gives Q_lambdaStar>=D/5 times actual mass,
uniformly in r (up to order D/log D). Keep the unique extreme pair for
MC6; all other cross terms together cost O((log log D)/D) times mass.
Every pair is accounted for. Verdict BRIDGE from MC6, novelty unestablished;
not arbitrary many-window positivity. Complete MC6 Lean first.

MC8 improves MC7 by using geometric row sums: spacing 4 log log log D
already suffices, since the total shorter-interaction cost becomes
O(D/log log D) times mass, independently of window count. The paper proof
keeps the D/5 margin and allows order D/log log log D windows. Classified
BRIDGE from MC6 plus the classical Schur bound. This is the strongest
paper survivor recorded on the no-go card; MC6 then MC8 need Lean closure.

`WeilWorkPBAPJointSourceBudget.lean` now proves the exact interval-width
Cauchy--Schwarz bound, pointwise Fourier-square budget, integrable log-deficit
cost and one/two-source Gamma floors. Targeted88.71s, final direct54.16s
empty and eight standard-only axiom checks12.91s all pass; import wired.
SHA256719e958d2a8b0c61801b2e43d60239374dce7b0f2f27875a658730cc9f2db96a.
Compact-support inference caused the earlier timeout; an explicit support
proof removed it without any heartbeat increase.
`WeilWorkPBAPJointLogQuadrature.lean` is complete: targeted87.11s, final
direct80.17s empty, seven standard-only axiom checks6.64s. Import wired.
SHA256f20797bd05d04901187efdb75fe151459c84c135e10cbc0a4bd6cb36928f70f0.
It proves the complex finite-node quadrature, exact positive-logarithm
substitution and actual cutoff Abel-variation bound. Six new supporting
leaves now have 39 public theorem audits. No MC6/MC8 capstone is claimed.
Latest index PASS16.29s; lint EXIT1 21.60s, eight unrelated reachability
errors (three other RHTower leaves plus the five HTGeometry baseline
leaves), no WP01 finding. All owned audit handles have exited.

Next exact cutoff: psi(y)=RHTower.plateauBump 4 (y+2), using the constructor
already checked in ConstrainedWeilPlateauProfile.lean:30--95. Do not use
its odd plateauProfile. Prove fixed derivative bounds for psi and the
normalized cosh family, then discharge actual integer endpoints and the
uniform growing-order phase bands. The paper supplies the literal choice
b=1/(8 log2), since 2<=integral psi<=4. No cutoff-existence premise remains.

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

### Spectral audits and a direct full-energy successor

- Nine-declaration axiom audit: exit 0, only `propext`, `Classical.choice`, `Quot.sound`. Final direct source audit: exit 0, no diagnostics. Final source hash `64190369ffaf22352f991b3dccb17fa381a2d176`. Index refresh reported no generated Markdown changes. Latest lint reports nine unrelated umbrella-reachability errors, recorded in `EVIDENCE.md`; no owned PBAP leaf flagged.
- Divisor-overlap search finished (`partial=false`, 68,364 files); candidate lemmas and source arguments inspected. No applicable box count supplied. This obligation remains live; no box leaf or placeholder has been added.
- Anti-theatre/anti-laziness answers posted: no significant scientific novelty or PBAP sign advance; scalarization and small-support candidates were rediscoveries; formal infrastructure alone does not move the sign frontier; no hard step was skipped for effort; corpus machinery was searched. Changed next cycle to attack actual full energy rather than accumulate further measure interfaces.
- Direct sign audit rechecked L259, L260, L353 and the literal signed polar form. Pointwise absolute bounds still discard the phase coherence and encounter the known square-root-versus-logarithm loss. They are not a new route.
- New exact successor in `results/01-pbap/PACKET-ENERGY.md`: arbitrary coefficients in the literal narrow integer packet family obey full-energy lower bound `m*S*((1/2)*log(1+N*L/4)-10-(2/L)*sqrt(1+log N))` for `N>=1`, `L>=105`. Paper proof is dependency-closed using the existing mean-value constant 104, the literal bump width, gamma lower bound, and both pole moments. No null constraint is assumed. This identifies a diverging energy cost in the torus realization itself; it does not prove general PBAP.
- Scientific verdict **BRIDGE**: L353 and classical Montgomery–Vaughan already supply the spreading mechanism. The exact unrestricted packet inequality needs formal verification; no novelty claim. Deep searches for it and its parents were partial; candidate and source-argument fields inspected. `/tmp/wp01-energy-names.lean` is checking the applicable names and gamma normalization before the next implementation cycle.
- Next formal objective: prove the whole displayed packet energy inequality, retaining arbitrary signs and both poles. Outstanding torus density/Jensen tasks remain recorded and unretired. Ultimate goal remains unconditional full `PrimeBlindPositive` and its compiled existence consequence.

- Final successor scratch `/tmp/wp01-energy-names.lean` passed, exit 0 with no diagnostics. Both the gamma lower bound and the two-sided constant-208 Dirichlet mean-square bound are proved there. The full energy statement remains paper-only. Fixed explicit Lebesgue-measure inference and pointwise function-power normalization; no heartbeat adjustment. All owned processes exited, final spectral hash unchanged, owned diff check clean, generated indexes have no tracked diff. Continue with actual packet Fourier factorization and low-frequency mass; do not repeat already passed spectral audits without a source change.

## Continuation — full narrow-packet energy

- Previous turn classified **progress**. hgtl7 applied again; spectral source hash unchanged; mission remains unconditional full PBAP, not merely this restricted family.
- Refreshed deep corpus search completed with `partial=false`, 68,370 files. Candidate lemmas and source arguments inspected; broad semantic hits did not close the actual packet bound. Source search found existing `HTGeometry.sq_integral_mul_le`, suitable for the literal bump's L1/L2 estimate.
- Paper proof and its external Montgomery–Vaughan parent audited again. Verdict remains **BRIDGE**, no established scientific novelty. Unlike a positivity premise, the estimate retains arbitrary coefficients and explicitly pays both signed poles.
- Plan: verify Fourier, reindexing, and integral Cauchy–Schwarz interfaces in scratch; implement actual packet mass and Fourier factorization; prove low-frequency mass, signed pole bound, and gamma assembly; run targeted leaf, direct-source, axiom and lint audits, then wire completed leaves. No umbrella/full builds. Density/Jensen obligations remain live.

### Packet Fourier estimate compiled

- New `WeilWorkPBAPPacketFourier.lean` proves actual packet mass, centered Fourier factorization, complex-argument bump envelope, symmetric mean-square estimate, and the coefficient-uniform bound `integral_{-NL}^{NL} |fhat|^2 <= 2*m*S` for every `N` and `L>=104`. No null or energy-sign premise enters. The slightly sharper threshold is already justified by the paper's arithmetic (`L+104<=2L`); it is not a new scientific claim.
- Targeted `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPPacketFourier`: exit 0, requested leaf built, dependencies replayed. Final direct-source/axiom audits and umbrella wiring remain pending. No full or umbrella build.
- Fixed compact-integral measure inference, explicit Fourier-sum arguments, natural-number casts, and a sum-reindexing elaboration issue. No heartbeat changes. `/tmp/wp01-packet-energy.lean` now checks the actual gamma lower bound via nonnegative spectral tails; full signed pole estimate remains outstanding.
- All five anti-theatre and four anti-laziness answers posted in chat: no established scientific novelty or full PBAP sign advance; no difficulty-based skip; direct energy control replaces further measure interfaces this cycle.

### Full narrow-packet energy verified

- `WeilWorkPBAPPacketEnergy.lean` proves the exact full energy lower bound, both signed poles included, for arbitrary coefficients and `L>=104`. `gramPacket_log_energy_lower` gives mass times `(1/4)*log N-11`; `gramPacket_uniform_energy_escape` gives a single packet-count threshold for every coefficient choice and every `L>=104` at each target energy per unit mass. No null, spectral positivity, or missing analytic estimate is assumed.
- Targeted `--old` builds of both new leaves: exit 0. Final direct `lake env lean` audits of each source: exit 0, empty logs. Twenty-declaration axiom audit: exit 0, only `propext`, `Classical.choice`, `Quot.sound`. Hashes: Fourier `f9729fc75387de461016b8844e655beea0de413e`; Energy `344ffe13b9c97068b3a3aa96adf0608c5f3ca03e`. Both imports added to `RHTower.lean`; no umbrella build.
- Index refresh passed; no tracked generated-index Markdown diff. Lint reports ten unrelated umbrella-reachability errors, listed in `EVIDENCE.md`; no owned PBAP leaf flagged. No heartbeat changes, computations, commits, or pushes.
- Analytic WP01 status: **CONDITIONAL ADVANCE** restricted to the literal narrow packet family. Scientific verdict remains **BRIDGE** to classical mean-value theory; no established novelty or full PBAP solution. The classical parent was checked against Montgomery–Vaughan's original 1974 paper as well as Montgomery's survey.
- New overlapping-support search returned `partial=true`, 68,389 indexed files. Candidate lemmas and source arguments inspected; unsigned-support disjointness needs nonnegativity absent in the signed PBAP cone. Broad retrieval did not close the extension. Do not infer absence from partial results.
- Next cycle must attack the signed pole-versus-gamma comparison for broad overlapping tests, or expose a precise obstruction. Avoid another narrow-family corollary or a reduction that merely rephrases PBAP. Revisit L259/L353's phase-loss obstruction and seek a comparison preserving signed phase information. Existing torus density/Jensen obligations remain live and unretired; weak torus convergence alone still cannot control full energy. Ultimate goal stays unconditional full `PrimeBlindPositive` and its compiled existence consequence.

## Continuation — signed comparison and failed absolute bounds

- Previous turn remains **progress**, not PBAP completion. hgtl7 applied again. Architecture/testing documents absent; relevant Serena memory read; existing packet-energy hash unchanged.
- Plan: audit stronger signed-comparison conjectures against actual null tests; record exact failures and positive survivors; select an unclosed mechanism from the corpus; complete its paper proof before adding Lean. No new Lean file, build, or changed declaration yet.
- Candidate A: every nonnegative finite full-null mixture satisfies `Gamma(c) >= |Pole(c)|`. Verdict **FALSE**. Existing `integral_normSq_paperFT_fejerTest_mul_arch_neg` gives a smooth test supported in `[-17/50,17/50]`, whose autocorrelation vanishes at every `log n`, `n>=2`, but whose gamma energy is negative. Absolute pole value is nonnegative. This is an existing witness, not a new PBAP counterexample. Positive survivor: gamma negativity can require compensation by the *positive* signed pole; phase-insensitive domination cannot prove full PBAP. Already established in the corpus; no duplicate Lean wrapper.
- Candidate B: `|Pole(c)| <= C*mass(c)` uniformly on the full-null cone. L239/L244 already discuss its failure via Gamma-free duality and Bohr's uniform-convergence theorem. The available Lean theorem assumes absolute convergence on every line `sigma>1`; general producer bounds initially give only `sigma>3/2`. The recorded Bohr repair is paper-only. Do not silently treat its stronger producer conclusion as Lean-proved or add a summability premise.
- Current searches: signed-core refresh `partial=false` (68,394 files); absolute-pole search `partial=true` (68,395 files); bounded-datum search `partial=false` (68,402 files). Candidate lemmas and source arguments inspected. The latter broad search did not supply the missing Bohr bridge. All three commands exited.
- External audit checked Zhu v2 (arXiv:2608.24827), Connes–Consani (arXiv:2006.13771), the AIM Weil formula, and Kolountzakis–Revesz Turan/pointwise extremal papers (math/0204086, math/0312218, math/0302193). Support/packing extremals do not themselves settle the signed logarithmic-null cone. No computation or numerical experiment performed.
- L396–L401 warn that Gram sampling inherits the two-cluster core, GY certificates can hide zero-sensitive bounds, and the near-null/sampling issue is critical. These are research notes with explicitly labelled gaps; do not promote sketches or dimension heuristics to facts.

### Exact successor — critical gamma coefficient

- **Conjecture C (not proved):** for every real `alpha` with `0 <= alpha < 1` and every real `C`, there exists an actual nonnegative finite smooth integer-null mixture `c` with `alpha*Gamma(c) + Pole(c) + C*mass(c) < 0`. Both poles retain weight one. This asserts necessity of the full gamma coefficient, not sufficiency/PBAP.
- First attack: scale a hypothetical positive completion by `1/alpha`. Its polar tests should obey the already sharp multiplicative Toeplitz/log-density ceiling, while its Herglotz continuation has pole residue `1/alpha`. A residue above one should contradict that ceiling. `alpha=0` is the previously recorded bounded-datum branch.
- `[OPEN CORE]`: prove the density-ceiling-to-residue transfer for signed coefficients with only the producer's available absolute convergence half-plane. Do not assume a PNT, eventual coefficient positivity, or convergence down to `sigma>1`.
- Proposed transfer: subtract the finite-sum ceiling to obtain an eventually nonnegative cumulative function; its Laplace transform equals a combination of the continued Dirichlet series times zeta and an explicit rational pole. Landau's theorem may force convergence up to the boundary and preserve the upper bound there. This is presently a proof plan, not a closed argument.
- The exact conjecture is being audited against corpus and current external sources. No Lean implementation until the full argument (including generic datum/slack duality) closes.

### Critical coefficient paper closure

- The earlier `[OPEN CORE]` is superseded by `results/01-pbap/CRITICAL-SLOPE.md`. Current `WeilPrimitiveSetMeanSquare` already proves absolute convergence on every `Re s>1` for ordinary positive data; L244's weaker convergence statement is stale. The modified-datum extension remains a formal obligation.
- Dependency-closed proposed argument: variable-coefficient polar resonators give the sharp Toeplitz ceiling; primitive-set vectors give actual absolute convergence; positivity bounds every translate of a fixed small autocorrelation; its one-sided Laplace identity forces the actual Dirichlet residue to equal the pole weight; Abel summation of the harmonic density ceiling bounds that residue by the gamma coefficient. Thus pole weight greater than gamma coefficient forces a negative full-null mixture, even after any mass slack.
- No Bohr continuation, coefficient-sign, spectral-measure, or summability assumption is inserted. The endpoint with equal weights remains unsolved. Verdict **SURVIVES PRELIMINARY ATTACK** for the precise universal boundary; scientific novelty is unestablished. Booker/Oliver positive L-data results require extra coefficient/discrete-spectrum axioms absent from this cone; not applicable as a shortcut.
- Remaining searches closed: critical-slope `partial=true`, positive-Laplace `partial=false`, positive-distribution `partial=false`; all candidate/source-argument arrays inspected. Exact lexical search confirms the existing summability theorem. The broad searches do not establish absence of an equivalent result.
- Formalization begins with the unconditional sharp gamma upper bound and exact mass/sample identities of the existing smooth polar resonator, extracted without a positivity premise. Then generic datum duality, primitive bounds, translated positivity/residue, and final negative null witness. This is one ongoing theorem proof, not a completed PBAP claim.

### Critical formal dependencies in progress

- `WeilWorkPBAPCriticalResonator.lean`: targeted `--old` leaf build passed. Proves actual smooth polar profile's positive mass, exact physical/Fourier mass, every integer sample, vanishing of both poles, and gamma upper bound with leading coefficient exactly one. No positivity assumption. Final direct-source/axiom audit and wiring pending.
- `WeilWorkPBAPCriticalDatum.lean`: targeted `--old` leaf build passed. Defines literal gamma/pole/mass datum on smooth compact tests; generic null-cone duality produces arbitrary real coefficients; their exact resonator pairing gives Toeplitz slope `a` and constant `a*K0+C`. Intermediate completion hypotheses are discharged by the null-cone alternative in the planned final obstruction; they are not claimed as unconditional PBAP producers.
- `WeilWorkPBAPCriticalCoefficients.lean` and `WeilWorkPBAPCriticalKernel.lean` are ongoing implementations, not yet compiled. Their roles are respectively actual absolute convergence plus the sharp harmonic ceiling, and actual translated Gram positivity plus boundedness. No final critical-coefficient theorem or PBAP proof yet.
- All nine hgtl7 self-audit answers posted: novelty unestablished, stale-note rediscovery corrected, endpoint untouched, no difficulty-based omission, finish the whole negative-mixture result before claiming a research advance. Exact external search also found arXiv:2607.24830v3 (Sep 28, 2026); its abstract describes numerical/operator spectral laws, not the arbitrary modified-null-mixture theorem. No numerical computation used here.

### Continuation — signed Laplace bridge

- Previous goal turn classified **progress**. hgtl7 workflow continues on the same paper-closed critical-slope theorem; full PBAP remains the goal and remains unproved.
- Targeted `--old` builds now passed for `CriticalCoefficients`, `CriticalKernel`, `CriticalWindow`, and `CriticalLaplace`, in addition to Resonator and Datum. The Laplace leaf proves the actual signed series identity and the quantitative remainder `M/sigma`. Final direct-source/axiom audits and umbrella wiring remain pending.
- Residue, generic signed Abel/Fubini, and arithmetic density-Laplace leaves are written and undergoing verification. Do not treat them, or the final negative-null-mixture theorem, as proved yet.
- Latest cumulative-Laplace corpus search: `partial=false`, 68,434 inventoried files; refresh incomplete because background indexer is running. Candidate lemmas, source arguments and ingredient proposals inspected. No complete applicable transfer supplied. Generic improper exponential/Gamma integrals and absolute-series Fubini are the checked parents.
- One procedural error was caught: a leaf build briefly overlapped an unfinished scratch name audit. The owned leaf build was terminated by its exact PIDs and exit 143 verified before proceeding. Subsequent audits/builds are sequential. No other agent process was touched.

- `CriticalResidue` targeted build passed: actual completion forces actual real Dirichlet residue equal to pole weight. Two redundant tactics removed afterward; final audit pending. `CriticalAbel` is now the sole owned running build. Density transfer and final boundary/normalized-witness proofs are written but unverified.
- All nine hgtl7 answers posted again this continuation: novelty unestablished; the fixed-datum absolute-convergence rediscovery was corrected; classical machinery is not the research claim; full PBAP is still open; signed cancellation at equal weights remains the central issue; no effort-based omission; finish this boundary then return to the endpoint; corpus coverage/freshness explicitly recorded.

### Abel transfer verification

- `WeilWorkPBAPCriticalAbel` passed targeted build. Its imports were reduced to Mathlib analysis; it proves signed cumulative-series Fubini and transfers a nonnegative quadratic upper envelope without imposing signs on the signed cumulative function. Two unused simp arguments remain for cleanup.
- `CriticalDensityLaplace` is the sole active build, latest command `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalDensityLaplace`, log `/tmp/wp01-critical-density-build.log`. Last failure was an `if`-condition rewrite with a dependent Decidable instance; replaced by `simp only`. Other proved components in that file must not be treated as audited until the whole source passes.
- `CriticalBoundary` now contains the final completion-residue comparison, negative full-null smooth mixture, mass-zero exclusion, and normalized energy-unboundedness proofs. It has not been compiled yet. No producer hypothesis remains in the intended exported negative-witness statement.
- Next sequence: finish DensityLaplace; clean/rebuild Residue and Abel; compile Boundary; final direct source audits for all ten new leaves; `/tmp/wp01-critical-axioms.lean`; wire imports; index/lint; update result/evidence/memory. Only then claim this necessary coefficient boundary. Full PBAP at equal coefficients remains unproved, and the goal remains active.

- DensityLaplace passed its targeted build (238s), including the exact signed pair transform, finite cumulative identity, and sharp Dirichlet-product ceiling. Cleaned Abel rebuilt successfully without diagnostics; cleaned Residue rebuilt successfully (63s). Boundary is now the sole owned running build.
- Exact current `PrimeBlindPositive` lexical search returned seven hits, no coverage/partial metadata, empty candidate/source-argument arrays. Source signatures confirm the full criterion is still an equivalence and its named producer still assumes RH; the similarly named other criterion is polar. This search did not supply an unconditional full producer. A fresh deep endpoint-mechanism search is running independently of the boundary compilation.

### Critical boundary targeted build closed

- Boundary's first build failed solely on elaboration heartbeats in the mass-zero integral lemma. Explicitly typed continuity, compact-support composition and nonzero value fixed the proof; no heartbeat option changed. `lake build --old +GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalBoundary` now exits 0 (81s leaf elaboration).
- All ten critical leaves have passed targeted builds. Direct `lake env lean <leaf>` final audits are now running sequentially, followed by the 22-declaration `/tmp` axiom audit. Ten imports wired in `RHTower.lean` per user's explicit requirement; no umbrella build.
- Finite-part deep search closed with `partial=true`, inventory 68,456/68,456, refresh incomplete/background indexer. Candidate lemmas, source arguments and proposed ingredient sets inspected; no endpoint producer supplied. Broad OR lexical query was too imprecise (89,757 hits); exact PBAP lexical search returned 210 indexed items, including our unfinished/new sources. Neither search is proof of absence or proof of compilation.
- Read current corpus audit `weil-cone-pbap-lean-audit-2026-10-07.md`: confirms full PBAP existence and general detection remain distinct open tasks in its checked corpus. Equal-weight residue matching cannot determine literal zero mass slack; next cycle must retain finite signed terms.

### Next endpoint attack — exact two-cluster cross term

- Candidate D (OPEN, existing core sharpened to its exact functional): let real smooth `beta` be supported in `[0,W]`, `0<W<log 2`, and let `L>2W`. Set `psi=beta*tilde(beta)` and require `psi(log n-L)=0` for every `n>=2`. For the literal full archimedean-plus-pole Hermitian form `B`, conjecture `|Re B(beta, translate L beta)| <= B(beta,beta)`. This makes every real two-cluster combination nonnegative. Both cross-pole terms stay present; no asymptotic `O(...)` is discarded. It is a substantive subclass of the PBAP endpoint, not a new name for a solved theorem or a claim to solve the full cone.
- Nonemptiness must be retained: for `exp L` noninteger, a sufficiently narrow nonzero smooth beta inside `[0,W]` has autocorrelation support smaller than its distance to the finitely many shifted logarithmic nodes near zero. Broad profiles with cancellation, not these narrow witnesses, are the target.
- Prior corpus checked: L371/L372 already identify the conductor/Pitt mechanism and its first-order interpolation failure; L375/L378 already state the two-cluster reduction; L376 explicitly kills uniform log-lattice flattening through overlapping high aliases. L353 explains phase loss under frequency splitting. These are parents/obstructions, not new discoveries in this cycle. Several stronger heuristic conclusions in those notes are not kernel-proved and are not adopted.
- Next proof attempt: exact joint shifted-node constraints, preserving their phases, against the full cross term. No new Lean until this inequality or a genuine counterexample/positive survivor has a dependency-closed paper proof. A reduced scalar sup-norm quadrature estimate would repeat L376 and is not the intended input.
- Current external check: Connes–Consani–Moscovici, arXiv:2310.18423v2, supplies semilocal prolate/Sonin structure; its abstract does not assert this exact inequality. Beckner math/0701939 and the new Giacchi–Oliveira–Tierney arXiv:2609.34946 (2026-09-28) are adjacent sharp-error/metaplectic Pitt references, not supplied proofs of the integer-null constraint. No numerical work used.

- Two-cluster deep search completed `partial=false`, inventory 68,464 files; refresh still incomplete/background indexer and compiler metadata mostly unverified. Candidate/source arrays inspected. Retrieved `ccmRestrictedWeil_groundShift_cauchySchwarz` pays Cauchy-Schwarz only after subtracting the actual aperture ground energy. For disjoint cluster vectors it bounds the unshifted cross term by a diagonal containing that unknown ground correction. Removing the correction would require its sign, so this is not an unconditional proof of Candidate D. Other proposed deviation bounds assume an existing full-positive producer. Do not import either missing sign/existence premise.
- Pitt search completed with partial results and coverage pending; it supplied no closed constrained endpoint estimate. Exact L371/L372/L375/L376/L378 source notes, not search heuristics, determine the current mathematical obstruction.

### hgtl7 self-audit after the boundary build

All nine answers posted in chat: (1) scientific novelty unestablished; (2) existing summability rediscovered, stale note corrected; (3) classical proof machinery and formalization do not alone establish novelty; (4) necessary coefficient boundary compiled, PBAP endpoint still open; (5) residue asymptotics erase mass slack, so signed finite terms remain; (6) exact obstruction produced, assigned problem unsolved; (7) no effort-based skipped step; (8) next attack is the actual two-cluster cross term rather than another narrow-packet corollary; (9) corpus and current primary sources checked with partial coverage/freshness recorded. Ultimate goal remains active. Final verification is completing before the current result is promoted to fully audited status.

- External correction to L371's motivation: Beckner's [math/0701939v6, Section 2/Theorem 4](https://arxiv.org/html/math/0701939v6) explicitly derives nonattainment of logarithmic uncertainty and an exact deficit identity. Thus its Gaussian-extremal claim is not usable. The conductor identification may still be valid, but a Gaussian-separation proof needs replacement by control of the actual deficit. This is a source correction, not a new theorem or a retirement of Candidate D.

### Critical coefficient final audit complete

- All ten final `lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPCritical<suffix>.lean` source audits exited 0 with no diagnostics. The 22-declaration `/tmp` axiom audit exited 0; only `propext`, `Classical.choice`, and `Quot.sound` occur. Ten source SHA-256 hashes were unchanged through the audit and are preserved in `EVIDENCE.md`.
- `RESULT.md`, `PROOF.md`, `CRITICAL-SLOPE.md` and `EVIDENCE.md` now record the fully formalized strict-coefficient obstruction and quantitative analytic survivor. The scoped failed-route card is `../5-failed/weil-pbap-subcritical-gamma-domination.md`; only that domination mechanism is retired. WP01 remains OPEN.
- Ten imports are wired; index refresh passed; current global lint failed only on nine unrelated unreachable modules, preserved verbatim in evidence. No full/umbrella build, numerical experiment, heartbeat increase, commit or push. All owned Lean and search commands have exited.
- Next active mathematical target is Candidate D above: the exact two-cluster signed cross bound with all shifted integer-node constraints. No closing paper proof exists yet. Do not replace it by the ground-shift Cauchy-Schwarz correction, a Gaussian-extremal argument, uniform-comb quadrature, or spectral phase loss. Continue hgtl7 from this actual open core.

### Current cycle — exact joint constraints and phase cost

Plan: refresh corpus and primary sources; attack Candidate D with all shifted-node constraints; close the next paper statement before adding Lean; audit any survivor and return to the actual energy inequality.

- Current deep search `/tmp/wp01-current-two-cluster-search.json` completed with `partial=false`, 68,468 inventoried/indexed files, background refresh incomplete and source-only compiler metadata. Its candidates/source arguments were mostly unrelated. Restricted Weil follow-up `/tmp/wp01-joint-weil-search.json` returned partial results: autocorrelation bounds and producer-conditional rigidity, no endpoint inequality. Exhaustive `rg` and direct reads located L375–L379 and L349–L370.
- A proposed critical-Toeplitz saturation shortcut is **REDISCOVERED and insufficient**: L57's own correction already gives the unconditional Schur/Mertens bound for von Mangoldt. Its leading ceiling is not a positivity certificate. Do not formalize this as new research or infer full positivity from the critical residue.
- C351's older reduction from arbitrary dilation-free measurable supports to two intervals is not adopted: bounds on individual interval-component widths do not by themselves control sums over all components. The recorded short-window numerical values also are not available under this task's no-computation rule. Candidate D remains open.
- Next exact conjecture (D1): for `L=(log p)/2`, prime `p>=17`, and any fixed nonzero real smooth profile beta supported in `[0,W]`, `0<W<log 2`, every weight `0<theta<1/2` can be retained on the unmodulated profile while finitely many arbitrarily high cosine/sine modulations cancel **all** shifted nodes `log n-L` jointly. Their two-cluster differences then give actual finite smooth integer-null mixtures on the same broad support. No positive energy or gamma budget is asserted. First paper obligation: exact positive finite interpolation, not approximate Kronecker cancellation.
- Mechanism under audit: the relevant integers satisfy `2<=n<p`; none uses prime p. On the torus of their prime factors plus `log p/2`, setting the p coordinate to -1 and other coordinates to 1 makes every shifted character -1. Distinct shifted characters are neither equal nor inverse (inverse would force `nm=p`). Their cosine coordinates have zero Haar mean and nondegenerate covariance, so zero is interior to their convex hull. For `theta<1/2`, the required constant negative vector is interior. Dense positive tails of the real phase orbit should then give an **exact** finite positive representation. The quantitative height/cost of that representation is deliberately unpaid; it is the prospective input needed for Candidate D, not supplied by density.

- D1 paper is now closed in `results/01-pbap/JOINT-PHASE-COST.md`: exact joint phase weights exist for every total correction mass `M>1`; `M=1` is the unattained infimum. The fixed-profile smooth-mixture extension and explicit high-frequency gamma/pole audit are included. This is a **BRIDGE**, with scientific novelty unestablished. Arbitrarily high corrections force energy upwards, so Kronecker exactness supplies no PBAP proof or counterexample.
- `/tmp/wp01-joint-cosine.lean` passed Lean with no diagnostics. It proves generic finite-cosine negative-tail escape, zero-interior convexity, and exact weights from a limiting all-negative phase. Promoted unchanged proof to `WeilWorkPBAPJointConvex.lean`; targeted build in progress. Actual prime-shifted frequencies, strict mass threshold, and smooth-mixture realization still require formal verification; do not count them as corpus theorems yet.

- Stronger D1 survivor paper-closed: for fixed p and nonzero fixed profile beta, exact correction mass M decreasing to one forces correction frequencies to leave every bounded interval in weight. The explicit compact-band bound is `sum_{|t_j|<=H} w_j <= 2(M-1)/d_H`, where `d_H=min_{[-H,H]}(2+cos(a_2 t)+cos(a_3 t))>0`. Literal full energy consequently tends uniformly to positive infinity, including after mass normalization. This is stronger than choosing high frequencies ourselves; it is still a classical compactness/coercivity **BRIDGE**, with Lean pending and D2 still open away from M=1.
- New deep search `/tmp/wp01-phase-energy-escape-search.json`: `partial=false`, inventory 68,488, older coverage snapshot, incomplete background refresh, mostly pending compiler metadata. All candidate/source-argument statements inspected; retrieved phase identities and unrelated coercive estimates, no applicable endpoint theorem. Broader OR lexical retry returned 15,280 mixed hits and no candidate/source arrays; it is too broad to establish absence. Current primary-source audit includes Kunis arXiv:2608.11915v1, whose full-band Haar quadrature bounds do not directly price the sparse shifted-character constraints.

- `WeilWorkPBAPJointConvex` targeted `--old` build passed (129s); `WeilWorkPBAPJointPhase` targeted build passed. Both are wired into `RHTower.lean`; final direct-source/axiom audits are pending. `joint_phase_correction_iff` gives the complete finite-phase mass classification for every prime p>=5, with arbitrary lower frequency threshold. Zero coefficients are allowed in this formal statement; the paper's strict-positive/cardinality refinement and actual smooth realization are not yet exported Lean capstones. The phase bound p>=5 was sent back to the paper audit; p>=17 remains necessary only for its stated uniform support separation.
- Next scratch proof is the stronger phase-forced logarithmic cost divergence as M approaches 1. It uses the explicit two-phase defect and compactness, with no generic coercivity premise in the exported logarithmic-cost theorem. Full gamma/pole realization still awaits formalization.
- The optimized phase proof passed `/tmp/wp01-joint-phase-light.lean`: it now imports elementary prime-factorization machinery directly instead of the spectral-mixture measure module. Its doubled arithmetic exponent is built directly from `primeExponentVector`; all exported statements are unchanged. Rebuilding that leaf, then auditing the corrected logarithmic-cost scratch, sequentially in one foreground command. No heartbeat settings changed.

### Continuation — sharp joint phase boundary

Previous goal turn: **progress**. Current source confirms two new phase leaves; logarithmic-cost scratch audit exited zero. Full PBAP remains OPEN. Continue hgtl7 from the paper-closed phase boundary and its stronger coercive survivor; no alternate success condition.

The last strict-positive/Caratheodory scratch audit handle was missing on continuation and no matching process remained. Its completion result was unavailable, so rerunning that exact audit with an owned log before using the strengthening. One foreground Lean process only. Plan: finish exact positive/cardinality interface; promote and directly audit logarithmic cost; realize actual smooth integer-null mixtures; formalize literal energy transfer; resume D2 away from the mass-one boundary.
- Promoted the already scratch-verified logarithmic-cost proof to `WeilWorkPBAPJointEscape.lean` (targeted build/final audit pending). It proves a universal delta-for-every-cost lower bound over all finite exact correction systems, not just existence of expensive examples. Exported theorem prices the actual function `log(2+abs t)`; no unproved coercivity premise is introduced.
- Smooth realization search `/tmp/wp01-joint-smooth-search.json` returned `partial=false`, 68,495 inventoried/indexed files, background refresh incomplete and source-only/pending compiler metadata. All candidate/source statements inspected. Useful actual parents are finite translated autocorrelation and real autocorrelation integral identities; no complete joint smooth realization was supplied. Building the explicit cosine/sine and translated-test algebra in `/tmp/wp01-joint-profiles.lean` before claiming a smooth-mixture result.
- Active-node audit: full `2<=n<p` phase equations are stronger than actual nullness when the base autocorrelation vanishes at some shifted nodes. Do not infer the two-node escape bound for all actual null modulation families from inactive n=2,3 constraints. Paper now proves rational independence of any two distinct shifted nodes with positive n,m<p: the p-coordinate forces equal integer coefficients, then injectivity of log forces both zero. Thus compact escape extends to any two active nodes. Formal generalization pending. Singleton cancellation can attain M=1, so the pair condition matters.
- Strict-positive/Caratheodory scratch audit rerun exited 0 without diagnostics. `JointConvex` now exports exact positive weights with at most k+1 nodes, and derives the previous nonnegative interface as a wrapper. Sequential foreground verification now rebuilds this leaf, audits the arbitrary-two-active-node phase strengthening, then audits the explicit smooth-profile algebra.

- Continuation audit: arbitrary distinct positive shifted nodes below p now exclude a common negative endpoint phase in Lean; strict-positive correction with at most p−1 atoms also scratch-verified. Promoted JointPhase; targeted build followed by generalized two-node escape audit running. Smooth cosine/sine profile scratch exposed coercion, smoothness-order and missing-import proof errors; repair remains in scratch. No PBAP claim.

- Active-real null search: partial=false, 68,516 files inventoried; refresh incomplete (background indexer), compiler metadata mostly pending/source-only. All 20 candidate statements and all 20 source-argument statements inspected; no generated ideas or ingredient sets. Existing real symmetric `logValue` confirms that complex-profile active nodes must use Re autocorrelation. Added exact paper identity/equivalence before formalization. Profile algebra scratch now has only explicit smoothness/coercion obligations under repair; generalized JointEscape scratch passed, source promoted and wired.

- JointProfiles scratch exits 0 with empty diagnostics after replacing inference-heavy smoothness proofs by explicit real trigonometric composition and the exact finite-order inclusion. Promoted and wired. JointEscape targeted `--old` build exits 0 (97s). JointProfiles targeted build followed by exact all-integer null/mass scratch audit now running, sequential foreground only. Final direct-source audits still pending.

- Energy-coercivity deep search: partial=false, 68,519 files; background refresh incomplete; candidate/source statements and full ingredient set inspected. Most hits irrelevant. Proposed fixed-point-support composition does not concern function support and is rejected. Useful exact source: CompactTestTransform.exists_testTransform_decay; for current interface the already imported Zeta23.norm_paperFT_le and norm_paperFT_mul_sq_le give uniform strip bounds directly. A follow-up lexical OR search was broad (101,922 hits, no coverage fields) and is not evidence of absence. Targeted source reads confirm translation FT and autocorrelation cosine-moment identities.

- Final direct JointConvex/JointPhase/JointEscape source audits all exit 0, empty logs. Seventeen named axiom checks exit 0, standard axioms only. JointProfiles targeted build exits 0 (246s). Actual null/mass scratch has one finite real-sum rewrite failure, repaired in scratch; rerun followed by final JointProfiles direct audit is running. Added a quantitative literal-energy paper bridge e(T)>=m log(2+|T|)-C, deriving low-frequency mass decay from the corpus second-derivative transform bound and retaining a uniform bound on both poles. Formalization pending; D2 away M=1 remains open.

- Exact JointNull scratch now exits 0, empty diagnostics; final direct JointProfiles source audit also exits 0, empty log. Promoted and wired JointNull. Its targeted build is followed sequentially by the actual real-active null equivalence/escape scratch and new exact Fourier modulation scratch. Corrected paper statement to p>=5 throughout: support uses L>W, not L>2W. Main goal remains active and unsolved.

- JointNull targeted `--old` build exits 0 (192s). Real-active null identity and equivalence scratch statements elaborated successfully; final escape wrapper hit a Lean parser ambiguity in tightly spaced `0<m`, repaired using explicit `show 0 < m`. Sequential chain now audits repaired active interface, Fourier formulas, final JointNull source and 19 realization axiom statements. Fourier/low-band analytic scratch prepared from the paper proof; no new energy theorem promoted.

- Analytic follow-through scratch inventory (unverified, not promoted): `/tmp/wp01-joint-fourier.lean` derives exact cosine/sine Fourier shifts and the common two-cluster multiplier; `/tmp/wp01-joint-lowband-body.txt` bounds central-band density by 64 B^2/T^4 with B=integral |beta double-prime|; `/tmp/wp01-joint-mass-body.txt` extracts exact paired mass and positive base mass. These are components of the closed paper coercivity estimate, not new assumptions or completed energy results. Retain this status through compaction.

- Repaired actual real-active interface scratch passes (empty log; sequential chain advanced to Fourier scratch). Promoted/wired JointActive. Its targeted build, final direct-source audit and four-declaration axiom audit remain pending. Exact real-null equivalence and actual-null logarithmic escape are now scratch-verified, without requiring complex-nullness or equations at inactive nodes.

- Global formal lint exits 1 on nine unrelated umbrella-reachability errors; exact names in EVIDENCE. No Joint-leaf error. Fourier scratch had one explicit-function mismatch in integral_sub, repaired by typing translated integrand before rewriting; first cosine/sine and norm-pair formulas elaborated. While Active targeted build runs, appended the pointwise central-band bound to the not-yet-started Fourier scratch so the later sequential audit checks the complete analytic leaf. Current chain: Active build; final Null and Active direct audits; 19 realization plus 4 active axiom checks; expanded Fourier scratch.

- Active targeted build exits 0 (338s). Final direct Null and Active source audits both passed (chain advanced to realization axiom process); axiom chain still running. Additional unverified scratch `/tmp/wp01-joint-density-body.txt` plans integrable actual pair density, exact Plancherel mass and inverse-cubic central-band mass bound. Not promoted. Paper now keeps the sharp pole translation-factor scale O(p^(1/4)) instead of an avoidable O(p^(1/2)) bound; uniform phase-height lower cost as p varies remains open.

- Six-leaf milestone complete: JointConvex/Phase/Escape/Profiles/Null/Active targeted builds and all final direct audits passed; all 40 axiom checks standard only; source hashes persisted in EVIDENCE and /tmp/wp01-joint-source-manifest.json. Index exits 0 and scoped diff check passes. Current sequential process has advanced to expanded Fourier scratch. Global lint remains red on the nine unrelated listed reachability errors. This is research progress, not full PBAP closure or a scientific novelty claim.

- New strengthening selected and paper-closed after corpus audit: retain full paired mass to prove Gamma(pair,T)>=2m log(2+|T|)-2m(10+log4)-4J, where J is the base normalized Fourier log moment. Pointwise log triangle inequality handles both translated Fourier squares; keep exact interference in main mass and bound it only in error. J integrability follows from existing integrable gamma-weighted Fourier square plus gamma lower bound. Both poles retain explicit O(p^(1/4)) lower bound. No energy sign or novelty claim. Search /tmp/wp01-joint-sharp-coercivity-search.json: partial=false, 68,536 files, refresh background incomplete; all 20 candidate and all 20 source-argument statements inspected, no ideas/ingredients. No exact full-PBAP bound found among these hits. Next analytic formalization should prefer this full-mass argument; low-band estimate remains an independent concentration result.

- Expanded Fourier scratch passes, empty diagnostics: exact complex-argument cosine/sine shifts, cluster multiplier, paired Fourier square, pointwise real bound, and inverse-quartic central density bound. Promoted/wired JointFourier. Starting targeted --old build, final direct-source audit and seven-declaration axiom audit sequentially. Actual full-mass gamma-plus-both-poles lower bound remains paper-only.

- Next-stage scratch assembled but NOT RUN: `/tmp/wp01-joint-coercivity.lean` imports the forthcoming verified JointFourier plus JointNull/CriticalKernel/PacketEnergy, then combines mass, actual density, low-band integral and log-moment helpers. Bodies are also saved separately in `/tmp/wp01-joint-mass-body.txt`, `/tmp/wp01-joint-density-body.txt`, `/tmp/wp01-joint-logmoment-body.txt`. The log moment should be proved integrable directly from the actual gamma-weighted square, then integrate the full-mass pointwise inequality from the paper. Current owned Lean chain is only JointFourier production build/final audit/seven axiom checks; do not start another before it exits.

- JointFourier targeted build exits 0 (245s); final direct-source audit running, then seven axiom checks. Updated index exits 0 and includes exact Fourier-density/central-band capstones. New lint snapshot has seven unrelated reachability errors (EVIDENCE lists names), no Joint error. No further source changes to audited six-leaf milestone.

- **Turn classification: progress.** Seven Joint leaves fully audited and wired; 47 named axiom checks standard only; earlier six source hashes unchanged, seventh hash in EVIDENCE. Owned Lean/build chain exited 0, no owned Lean process left running. Index passed; latest global lint has seven unrelated reachability errors. Full PBAP remains open and goal ACTIVE. Next conjecture/paper refinement to formalize is the full-mass gamma lower bound with finite base log moment and both signed poles; `/tmp/wp01-joint-coercivity.lean` is assembled but NOT RUN. Do not count that scratch or paper energy theorem as Lean-complete. Scientific novelty of the completed classical-mechanism bridges remains unestablished.

## Continuation — literal full-mass energy coercivity

Previous turn classification: **progress** (seven source-audited Joint leaves, 47 standard-axiom checks). Current-state validation: all seven source hashes match saved manifest; no owned Lean process was live; architecture/testing docs still absent. Main mission remains unconditional full PBAP and its compiled existence-equivalence application. Applying hgtl7 throughout.

Plan: (1) refresh internal/external statement audit; (2) check exact paired mass, log-moment integrability and actual gamma integral; (3) integrate full-mass logarithmic inequality and retain both signed poles; (4) transfer to actual real-null and normalized energy escape; (5) audit/wire finished leaves, reassess D2 and the full-mixture extension. First scratch audit `/tmp/wp01-joint-coercivity.lean` running in foreground. Full PBAP remains OPEN; no narrower completion criterion is adopted.

- Current-turn contextual audit: hybrid search `/tmp/wp01-coercivity-turn-frontier-search.json` completed, partial=false, 68,537 inventoried/indexed files; background refresh incomplete, compiler metadata mostly pending/source-only, semantic coverage unmeasured. All 20 candidate and all 20 source-argument statements inspected; no generated ideas/ingredients. These hits do not discharge current coercivity or PBAP. Rephrased a deep search around actual-null full energy. External primary audit: Laptev–Weth logarithmic-Laplacian quadratic forms are classical ancestry; Connes–Consani 2006.13771 treats the single archimedean place; Chen–Chen–Hauer 2602.06581v5 (30 September 2026) has a fractional-logarithmic symbol, not our actual gamma-plus-poles null cone. Classification BRIDGE, no literature novelty claimed. Nine hgtl7 self-audit answers posted.
- First mass/log-moment scratch audit verified paired physical/Fourier mass and low-band integral; failed only in logarithm name and explicit coercion normalization. Repaired scratch rerun remains owned and live; no module promoted yet. Full-mass pointwise and integrated gamma proof prepared separately in `/tmp/wp01-joint-gamma-body.txt`, not yet audited. Both poles and actual-null energy escape still pending in Lean.
- Rephrased deep search `/tmp/wp01-full-null-energy-search.json` completed: partial=false, 68,541 indexed/inventoried files, refresh incomplete/background, semantic coverage unmeasured. All 20 candidate and 20 source statements plus the full ingredient set inspected. Suggested kernel-positive-definiteness route leaves quadratic-form positivity as an obligation: not an unconditional PBAP proof, reject as a discharge of the core. Current hypothesis-free analytic parents remain the actual gamma integrability and exact Fourier identities. Expanded coercivity scratch verified the full-mass pointwise lower inequality and physical weighted-L1 pole estimates; explicit integral/function normal forms and pole scalar rewrites repaired, rerun in progress. Full mixture and actual-null normalized energy transfer prepared in separate scratch bodies, not claimed as audited.
- Expanded scratch now includes literal pair energy, finite-mixture lower bound, exact physical mass and actual real-null normalized energy escape. The two-active-node hypotheses internally force a nonzero base; there is no extra nonzero-profile or energy-coercivity assumption. Latest run reported only two gamma-assembly errors (bundled-function coercion in integral_add; polynomial normalization of exact mass). Both repaired explicitly. Pole and actual-null transfer declarations generated no further errors, but no completion claim is made until the whole scratch passes. Next substantive research target remains simultaneous-node quantitative height/energy control away from M=1, with p/profile dependence retained.
- Complete expanded coercivity scratch exits 0 with EMPTY diagnostics. Promoted and wired three leaves: JointCoercivity (exact physical/Fourier mass, low-band concentration, finite base logarithmic moment, full-mass gamma bound); JointEnergy (both signed poles, explicit nonnegative cost, literal pair and finite-mixture energy bound); JointEnergyEscape (exact mixture physical mass, actual real-null energy escape and normalized escape under two real-active nodes). No energy-coercivity or nonzero-profile premise is inserted into the escape capstones. Sequential targeted --old builds, final direct-source audits and 24 named axiom checks are now running via `/tmp/wp01-joint-energy-audit.sh`. Full PBAP remains OPEN; D2 away M=1 and arbitrary-mixture extension remain unresolved.
- Simultaneous-height deep search `/tmp/wp01-joint-height-frontier-search.json`: partial=false, 68,550 indexed/inventoried files, refresh background incomplete; all candidate/source statements and ingredient set inspected. DiscreteRecurrenceDirichletBound supplies an UPPER recurrence-time bound, not the needed lower cost. LiClockThetaReciprocalDegreeTilt's compLog coefficient recurrence is not simultaneous shifted-node Diophantine control. Reject the proposed ingredient chain for this target. A new corpus query asks about actual integer-dilation null geometry before selecting the next conjecture.
- Post-promotion index exits 0 and scoped diff check passes. Current formal lint exits 1 on ten unrelated reachability errors, enumerated in EVIDENCE; no Joint leaf flagged. Sequential production audit remains live. No full or umbrella build, no numerical experiment, no heartbeat override.
- Integer-dilation deep search `/tmp/wp01-null-dilation-frontier-search.json`: partial=true (semantic_retrieval unfinished), 68,554 indexed/inventoried files; refresh background incomplete. All 20 candidate/source statements and ingredient set inspected. Norm-preserving abstract Julia dilation plus gamma parity decomposition does not identify the actual integer-null form or prove its positivity. No absence claim. Current Fourier factor exposes another extension limitation: every fixed-L cluster mixture has common spectral zeros, including at zero frequency, while short-supported nonnegative integer-null tests need not. Recorded as a scope check in the paper, not a new scientific claim or a substitute for the full-cone proof.
- **Completed analytic checkpoint (8 October 2026):** JointCoercivity/JointEnergy/JointEnergyEscape targeted builds pass (71s/149s/41s); all three final direct-source audits have empty diagnostics; all 24 named axiom checks standard only. Sequential owned audit chain exits 0. Prior seven source hashes unchanged; manifest now contains ten audited leaves and hashes are recorded in EVIDENCE. Ten Joint leaves, 71 named checks total. Index passed; current global lint has ten unrelated reachability errors; scoped diff checks pass.
- Turn classification: **progress**, BRIDGE. Literal full-energy and normalized escape close the mass-one boundary diagnostic, with actual real nullness and two real-active nodes. Full PBAP remains OPEN and goal ACTIVE. Next loop must attack simultaneous-node energy control away from M=1, preserve p/profile dependence and account for the common spectral-zero restriction before any full-cone extension. Upper recurrence bounds, abstract norm-preserving dilations and a positive-definite-kernel premise do not discharge this core. Latest searches and rejected ingredient chains are logged above. No unfinished production source or live owned Lean job remains.

## Continuation — full null-cone energy beyond the mass-one boundary

Previous turn: **progress**, three analytic leaves fully audited. Current-state check confirms all ten saved source hashes unchanged; architecture/testing docs absent. Main mission: prove unconditional full PrimeBlindPositive and compile its existing existence-equivalence application. hgtl7 workflow continues. Plan: refresh exact PBAP and full-energy corpus; audit the sharp next conjecture against current primary literature; attack competing mechanisms before selecting a proof; formalize only a dependency-closed survivor; retain all aggregate real null constraints and both poles.

- Current frontier audit: full-energy search `/tmp/wp01-20261008-full-energy-frontier.json` is complete, 68,565 inventoried/indexed files, refresh incomplete and mostly source-only/pending compiler metadata. Every candidate/source statement and ingredient set inspected. Proposed full-energy chain assumes the unpaid sign; positive mixture coefficients are not positive energy. GY search `/tmp/wp01-20261008-gy-frontier.json` is partial (semantic deadline), same coverage snapshot; every candidate/source statement and ingredient set inspected, generated Hawking-resonance chain irrelevant. No absence claim.
- Read later GY mentions through L405, including L398's correction of L385. Neither opposing sketch is a formal theorem. External audit read Goldston–Yıldırım I, Lemma 2.1/(2.14), and Bettin–Gonek 1604.02740: coprimality uniformity and length/height quantifiers are essential. Bare complex-pole Fourier cancellation contradicts L398's frozen-coefficient Lorentzian step; it does not disprove L398's intended full-window conclusion. Exact positive survivor and closed paper proof in `GY-CAUSALITY-AUDIT.md`; Lean verification pending. BRIDGE/correction, no novelty claim; GY not retired.
- Resolvent deep search `/tmp/wp01-resolvent-frontier.json`: complete, 68,567 indexed files, refresh incomplete; every candidate/source statement and ingredient set inspected. Direct source search found the exact stronger parent `perron_kernel_identity`; reuse it rather than reproving contour integration. Mass-slack search `/tmp/wp01-mass-slack-frontier.json`: complete, 68,575 files, refresh incomplete; all candidate/source statements and ingredient set inspected. Near-radical Weil tests and matched exposing-ray tests do not assert integer-nullness. The proposed chain's prime-entry cancellation is not established by its referenced lemmas.
- New competing critical-endpoint conjectures: (S0) for every epsilon>0 there is an actual smooth nonnegative integer-null mixture of physical mass one with full energy<epsilon; (S+) some epsilon>0 is a universal full-energy/mass lower bound on that cone. These are exact incompatible alternatives, not added premises. S0 is the constant-weight case of the prior L401 sharpness program, so the statement itself is REDISCOVERED; a new proof mechanism is required. S0 alone would not prove nonnegative energy. Open core: construct null near-minimizers while retaining the finite critical energy, or derive a strict uniform lower bound; subcritical residue matching cannot decide either. Conductor/extended-Selberg classification cannot be applied without first deriving its analytic/divisor hypotheses.
- Conductor/margin deep search `/tmp/wp01-critical-margin-conductor.json`: partial (semantic deadline), 68,575 indexed/inventoried files, refresh incomplete. All 20 candidate and 20 source statements and the complete ingredient set inspected. Generic shifted-arcsine margins and onset bounds do not concern PBAP; reject the proposed chain. Dixit's extended-Selberg uniqueness theorem has additional analytic/class assumptions and positive Dirichlet coefficients, unavailable for a general real PBAP completion. Nine hgtl7 self-audit answers posted; no significant scientific advance claimed.

### Continuation — recover GY audit, then critical energy

The prior targeted MollifierCausality build passed; final audit handles and temporary logs were unavailable on continuation, with no owned processes remaining. Reran final source and seven axiom audits: both exit 0, source diagnostics empty, standard axioms only. Source hash and exact declarations recorded in EVIDENCE; import already wired. Index passed; global lint fails on thirteen unrelated unreachable modules, listed in EVIDENCE. The completed result is a classical one-sided Fourier bridge correcting one proof step, not a significant new PBAP theorem. Full PBAP remains OPEN and goal ACTIVE.

Critical-cone deep search complete (`partial=false`, 68,586 files, incomplete background refresh/source-only compiler metadata); every candidate/source statement and ingredient set inspected. Generic energy compactness, prime first-trace nullness and the polar ground-state theorem do not prove compactness or positivity on the actual aggregate integer-null cone. Do not turn an atomic-minimizer reduction into a claimed energy certificate. Next corpus query targets actual log-lattice sampling and full energy, preserving both poles.

- Null-energy Weil search `/tmp/wp01-null-energy-weil-20261008.json` complete (`partial=false`, 68,587 files); every candidate/source statement and ingredient set inspected. The exposing-ray completion identity preserves a prescribed nonzero trace; neither it nor the autocorrelation/Fourier identity supplies the null-cone sign. Exact `LogLatticePoissonAnticoncentration.norm_integral_le_of_vanish_logLattice` retains a square-root height weight; replacing it by a logarithmic energy weight is an additional theorem, not an application.
- Smooth-extension search `/tmp/wp01-smooth-extension-20261008.json` complete (`partial=false`, 68,589 files), refresh incomplete/source-only metadata. All candidate/source statements and ingredient set inspected. Its proposed step “Ensure null repair energy zero” is false: repair annihilates the defect, and only bounds the energy change. The smooth-to-C2 extension already has a dependency-closed paper argument in PROOF; it is not new scientific knowledge. No new approximation leaf is started.
- Next hostile test: three-cluster shifted phases can obey `a+b=c`. If nonnegative correction weights satisfy `sum w*cos(t*a)=sum w*cos(t*b)=sum w*cos(t*(a+b))=-1`, then `sum w>=2`, by `|1+exp(i*t*a)+exp(-i*t*b)|^2>=0`. At equality every used frequency makes an equilateral triangle, so irrational a/b excludes finite attainment. This is a classical Gram/simplex constraint, not a new PBAP sign theorem. It warns that independent pairwise repairs lose the multi-cluster compatibility. Current search audits whether the corpus already covers its exact arithmetic realization before any further conjecture or Lean work.

- Three-cluster search `/tmp/wp01-three-cluster-20261008.json` complete (`partial=false`, 68,593 files), refresh incomplete/source-only compiler metadata. All candidate/source statements and ingredient set inspected. The proposed chain uses the natural-number distance triangle inequality and a cosine identity; it does not prove a simultaneous phase or energy estimate. The Gram threshold above is an elementary compatibility check, not a significant scientific advance or a retired PBAP route.
- New precise critical-energy conjecture D2-CERT is recorded at the end of JOINT-PHASE-COST: the actual pair energy e(T) admits a finite cosine minorant using only real-active shifted nodes. Evaluating at zero automatically pays the seed normalization; actual null constraints then pay every finite correction exactly. Only this sufficient paper implication is established. Constructing coefficients with an all-height signed bound remains OPEN CORE; no such bound is introduced as a Lean premise. The known coercive floor has an inadmissible constant term; ordinary quadrature still leaves the L380/C383 high-height error.
- Current primary-source check: Suzuki arXiv:2606.09096v2 (August 2026) treats localized Weil forms and their operator/compactness structure. It supplies no integer-null full-energy certificate. Literature and corpus novelty for the current elementary reductions is not claimed.
- Nine hgtl7 answers posted: no significant new scientific theorem; smooth extension rediscovered and not reimplemented; classical pole correction fully verified; PBAP energy frontier unchanged; simultaneous height-sensitive cancellation is central; triangle compatibility does not pay energy; no effort-based deferral; necessary audit recovery finished and explicit energy certificate targeted; corpus/current primary source checked. Continue with D2-CERT's actual coefficient construction and all-height error, not another compactness or simplex lemma.
- All owned source/axiom/index/lint/search commands from this turn have exited. Mollifier source final hash unchanged. Goal remains ACTIVE; no unconditional full PBAP or completion sequence has been produced.

## Current cycle — actual energy certificate and jump-kernel audit

Previous turn: progress, final MollifierCausality audits completed; source hash unchanged on current-state inspection. Architecture/testing docs absent. Mission remains full unconditional PrimeBlindPositive and compiled completion equivalence. Continue hgtl7. Plan: inspect actual energy kernel; attack D2-CERT constructions without inserting the desired minorant as a premise; audit any positive survivor before Lean.

- Exact lexical PrimeBlindPositive search and exhaustive source-text check still locate only the target definitions, duality equivalences and the RH-dependent sufficient theorem, with no unconditional full target theorem. Full PBAP remains OPEN.
- Energy-kernel deep search complete (`partial=false`, 68,597 files), refresh incomplete/compiler metadata mostly pending/source-only. All candidate/source statements and full ingredient set inspected. The actual cosine/sine Fourier and correlation identities are applicable; a modulation phase-recovery clock supplies neither the seed normalization nor a nonnegative full-energy residual.
- Jump-certificate deep search partial (`partial=true`, same 68,597 snapshot), refresh incomplete. All candidate/source statements and ingredient set inspected. PositiveJumpDatum includes positivity/integrability as data; it does not construct those properties for the actual PBAP source. The existing ArchimedeanWeilKernelSign proves the full pole-plus-gamma jump weight changes sign. Do not discard that signed part.
- Hostile test of a proposed jump-square certificate: if the residual `e(T)-sum d_n*cos(a_n*T)` had a nonnegative Levy jump representation, uniqueness would require its nonzero discrete jump coefficients to be nonnegative. At negative seed energy the zero-frequency normalization instead requires sum d_n<0. This is a classical Fourier/Lévy uniqueness diagnostic, not yet a fully verified actual-source no-go: the exact signed continuum representation, integrability and negative-seed specialization must first be closed. General D2-CERT does not require conditional negative definiteness and is not refuted.
- Primary-source check: Gao, *A Probabilistic Characterization of Negative Definite Functions*, equation (5.3), https://pmc.ncbi.nlm.nih.gov/articles/PMC7604715/, gives the classical unique nonnegative Levy representation. Thus invoking this mechanism is not scientific novelty. Newly located Zhu preprint arXiv:2608.24827 concerns finite compact windows; no all-aperture PBAP conclusion is inferred from its abstract.

- Bibliographic correction after opening full HTML: arXiv:2608.24827v1 lists Marcus Chuk, not Zhu. Its finite-window reduction retains a leading-block positivity check and its broad-window upper bound assumes RH. Neither supplies an all-aperture null-cone sign. Numerical results are not adopted or reproduced.
- Multiplicative-Hilbert search complete (`partial=false`, 68,599 files), refresh incomplete. All candidate/source statements and ingredient set inspected. Generic Hilbert moment positivity does not identify the PBAP form; reject that chain. Cosine-dual-attainment search partial (`partial=true`, 68,606 files), refresh incomplete, source/compiler metadata mostly pending. All 20 candidate and 20 source statements plus ingredient set inspected. Its centered-cosine/strict-certificate chain does not prove the actual sign. Direct reads locate the existing Riesz-extension machinery, so no duplicate duality wrapper is selected.
- Exact lexical actual-head Gamma search: 31 hits, 4 displayed under the module cap, no coverage object; all displayed entries inspected. The source `CCMActualHeadGammaAutocorrelationEnergy` proves actual complex-L2 Binet--Plancherel. New outgoing-quantile characteristic formulas and signed-moment Gamma bounds retain an unsigned scalar/remainder and do not close PBAP.
- Selected positive survivor: for L>2W, actual paired modulation energy has increment integral K_L(y)*Re autocorr(beta)(y)*(1-cos(Ty)), with explicit strictly positive K_L. Thus profiles with nonnegative real autocorrelation minimize this energy at T=0. Full paper derivation/ancestry in JOINT-PHASE-COST; Lean verification pending. Baseline may be negative, so this is not PBAP. The stronger Levy-residual classification is still under audit; no route retired. Formalize literal energy identity before relying on its sign restriction.
- Nine hgtl7 self-audit answers posted. No significant scientific novelty or PBAP sign claimed. Scratch `/tmp/wp01-joint-kernel.lean` now verifies literal Gamma jump integrability/normalization and positivity of the proposed weight; the latest audit had only two pole-identity rewrite errors, now repaired. Added scaled-variable Gamma identities for the forthcoming separated-cluster integral. Current scratch audit running; no new production module or umbrella import. Remaining capstone is the actual paired-energy increment, then its nonnegative-real-autocorrelation minimum theorem. Do not count the isolated positive kernel as that capstone.
- Subsequent scratch audit exits 0 with empty diagnostics through both signed poles, scaled Gamma integrability, modulation-defect integrability, actual paired real correlation, paired Gamma jump formula and paired Gamma difference. No source promotion yet. Appended the separated shifted-jump integrability and half-line folding helpers; next scratch audit running. Remaining: instantiate folding with the actual even compact modulation defect, combine exact pole increment, prove actual minimum, optimize/promote/wire, targeted `--old` build, final direct-source and axiom audits. Scratch helper bodies additionally saved under `/tmp/wp01-joint-kernel-*-body.txt`.
- Separated folding scratch advanced: shifted-jump integrability and reflection identity elaborate; actual Gamma increment assembly had a pointwise-function unfolding issue and an Ioi-membership normalization issue, repaired. The same owned scratch now includes the literal two-pole increment and its cosh translation/folding proof; audit running. No production changes or new verified capstone yet. Current formula retains the full signed energy and the profile restriction; it is not an unconditional full-cone sign theorem.
- Full helper scratch now exits 0 with empty diagnostics: folded actual Gamma increment and exact folded two-pole increment both verified. Appended literal full-energy increment, nonnegative-real-autocorrelation minimum, and identification of the zero-modulation seed; capstone scratch audit running. Those new capstones are not yet verified or promoted. Production/final-audit plan unchanged.
- Complete capstone scratch exits 0, empty diagnostics. Promoted as two focused leaves, `WeilWorkPBAPJointJump` and `WeilWorkPBAPJointModulation`, and wired both imports. The second leaf reuses the public conjugate-correlation identity across the module boundary. Sequential guarded audit (`/tmp/wp01-joint-kernel-audit.py`, state JSON alongside) now runs both targeted `--old` builds, both final direct-source audits and 11 named axiom checks. No full/umbrella build. The exact kernel and restricted global-minimum statement are bridges, not an unconditional full-PBAP proof or significant-novelty claim.
- **Completed production checkpoint:** both targeted builds pass (57s/65s), both final direct-source audits pass with empty logs (36s/6s), and all 11 axiom checks are standard-only. Guarded chain exits 0. Source hashes and declarations recorded in EVIDENCE; RESULT and JOINT-PHASE-COST updated. Index exits 0; global lint has seven unrelated reachability errors, listed in EVIDENCE, no new-leaf error. Both new source files are below 500 lines and use default heartbeats.
- Next corpus search `/tmp/wp01-seed-crossing-certificate-20261008.json` completes with `partial=false`, 68,630 files, refresh incomplete/source-only metadata. Every candidate/source statement and ingredient set inspected. Zero-deficit conditional on a positive completion, zero perturbation weights and graph-cluster identities do not construct the desired cosine certificate. New concrete conjecture at the end of JOINT-PHASE-COST: for each sufficiently large prime, an actual scaled nonnegative bump has negative seed energy yet a one-active-node negative cosine minorant at every height. Construct the width crossing, prove active-node existence, strengthen the kernel minimum, and retain uniform coercivity under width perturbation. Do not formalize those missing source facts as hypotheses. No claim that this sector solves full PBAP.
- Turn classification: **progress (verified bridge)**, scientific novelty unestablished. Full PBAP remains OPEN and goal ACTIVE. All owned build/audit/index/lint/search commands have exited; no unfinished new production leaf remains. Continue hgtl7 with the actual seed-crossing conjecture and hostile novelty/parameter audits, or reject it with its positive survivor if the construction fails.

### 8 October 2026 — actual width sector selected

Continued hgtl7 cycle. The tentative zero-crossing route is superseded by an
explicit family beta_W=phi(u/W), W=(int phi^2)/(int phi)^2 * L*exp(-L/2).
`JOINT-WIDTH-SECTOR.md` gives the dependency-closed paper argument for negative
seed E0/m=-L-2log L+O(1), actual active node n=floor(exp L), and all-height
certificate e(T)+(3/2)mL*cos((log n-L)T)>=mL/8. This would imply every actual
real-null correction has full energy >=(L/16)*physical mass, at unbounded
aperture. Proof uses refined full-mass high-frequency Gamma concentration and
decay of BOTH pole transforms; the old logarithmic-moment lower bound is too
lossy under this shrinking width. No computation or positivity assumption.
Scientific novelty unestablished; candidate survives preliminary attack.
Lean implementation is pending; full PBAP remains OPEN.

Plan: (1) finish exact-statement corpus/primary-source attack; (2) formalize
actual high-frequency Gamma and pole estimates; (3) formalize width scaling,
seed asymptotic and integer-node selection; (4) assemble literal certificate
and real-null energy theorem; targeted --old and direct leaf audits throughout.
The sharper alpha/lambda one-node boundary is a subsequent conjecture, not a
proved no-go. No conditional wrapper will substitute for the actual family.

Exact-statement search completed: `/tmp/wp01-negative-seed-sector-20261008.json`,
partial=false, 68,630 inventoried/indexed files, refresh incomplete with mostly
source-only/pending compiler metadata. Inspected all 20 candidate and 20 source
statements plus ingredient set. Proposed kernel/old-energy chain still requires
the width-dependent cost bound; it does not close the sector. Coherent polar
completion and RH-equivalent two-edge statements were inspected directly and
have different quantifiers. First broad dilation search was mostly irrelevant;
module-filtered Gamma search supplied actual Fourier/energy ingredients.

Implementation starts in `/tmp/wp01-high-frequency.lean`; no unfinished
production leaf yet. API scratch required explicit universe levels for three
`have := @...` checks; corrected and passed. Existing complex Fourier second-
derivative decay directly supplies the pole estimate, strengthening the paper
proof without introducing a new analytic assumption.

High-frequency bridge completed: `WeilWorkPBAPJointHighFrequency`, 292 lines,
wired; targeted --old 148.0s and final direct source audit 31.6s passed. Seven
standard-axiom-only declarations audited. The proof retains exact paired mass,
charges actual central Fourier leakage, and proves quartic decay for BOTH
signed poles. Scratch parser ambiguity `|*` and `norm_ofNat` corrected; final
production diagnostics empty. No heartbeat changes. Next scratch
`/tmp/wp01-width-scale.lean` formalizes actual dilation, support, mass,
autocorrelation and second-derivative cost; no unfinished production leaf.
Nine hgtl7 self-audit answers posted. Scientific novelty still unestablished;
full PBAP and the complete width-sector formal theorem remain open.

`WeilWorkPBAPJointScale` completed: all exact dilation identities plus real
nonnegative-profile autocorrelation. Wired; targeted --old 112.3s, final direct
34.8s (empty diagnostics), eleven standard-axiom-only checks 178.9s. Source hash
304cab39320ec541af0bfb592b729de4bb91966e3cc98b7e758167ce56fdfc6c.
The high-frequency source hash is
36ae3f774880b38b7f43ef782e1b7e60405277b8d4131e68f9b583b042f9a037.

Current scratch `/tmp/wp01-seed-log.lean`: fixed integrable Fourier majorant for
Gamma(v/W)+log W, including the logarithmic singularity at v=0. The equivalent
Fourier proof of the seed estimate is appended to JOINT-WIDTH-SECTOR.md. It
retains exact cluster mass and bounds only the remaining Fourier multiplier.
Latest search `/tmp/wp01-width-gamma-asymptotic-20261008.json` complete with
68,652 files, refresh/compiler coverage caveats; all20candidate/all20source and
ingredient statements checked. Proposed partition inputs assume a producer;
they do not supply the required width estimate.

Process slip recorded in EVIDENCE: new scratch command launched <=3.464s before
prior axiom-audit wrapper exited; only one remains active now. Require explicit
exit confirmation before the next Lean launch. No extra production file is
unfinished. Full PBAP and assembled width-sector theorem remain OPEN in Lean.

Seed Gamma bridge closed: `WeilWorkPBAPJointSeedGamma`, wired and audited.
Targeted --old build 25.9s, final direct 5.0s empty, nine standard-axiom-only
checks 4.5s. Uniform in arbitrary cluster separation:
|Gamma(g_W,L)+mass(g_W,L)*log W|<=W*C(phi). Exact source integrability at zero
is proved, not supplied. Hash9001bbe731da8f84d8d409693b170c5bc1204f5bed95e201c076fb1f43b02b50.
Current scratch `/tmp/wp01-seed-pole.lean` derives the exact cluster pole factor,
width-squared scaling and continuous source profile at width zero. Next use
W=kappa*L*exp(-L/2) to prove the actual normalized seed limit; only its limit
is required for the sector, so no stronger remainder estimate is needed in Lean.

Seed pole bridge completed and wired: targeted 40.2s, final direct 5.6s empty,
seven standard-axiom-only checks 5.0s. Hash and exact commands in EVIDENCE.
Current scratch `/tmp/wp01-seed-limit.lean` proves width limits and normalized
pole limit before combining the already audited uniform Gamma remainder.
No owned audit overlap; previous chain explicitly exited before new Lean run.

Nearest-integer source search completed (`partial=false`, 68,669 files;
refresh incomplete/source compiler metadata mostly pending). All20candidate,
all20source statements and ingredient set inspected. Phase identities and
Riemann-kernel decay do not supply positivity at the shrinking active lag;
Herglotz-positive inputs are conditional and rejected as a shortcut. Direct
existing actual-active-null API is available. Simpler uniform high-frequency
exponential error bound appended to JOINT-WIDTH-SECTOR; no logarithmic
monotonicity lemma is needed for the selected sector.

Complete actual seed-limit scratch passes (only two tactic-style warnings,
removed on promotion). `WeilWorkPBAPJointSeedLimit` now wired and in sequential
targeted/direct/axiom audit. Eleven public results include the literal full
energy limit and balanced eventual bound -9mL/8<=E0<0; no energy-sign premise.
Next scratch `/tmp/wp01-width-high.lean` assembles uniform high-frequency
control from actual dilation and the already audited two-pole decay.

SeedLimit audit complete: targeted107.1s, final direct64.5s empty, eleven
standard-axiom-only checks6.1s. Source hash recorded in EVIDENCE. Current
high-width scratch includes both elementary remainder bounds and their exact
exponential normalization; no unfinished production leaf or audit overlap.

Uniform high-frequency width leaf completed, wired, targeted63.0s,
final direct133.4s empty, eight standard-axiom-only checks84.7s. EVIDENCE has
hash and commands. Current `/tmp/wp01-width-phase.lean` audits actual floor-
exponential node, exponentially small lag, real activity from positive mass,
and uniform low-band cosine bound. `/tmp/wp01-width-sector.lean` is prepared
but not run: explicit translated bump and all-height certificate assembly.
No unfinished production leaf. Full PBAP remains open.

Phase scratch now passes with empty diagnostics; `WeilWorkPBAPJointWidthPhase`
wired and sequential audit running (five public declarations). Fixed source
capstone scratch prepared in `/tmp/wp01-width-sector.lean`; actual all-real-null
energy margin body appended. Further prepared body
`/tmp/wp01-width-sector-nonempty-body.txt` specializes to prime half-logarithms
and constructs corrections at every prescribed mass M>1, using the existing
finite simultaneous correction theorem. These capstone parts are not yet Lean
verified. No unconditional PBAP or novelty claim. Next conjecture remains the
alpha/lambda sharp one-node boundary; do not advance it before finishing this
actual-source sector and its nonemptiness audit.

Phase production audit complete: targeted152.7s, final direct31.4s empty,
five standard-axiom-only checks89.5s. Hash in EVIDENCE. Capstone scratch
`/tmp/wp01-width-sector.lean` now running, including explicit unit bump,
all-height certificate, universal real-null energy margin and nonempty prime
sector at every correction mass M>1. Previous audit explicitly exited before
this Lean process. No unfinished production module.

### Completed checkpoint — actual negative-seed sector

`WeilWorkPBAPJointWidthSector` passes targeted --old43.9s, final direct70.2s
(empty), eight standard-axiom-only checks33.5s. Hash
4e7abc165ffb97fb3b4f80b7f5b182e80187beb35f9829f8392d833d2fa55a0f.
All eight new leaves, eight final source audits and 66 named axiom checks
complete; all imports wired. Explicit unit bump has no supplied source-sign,
energy-sign, crossing, active-node or certificate premise. Every real-null
correction has full energy >=L/16 times physical mass; actual positive-mass
corrections exist at each M>1 for every sufficiently large prime half-log.
Full PBAP remains OPEN; goal ACTIVE. Scientific novelty unestablished.

RESULT, JOINT-WIDTH-SECTOR and EVIDENCE updated; earlier crossing proposal
marked historical/superseded. Corrected general support-diameter wording:
between L and L+W, with equality at upper endpoint requiring full source
support. Index exits0, scoped diff-check exits0. Global lint exits1 on five
unrelated HTGeometry reachability errors listed in EVIDENCE; no new-leaf error.
Every owned Lean/build/research/index/lint job has exited. Intermediate scratch
body fragments are being removed; production leaves and audit/search logs are
the authoritative retained record. No commit, push, full build or heartbeat
increase.

Next hgtl7 cycle: audit the sharp one-node width boundary and its positive
survivor, then return to the many-node/full-cone gap. Latest exact mechanism
search `/tmp/wp01-one-node-boundary-20261008.json`: partialfalse68,685files,
refresh incomplete/source-only caveats. All20candidate/all20source, two ideas
and ingredient set inspected; truncated source-head statement read directly.
Conditional RH witnesses/decompositions do not give the actual high-frequency
upper estimate. Candidate exact diagnostic: a one-node certificate forces
E0+e(pi/abs(a))>=0. For width factor alpha and nearest-node rate lambda,
alpha=lambda+1/2 is an UNPROVED critical-boundary failure candidate because
of the -2*m*log L seed correction; prove the actual upper estimate before
asserting failure. No route retired. Do not mistake the completed restricted
sector for a spanning or arbitrary-width theorem.

### Current cycle — exact one-node boundary and its positive survivor

Full-target and deep actual-upper-energy corpus audits completed; all result
sections inspected with source/compiler freshness caveats. Owned research
PID44348 confirmed exited. New first-moment search is session4378, output
`/tmp/wp01-first-moment-20261008.json`; no owned Lean build is running.
The corpus already supplies linear-weight Fourier integrability, avoiding
new derivative/Plancherel infrastructure.

Plan: (1) close and hostile-audit the exact paper statement; (2) formalize
the actual full-mass upper estimate and critical width boundary; (3) formalize
the stronger lambda-dependent positive survivor, audit targeted leaves,
then revisit the many-node/full-cone gap. The complete paper argument is
`JOINT-ONE-NODE-BOUNDARY.md`: alpha*=lambda+1/2 fails by the negative
-2*m*log L correction; every fixed alpha=alpha*-d, 0<d<1, has a positive
all-frequency margin. Both new capstones remain unformalized. Scientific
novelty unestablished; full PBAP OPEN. Do not retire the route based only
on the negative boundary statement.

Three-band paper audit sharpens the survivor: with
alpha=lambda+1/2-d*log(L)/L, d<1 fails the two-point test, whereas d>1
has a positive all-frequency certificate and mass-normalized logarithmic
margin. Use seed minimum only below exp(7L/8), the nonnegative cosine plus
positive energy in the middle band, and the sharp high-frequency bound
above pi/(2*delta). This avoids losing a spurious extra log(L) term.
Full proof added as conjecture C in JOINT-ONE-NODE-BOUNDARY; neither
boundary capstone is yet Lean verified. Current Lean session3209 audits
the actual first-moment Gamma upper bridge in `/tmp/wp01-joint-upper.lean`.

Upper-energy scratch now passes with empty diagnostics. Production
`WeilWorkPBAPJointUpper` copied and wired; targeted/direct/axiom audit not
yet launched, pending exit of its API probe session90232. Six public
theorems preserve exact 2m Gamma coefficient, first-moment dilation
invariance and both signed pole terms. Next prepared scratch is
`/tmp/wp01-pole-bounds.lean`, using the actual autocorrelation integral to
bound the seed pole between its zero-width value and a cosh(width/2)
multiple. No numerical computation or heartbeat increase.

First-moment search completed partial=false68,700files, all20candidate,
all20source and ingredient inspected; suggested derivative identities
unneeded because the existing linear-weight integrability theorem applies.
Three-band search completed partial=true68,705files, all20candidate,
all20source and ingredient inspected. Generic log-width, phase correction
and conditional source identities do not supply the sharp transition.
Refresh incomplete and compiler metadata mostly pending; no absence or
novelty claim follows. Anti-theatre and anti-laziness answers posted in chat:
the upper bridge uses standard analysis; the significant candidate is the
unformalized logarithmic transition, and the full-cone gap remains unpaid.

Upper bridge production audit complete: --old25.4s, final direct6.3s empty,
six standard-axiom-only checks10.6s, API probe189.8s; guarded chain exit0.
Hash b7895a07238b4397cd8ca34181305c40f44271e0cf4e3ef7724d0e56d0cfccc1.
Current sole Lean process is pole scratch session14380. Further prepared
scratch `/tmp/wp01-prime-lag.lean` has not run; it proves prime non-square
separation and 1/(2p)<=abs(actual nearest lag). No unfinished production leaf.

PoleBounds production audit complete and wired: --old240.2s,
final direct64.4s empty, six standard-axiom checks4.9s; guarded chain exit0.
Hash3c093d8a7d5e01b6fd4e4f61e3b196005c7e6344e67c398d6cefbd9df1036119.
Actual profile error is at most B^2*W^2/2, including concrete unit-bump
specialization. Current sole Lean job is seed-expansion scratch session58108,
`/tmp/wp01-seed-expansion.lean`. It combines the new pole error and old
Gamma error before any limit. Prime-lag scratch remains unrun. Two new
production leaves and twelve checks complete; full transition and PBAP OPEN.

Seed expansion first scratch run found a representation-only rewrite mismatch;
explicitly unfolded the constructed test in the already proved energy identity.
Current retry is session41914; do not launch another Lean until it exits.
Prime-lag scratch now also derives L-log2<=log(1/abs(lag))<=2L+log2.
It has not run yet. The explicit quadratic pole remainder is already audited.

Independent preparation for the next full-problem step:
`/tmp/wp01-many-node-cost-20261008.json` completed partial=true, coverage
pending, refresh incomplete. All20candidate/all20source inspected, no proof
ideas/ingredient sets. Quantitative simultaneous recurrence gives upper
hitting-time estimates, not the needed lower logarithmic cost; conditional
Weil-positive moment leaves cannot be used. Next research question is whether
many actual nearby integer-log constraints impose a uniform logarithmic
frequency cost at fixed correction mass, beyond the existing two-node
M-down-to-one escape. No new theorem or selected conjecture is claimed from
this weak search; rephrase/filter before selecting that next route.

Seed expansion scratch now passes empty and production
`WeilWorkPBAPJointSeedExpansion` is copied/wired; sole owned Lean audit is
guarded session3735 (targeted, direct final, three axioms sequentially).
Prime-lag scratch remains next. Filtered many-node-cost research is
session12214, `/tmp/wp01-many-node-filtered-20261008.json`.

Implementation simplification for the pending C capstones: use s=log(1/delta)
and K=L/2+s-d*log L directly, with W=kappa*K*exp(-L/2). This is exactly the
paper width but avoids carrying lambda=s/L through every product. Arithmetic
gives L-log2<=s<=2L+log2; hence eventually1<=K/L<=3 for fixed d. The exact
seed expansion should yield a uniform bounded error for
e0/m+2s-2(d-1)*log L. Explicitly its main remainder is
-2*log(kappa*K/L)+2K*(2exp(-L/2)-exp(-L)), with quadratic pole error
vanishing by W bounds. Certificate coefficient is m*(2s-(d-1)*log L).
Retain the three-band proof already on paper; no abstract seed/Gamma/phase
sign premises in the final explicit-source prime capstones.

Filtered many-node search completed partial=false68,725files, refresh
incomplete/compiler metadata pending. All20candidate/all20source and the
ingredient inspected; the parser-truncated resonator sample was read directly
at CriticalResonator195--200. Results recover the known two-node compactness
minorant, M-down-to-one escape, exact correction existence and fixed-profile
energy lower bound. They provide no uniform p-dependent cost at fixed M.
Keep this distinction explicit when selecting the next conjecture; recurrence
upper bounds and the exact resonator sample identity do not pay the lower cost.

Next analytic assembly caution: `joint_seed_pair_high_normalized_lower`
already specialized the main term to7/4, so it only suffices for C's middle
band. For the final high band start from `joint_dilated_pair_high_simple`
and RETAIN 2*log(T/2); do not infer the 2s coefficient from the7/4 theorem.
The existing explicit inverse-square/quartic errors normalize using
W>=kappa*L*exp(-L/2) and vanish uniformly above exp(7L/8). At
T>=pi/(2delta), log(T/2)>=s-log2. At T*=pi/delta, upper estimate needs only
log(1+T*)<=s+log(1+pi) once delta<=1, and bounded/vanishing error;
no exact high-frequency constant limit is needed for d!=1.

SeedExpansion production audit complete: --old167.8s, final direct174.8s
empty, three standard-axiom checks21.0s, guarded chain exit0; wired.
Hash5c389245b817c5fa085bea989404b239c6cb4f0e2b2c4fe819ea0fedd9f291d3.
Current sole Lean scratch is prime lag session60529. The three new production
leaves and fifteen public checks are complete. Both C capstones remain OPEN.

Prime-lag scratch retries fixed this toolchain's `Nat.le_floor` implication
(not an iff), the explicit cast of1, and distribution before cancellation.
No arithmetic or analytic premise was added. Current sole Lean session5490
runs `/tmp/wp01-prime-lag.lean`; the source stays in scratch until it succeeds.

### Completed checkpoint — upper energy, quantitative seed and arithmetic lag

Prime-lag scratch passed empty and production `WeilWorkPBAPJointPrimeLag`
is wired/audited: --old53.2s, final direct6.8s empty, five standard-axiom
checks6.4s. Hash599f0faa32878bce7826331701650bcb53ed10cdf5034cee81e60676acc4af0b.
All four new leaves and twenty named axiom checks complete. No owned Lean,
build, search, index or lint command remains running. No unfinished production
leaf, numerical computation, full/umbrella build, heartbeat increase or commit.

Index exits0. Global lint exits1 on eight unrelated reachability errors,
listed exactly in EVIDENCE; none of these four leaves is flagged. Scoped
diff-check exits0. Old failed API-probe log is removed; final passing API,
scratch and production audit logs remain for reproducibility. Production
files and EVIDENCE are authoritative. Full PBAP OPEN, goal ACTIVE; scientific
novelty unestablished. The paper conjecture C is still NOT a Lean theorem.

Next exact work: formalize the variable-width uniform estimates with
s=log(1/delta), K=L/2+s-d*log L, W=kappa*K*exp(-L/2), then the three-band
certificate for d>1 and two-point failure for d<1. Pay every bound from the
literal unit bump and the just-compiled prime arithmetic. Uniform analytic
lemmas can quantify over real L and L-log2<=s<=2L+log2, then specialize to
actual prime half-logarithms; no supplied energy or phase-cost premise.
After that, return to the fixed-M many-node cost/full-cone gap recorded above.

### 2026-10-08 — uniform boundary estimates underway

- Full PBAP OPEN. Continue conjecture C from `JOINT-ONE-NODE-BOUNDARY.md`.
- Plan: (1) retain the exact `2 log |T|` coefficient uniformly for all
  `κ L exp(-L/2) ≤ W ≤ 1`; (2) close the uniform seed expansion at
  `W=κ(L/2+s-d log L)exp(-L/2)`; (3) assemble negative two-point obstruction
  and positive three-band survivor; (4) source audits, umbrellas, index/lint.
- Refresh `/tmp/wp01-boundary-frontier-refresh-20261008.json` completed:
  partial=false, 68,730 indexed files, refresh incomplete, compiler coverage
  mostly pending. All 20 candidates, 20 source arguments and ingredient set
  inspected. The suggested spectral-density-to-prime-sector chain does not
  prove full PBAP; it only recovers known sector positivity.
- External primary check: arXiv 2006.13771 (archimedean Sonin comparison),
  2607.02828v3 (finite dictionary/tail certification). Neither inspected abstract
  supplies the missing full-cone producer. No novelty claim from search absence.
- Verdict remains SURVIVES PRELIMINARY ATTACK for C; uniform estimates are BRIDGE.
  Work in `/tmp/wp01-uniform-high.lean`; no new production leaf yet.

- Uniform high-frequency bridge COMPLETE: production
  `WeilWorkPBAPJointUniformHigh`, targeted build 37.0s, final direct audit 7.4s
  (empty), seven standard-only axiom checks 5.1s; all exited0. Import wired.
  SHA256 cf2375c6afe9f44e8f3716b48cc44d93e16bc26daecde93e6927b2ee345573b0.
- Uniform seed draft `/tmp/wp01-boundary-seed.lean` now carries the literal
  source balance, scale interval, explicit vanishing pole error, and bounded
  remainder after centering by `-2s+2(d-1)log L`. It is under Lean audit;
  not yet a production theorem. Full C capstones remain open.

- Uniform seed bridge COMPLETE: `WeilWorkPBAPJointBoundarySeed`, targeted
  build63.2s, final18.3s empty, eight standard-only checks56.6s, chain exit0.
  SHA256 6bf9a1d7dd8b3eb3f2e3deab7d0a9618c41ccc6686b1fccd7dfb0183234d844f.
  Actual-prime capstone derives lag range and width geometry.
- Negative C capstone compiles in scratch: for every d<1 and all sufficiently
  large L, uniformly over the permitted s range, `e(0)+e(pi*exp(s))<0`.
  Hence no real c gives `-c*cos(exp(-s)*T) <= e(T)` globally. Production
  `WeilWorkPBAPJointBoundaryObstruction` is wired and under final sequential
  build/source/axiom audit. This is not a null-mixture counterexample.
- Positive survivor draft `/tmp/wp01-boundary-certificate.lean` is ready for
  its first Lean run after that audit exits. It proves the literal unit-bump
  normalized certificate with margin `(d-1)*log L/2` for d>1, via three bands.
  No retirement until this positive survivor and actual-prime/null transfer
  are formalized. No numerical experiment, full build or new axiom.

- Opposite-phase obstruction COMPLETE: `WeilWorkPBAPJointBoundaryObstruction`,
  targeted160.7s/final25.6s/two axiom checks5.9s, all exit0, final empty.
  SHA256 4c7bea07919b193a412b3023beba162f4bf48a53430d395d2db17e5c47bc0fdf.
- Positive three-band scratch proof has passed once; a diagnostic cleanup
  is being rechecked before production. Margin `(d-1)log L/2` in source-mass
  units, positive coefficient `2s-(d-1)log L`, all real frequencies.
- `/tmp/wp01-boundary-prime.lean` drafts actual-prime phase identity,
  uniform node activity, negative seed, and both actual-prime capstones.
  Not yet compiled. Null-mixture margin and nonemptiness still need transfer.
- Fresh many-node search `/tmp/wp01-many-node-uniform-cost-next-20261008.json`:
  partial=true;68,745 indexed files; reranking deadline; two unfinished
  reformulations; refresh incomplete. All20 candidates/all20 source arguments
  and sole ingredient set inspected. It recovers the existing mass-down-to-one
  two-node escape, not a fixed-M bound growing with p. Proposed ingredient chain
  incorrectly pairs a bounded logarithm estimate with mass-to-one escape;
  it does not pay the missing many-node cost. No new conjecture selected yet.

- Positive C survivor COMPLETE: `WeilWorkPBAPJointBoundaryCertificate`,
  targeted94.1s/final10.2s/one standard-only axiom check4.8s; all exit0,
  final empty. SHA25657846612416c0f8e91464f8758d2444046c4ba92673de1a5d53fd4ad34f14cf8.
- `/tmp/wp01-boundary-prime.lean` passed its first Lean run. Production
  `WeilWorkPBAPJointBoundaryPrime` now wired; targeted build passed29.8s,
  final/axiom audit still running at this checkpoint. It proves actual-prime
  phase identity, uniform node activity, negative seed, and both actual-prime
  boundary capstones. SHA256bba6ce1fb0712a32640444f24fd2b9d6a9d81eabdb54fbf206c6f9752bb825e6.
- `/tmp/wp01-boundary-null.lean` now drafts both final physical-mass margin
  and nonemptiness for every M>1. First Lean run must wait for the owned prime
  audit chain to exit. No other owned process remains running. No route retired.

### Final C checkpoint — 8 October 2026

- `JointBoundaryPrime` final68.2s and six axiom checks146.1s passed; empty final.
- `JointBoundaryNull` targeted156.0s/final158.3s/two axiom checks17.1s passed;
  final empty, standard-only. SHA256
  73afc90b86fcaadf68573dac348304a2f619e2c9dc5e57798b861209a6da8235.
- C COMPLETE for d<1 and d>1. Six production leaves wired, 26 public theorem
  axiom checks, all targeted/final audits pass. Actual prime phase, active
  nearest node, negative seed, full physical-mass margin and nonemptiness at
  every M>1 all paid. No owned Lean/build process remains. d=1 and full PBAP OPEN.
- Next core: many-node phase cost at fixed correction mass as p grows. Existing
  two-node escape is only M down to one at fixed p; do not conflate the limits.
  Candidate under audit: a positive autocorrelation-weighted sum over actual
  logarithmic nodes is asymptotically nonnegative uniformly on each polynomial
  height horizon |T|<=exp(A L). This would force correction log-cost/L to diverge
  at fixed mass cap. It would still not pay the broad-profile exponential pole
  cost. No new Lean code or scientific novelty claim for this candidate yet.
- Fresh searches recovered a general derivative schedule in
  `Sieve/RouteTHybridZetaBlock.lean` and `Sieve/DirichletBlockSigma.lean`.
  Reuse this corpus before rebuilding classical derivative estimates.

### Many-node continuation — 8 October 2026

- New research file `results/01-pbap/JOINT-MANY-NODE-COST.md` records fixed
  actual beta at W=log2/2, exact real-active constraints and correction cost.
- MH1: fixed-mass cost/log(p) diverges. Closed paper proof uses positive
  autocorrelation quadrature through |T|<=N^(1/2), then existing all-order
  Dirichlet block schedule and bounded-variation Abel summation through N^a.
  BRIDGE, not scientific novelty; no new Lean declaration yet.
- MH2: fixed-mass cost/p^(1/4) diverges. Exact, falsifiable, OPEN. Its contrary
  is an exact admissible bounded-cost family at arbitrarily large primes,
  which need not refute PBAP. Proving MH2 would force full normalized energy
  to diverge on the same scale in this fixed-source sector. The paper proves
  that implication with both poles retained, not MH2 itself.
- Quantitative recurrence attack read Maksimova2405.07051v1, Theorems C/1,
  and actual corpus Kronecker/phase construction sources. Available bounds
  are upper recurrence horizons, not the required lower cost. Approximate
  visits do not pay exact-null repair. MH2 survives this preliminary attack.
- All returned 20 candidates/20 source-argument statements and ingredient
  sets inspected for weighted-horizon, height-cost and spectral-atom searches.
  Partial search coverage/deadlines are recorded in the paper. The suggested
  `WeilPositiveFull` spectral-kernel chain would be circular and is rejected.
- Index exits0, six hashes unchanged, scoped/no-index whitespace clean.
  Current global lint exits1 on twelve unrelated umbrella reachability errors;
  no WP01 leaf flagged. Full list in EVIDENCE. Nine hgtl7 answers posted again.
- Plan: attack the full vector MH2 by a cost-sensitive separating polynomial
  or an exact cheap convex construction; close a paper theorem before Lean.
  No numerical experiment, heartbeat raise, full build, commit or push.
