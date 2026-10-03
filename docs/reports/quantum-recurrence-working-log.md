# Static local quantum recurrence: working log

## Objective

Prove the complete same-draw Brown–Susskind growth–plateau–first-circuit-return
law for ordinary fixed-locality, time-independent Hamiltonians, together with
permanent distinguishability of locality from Haar randomness at maximal
complexity. This objective is not complete.

## 2026-09-29: remove an artificial time-union loss

Proof chain: ordinary source measure → return-excised incidence-action bound
→ continuous complete-circuit exclusion → growth, plateau, first return.
The decisive growing-replica incidence-action estimate is still missing.

Previous verified correction: nonzero radial rescaling of target vectors
does not change their replica span or the bare projected pair action.
Target norm suppression must remain in the capture threshold or in an
explicit norm-weighted reporter. See `ReplicaTargetRadialGaugeLaw.lean`.

Corpus investigation found a different avoidable loss:
`PauliReturnExcisedCircuitContinuumLaw.lean` charges a time grid and an energy
cap even though `PauliCommutatorReturnTubeLaw.lean` maps every hitting time
into the same static commutator small-ball set.

Conjecture: the existing incidence-weighted finite-target bound holds for
the union over all real times, without the energy tail or time-grid factor.
Proof: choose a hitting time and target, apply the deterministic commutator
inequality, then apply the already-proven static Gaussian union estimate.
Exact endpoint-image compression is retained. This is a strengthening of
the existing corpus result, not an externally established novelty claim.

Adversarial boundary: the error is energy-normalized; identity and weak
centralizers remain difficult; the complete surviving circuit-image sum
still needs suppression. Low-incidence target excision is not equivalent to
the circuit-budget-dependent initial-time cutoff. No source-fibre coarea
multiplicity has been estimated or discarded by this argument.

Implemented `HTGeometry/PauliAllTimeCircuitExclusionLaw.lean`, wired into
`HTGeometry.lean`. All eight initial theorems passed both scratch verification
and `lake --old env lean` on the integrated source. Three headline axiom
audits cover all helper proofs: only `propext`, `Classical.choice`, `Quot.sound`.
No full or umbrella build, no heartbeat increase, no new oleans required.

Second conjecture tested: removing the time-grid penalty might let the static
incidence certificate handle arbitrarily large occupied circuit images.
The verified boundary disproves that extrapolation: each incidence is at
most the number `m` of two-local Pauli directions, hence the unweighted
incidence partition function is at least `N * exp(-a*m)`, with
`a = gaussianIntervalActivationMass^2 / 2`. Taking the family to be the
occupied endpoint subtype makes `N` the number of distinct endpoints.
This is a lower bound on the certificate, NOT on the actual return probability
and NOT a counterexample to Brown–Susskind. The all-time exclusion estimate
above is the positive result retained from this test. Both new ceiling
theorems passed a separate scratch check and standard-axiom audit. The final
combined-source check, `lake --old env lean
GaloisForLFunctions/HTGeometry/PauliAllTimeCircuitExclusionLaw.lean`, exited 0
without warnings. All owned Lean and search processes terminated normally.

Further corpus inspection found the all-time operator-norm Ward reduction
already in `StaticEvolutionProjectiveWardTrichotomyLaw.lean`. It must not be
rediscovered or called the missing probability bound. The weighted carrier
law in `PauliWeightedCommutatorCarrierLaw.lean` avoids cardinality only for
events with design mass at least a threshold `κ`; one adaptively chosen
captured endpoint does not itself provide that lower bound.

Next live conjecture: source-conditioned growing-replica geometry supplies
enough occupied capture mass after the budget-dependent initial cutoff to
close the incidence-action receiver. This remains unproved. Preserve both
source variables in the return-free square and all fibre-sheet multiplicity.
Do not substitute Haar mixing, norm-rescaling of target spans, or the static
unweighted incidence sum for this missing estimate. A coefficient-energy /
operator-norm transfer is a possible normalization improvement, not yet a
proof of complete-circuit exclusion.

Project lint fails on 15 unrelated unwired RHTower modules at the latest
check. No proof-debt error or wiring error was reported for the new leaf.

Search evidence: hybrid and deep corpus queries inspected declarations,
candidate lemmas and source arguments. Coverage reports unavailable semantic
coverage statistics and some stale compiler metadata; source inspection is
the authority. A deep search confused Hamiltonian dynamics with Hamiltonian
graph paths; those candidates were rejected.

Broad recent literature checks: arXiv:2609.05386 describes determinantal
geometry of iterated 2×2 commutators; arXiv:2609.14585 describes single
commutators in C*-algebras. Neither abstract supplies a lower-tail estimate
for a prescribed random local generator or the surviving circuit image.
No transfer from these papers is claimed.

## 2026-09-29: optimize exclusion-proof elaboration

Maintenance only; the growing-replica incidence-action frontier remains open.
Changed four proof bodies in `PauliReturnExcisedCircuitContinuumLaw.lean`
and `PauliAllTimeCircuitExclusionLaw.lean`, preserving every statement and import.
Restricted constant-sum simplification to explicit lemmas; replaced nonlinear
arithmetic, congruence search and ring normalization with order/associativity
lemmas. Broad simplification had attempted expensive failed typeclass searches
on unitary endpoint subtypes.

Same combined-source scratch, synchronous elaboration and native profiler:

- Continuum exclusion proof value: 51,509,745 → 4,703,540 raw heartbeat ticks.
- All-time return-excised exclusion: 36,505,575 → 3,085,771.
- Combined two dominant proofs: 88,015,320 → 7,789,311, a 91.2% reduction.
- Incidence ceiling: 5,271,834 → 1,144,590.
- Certificate-floor proof now falls below the 1,000,000-tick logging threshold.

These are proof-elaboration counters, not whole-project wall-clock speedups.
The profiler threshold filters output only; no proof heartbeat or recursion
limits were changed. Both integrated sources matched the measured combined
scratch byte-for-byte. Final combined-source `lake --old env lean` audit passed
without warnings. Exactly the four changed proofs were axiom-audited: only
`propext`, `Classical.choice`, `Quot.sound`. Existing umbrella wiring retained;
no builds, new oleans, git operations or agents. Global lint still reports 15
unrelated unwired RHTower modules and no failures for the edited leaves.
Owned Lean/search/lint processes exited; temporary optimization files removed.

## 2026-10-02: return-free near-diagonal coherence test

Full ordinary-ensemble incidence-action producer remains open. Hybrid and deep
corpus searches inspected candidate lemmas, source methods, and ingredient sets.
Coverage metadata lacks semantic statistics; source inspection checked actual
applicability. StaticChoiCentralizerCarrierReplicaLaw and
StaticChoiKurtosisNearActionLaw suppress transverse individual targets but leave
the occupied high-centralizer circuit carrier unpaid. No complete-circuit bound
follows from their conditional receivers.

Conjecture under test: for every spectrum in positive dimension, every replica
order r, cutoff a, and T >= max(1,4|a|), the return-excised full pair purity P is
at least g^2/(16 sqrt(r+1) S T), where g=gaussianFloorTwo and S=staticChoiSpeed.
Public unconditional specialization uses T=1+4|a|+u^2 and dimension n+1.

Dependency-closed mathematical proof: set delta=1/(4 sqrt(r+1) S T).
S,T,sqrt(r+1) >=1 imply 0<delta<=1/4. Restrict outer time x to [3/4,1]
and inner time y to [x-delta,x+delta]. Both times lie above 1/2 and hence
outside [-|a|/T,|a|/T]. Speed gives trace distance <=1/(4 sqrt(r+1)),
so fidelity >=1-1/(16(r+1)). Bernoulli gives fidelity^r >=1-r/(16(r+1))
>=1/2. The shifted Gaussian interval lower bound gives inner mass >=2g delta
and outer mass >=g/4. Positivity, restriction monotonicity and Fubini yield
P >= (1/2)(2g delta)(g/4)=g^2/(16 sqrt(r+1) S T).
No nonresonance, ensemble mixing, lost source sheet, or target assumption enters.

At errors epsn=1/2, epsw=3/4, receiver threshold is
g^2(7/16)^(2r)/(64 S^2 T^2). Since sqrt(r+1)<=r+1<=2^r and
2(7/16)^2<1, the purity lower bound strictly exceeds this threshold for
every r, including r varying with T. This only falsifies full-purity substitution;
it does not falsify actual projected action suppression or Brown--Susskind.

Positive survivor to formalize: actual carrier compression ratio A/P must
satisfy an explicit bound proportional to sqrt(r+1)(7/16)^(2r)/(N S T)
whenever the exact incidence-action receiver succeeds. This is a necessary
quantitative requirement, not a new ordinary-ensemble producer. Short-time
coherence and Bernoulli are known ingredients; no external novelty or Nature
claim is assigned to this diagnostic without a further novelty audit.

Completed formal result: `RHTower/StaticChoiReturnExcisedCoherenceFloorLaw.lean`.
Four public capstones passed in scratch and a warning-free integrated leaf
check with `lake --old env lean ... -o ...olean`. No heartbeat/recursion limit
changes, umbrella builds, full builds, git operations, or subagents.
The scratch axiom audit of all four public theorems reported only `propext`,
`Classical.choice`, and `Quot.sound`. Private helper assumptions are derived
inside the data-only public capstones; no unknown ensemble bound is assumed.
Umbrella import added immediately after StaticChoiCarrierPurityCrowdingLaw.
Only the new leaf olean was generated, reusing cached dependencies.

The positive survivor is an exact diagnostic disjunction for the ACTUAL
projected carrier action and every positive integer capacity N=k+1:
the incidence budget fails OR A/P < sqrt(r+1)(7/16)^(2r)/(4 N S T).
The receiver's incidence number is a natural-valued occupied-subspace rank,
as checked directly in ContinuousCircuitReturnExcisedFirstEntryLaw; the
positive-integer parametrization does not replace it with target cardinality.
Zero occupied rank is the separate trivial no-capture case, not a positive
capacity case claimed by this theorem. The disjunction does NOT prove its
compression branch holds for an ordinary ensemble. Neither this bound nor
the purity obstruction is a new physics discovery or the missing producer.

Lean optimization within the new proof: explicit `change` folds time and the
large incidence integral into local scalar variables before normalization.
Without this, `ring` normalized inside the state/integral expression and
treated syntactically altered integral expressions as distinct atoms. Scoped
normalization fixes the proof; increasing heartbeats would not fix that error.

Current lint exits 1 for 13 unrelated unwired RHTower modules, with no failure
reported for the new leaf or its wiring. All owned searches and Lean/lint
processes exited normally; temporary scratch sources are being removed.

Next hard attack: source-conditioned target leverage after the budget-dependent
cutoff, particularly the high-centralizer occupied carrier. The universal
full-purity shortcut is now rigorously ruled out for the growing-replica
first-entry receiver. Estimate actual projected action rather than discard
projection, insert a Haar assumption, or normalize away source sheets.
Expanded-corpus deep searches returned generic graph-gap and D-optimal-design
receivers, not an applicable ordinary-source suppression producer; partial
coverage metadata prevents interpreting this as exhaustive corpus absence.
Recent broad arXiv search inspected 2609.06981, an open-system Liouvillian
visibility paper; its abstract supplies no closed-static-ensemble transfer.

## 2026-10-02: profile-guided coherence-proof optimization

Maintenance requested by user; no mathematical frontier claim. L7 adversarial
review restricted edits to seven proof bodies in
`RHTower/StaticChoiReturnExcisedCoherenceFloorLaw.lean`. All nine theorem
signatures, definitions, imports and umbrella wiring remain unchanged.
Restricted arithmetic tactics to needed scalar facts; replaced a broad
nonlinear search with linear arithmetic. Replaced carrier-denominator
normalization and commutativity simplification with direct rewrites.

Native synchronous profiler, identical unchanged proof limits:
pointwise coherence helper 21,040,418 -> 7,853,327 raw elaboration ticks
(62.7% reduction). Within the two scratch candidates, direct normalization
reduced relative-compression proof 7,178,348 -> 4,680,436 and direct
commutativity reduced receiver/compression proof 7,110,598 -> 5,865,327.
These are proof-elaboration counters, not whole-project timing claims.
The trace threshold filters logging only; no maxHeartbeats or maxRecDepth
change or workaround was introduced.

Both scratch batches passed. All seven changed proofs axiom-audited in
scratch: only propext, Classical.choice, Quot.sound. Final source matched
verified scratch and warning-free `lake --old env lean` leaf audit generated
only its cached olean. No full builds, umbrella builds, git or subagents.
Lint baseline reports 12 unrelated unreachable RHTower modules; untouched.
Owned Lean, search and lint sessions exited normally. Scratch cleanup follows.
The ordinary-ensemble complete-circuit incidence-action bound remains open.

## 2026-10-02: pair-integrability dependency optimization

Continued the requested proof-performance maintenance in the existing leaf
`RHTower/StaticChoiCarrierPurityCrowdingLaw.lean`. Two proof bodies changed;
all four theorem statements, imports, and existing umbrella wiring unchanged.
Pair integrability now uses direct power-of-one bounds instead of nonlinear
arithmetic, and a single explicit simplification set for continuity. The
pair-crowding proof folds its integral and bound into their existing local
names rather than expanding the state expressions in a redundant rewrite.

Identical native synchronous profiling options and unchanged proof limits:
pair-integrability declaration 7,676,026 -> 5,397,298 raw elaboration ticks
(29.69% reduction); pair-crowding declaration 2,620,635 -> 2,443,671
(6.75%). Unchanged declarations varied by less than 0.7%. These counters do
not establish a whole-project wall-clock speedup. The profiler threshold
filters trace output only; no heartbeat/recursion limit change or wrapper.

Scratch passed, including name verification and axiom audits of only the two
changed declarations: propext, Classical.choice, Quot.sound. Repository source
matched verified scratch exactly after removing its audit commands. Final
`lake --old env lean` leaf check generated only its own cached olean and exited
0 without warnings. No full builds, umbrella builds, dependency builds, git,
or subagents. Lint still exits 1 for the same 12 unrelated unwired RHTower
modules; none in this edit scope. Owned Lean and search sessions terminated
normally. Temporary scratch source removed after validation.

This is verified maintenance, not mathematical frontier progress. The actual
same-draw ordinary-ensemble projected incidence-action producer remains open.

## 2026-10-02: observer-matched transfer-moment attack

Hybrid and deep corpus searches were run for observer-relative moments,
preserved conditional source variance, occupied incidence, and slow covariance
carrier overlap. Coverage exceeded 64,500 files; some searches were partial.
Generated ingredient groups claiming fibre topology proves inverse variance
were rejected as inapplicable. Direct Lean inspection found the existing
Krylov finite-family receivers, one-step scalar-removed innovation identity,
and the complete-continuum incidence receiver. None supplies the ordinary
same-draw suppression estimate needed by that receiver.

Conjecture attack: a fixed-observer Gaussian commutator moment estimate cannot
be transferred unchanged to arbitrary same-source adaptive observers.
The observer exp(-itH) commutes with H. This invalidates that transfer, not the
desired circuit-exclusion theorem. Conditional Wishart inverse variance in
arXiv:2610.00112 requires directions depending on a preserved transpose Gram;
no such preserved-coordinate representation was derived for the physical
static-Hamiltonian circuit carrier. In particular real factors identify the
transpose and Hermitian Gram, so blindly copying its complex fibre variation
is invalid. The new random-circuit results 2610.02100 and 2610.02125 concern
independently refreshed gates, not the requested static ensemble.

Positive deterministic survivor, classified BRIDGE (Cauchy--Schwarz, not a
new physics discovery): define Q=d^-1 sum Delta^2 |Uij|^2 and
R4=d^-1 sum Delta^4 |Uij|^2. Let Moff=d^-1 sum_{i!=j}|Uij|^2.
For every matrix, Q^2<=R4*Moff: apply finite weighted Cauchy to
f=Delta^2*w, g=1_{i!=j}w, h=Delta^4*w, then multiply by d^-2.
No stochastic independence or unitary assumption is needed for this inequality.
R4 is exactly normalized energy of the double spectral commutator and is
invariant under common spectral shifts. For unitary U, row/column sums and
Delta^4<=8(Ei^4+Ej^4) give R4<=16*M4(E-a) for every center a.
The existing diagonal-centralizer estimate gives Moff<=1-beta^2, hence
Q^2/R4<=1-beta^2. Zero R4 uses total division; empty dimension has Q=R4=beta=0.
If R4=0 the Cauchy inequality additionally forces Q^2=0, so
Q^2/(16*M4(E-a))<=Q^2/R4 holds in all cases. Otherwise denominator monotonicity
proves this comparison. Finally beta^(2r)<=(1-Q^2/R4)^r<=exp(-r Q^2/R4),
with the second step justified by 1-b<=exp(-b); the existing near-action
receiver yields the observer-matched replica suppression bound for every r.
This is a dependency-closed proof of the exact pointwise replacement, including
empty dimensions, degenerate/scalar spectra and zero moments. It still needs
an actual source-conditioned circuit-carrier producer, not a new hypothesis.

The transfer-moment scratch now passes all eight declaration axiom audits:
only propext, Classical.choice, Quot.sound. Integrated its checked source as
RHTower/StaticChoiObserverTransferKurtosisLaw.lean and wired its umbrella import;
final leaf/cache check remains pending behind the single owned Lean process.
This closes the deterministic bridge, not the missing quenched estimate.

Important quantifier correction for the next attack: the arbitrary adaptive
observer exp(-itH) defeats a naive individual-observer transfer, but the
complete bounded-circuit carrier itself is fixed in physical coordinates.
Existing returnExcisedReplicaMinimalIncidenceAction_eq_targetAction preserves
the action when replacing the source-dependent occupied carrier by that full
fixed target span, including both source sheets. A fixed physical carrier
basis is therefore admissible before ensemble averaging. This exact identity
is already in the corpus, not a new discovery here. Source dependence of the
evolution and growing-replica covariance suppression remain unresolved.

Requested optimization is being tested separately on the two remaining
proofs in StaticChoiCarrierPurityCrowdingLaw. Matched scratch compares original
proofs with typed shared state/tensor expressions and explicit local instances.
No proof resource limits changed; no full/umbrella builds or other processes
owned by this agent are running concurrently with that check.

Matched synchronous native-profile result: carrier-action declaration
4,111,234 -> 2,686,793 raw elaboration ticks (34.65% reduction).
Its shared typed state/continuity proof and explicit standard local instances
were accepted; theorem statement and dependencies unchanged. Integrability
candidate 3,352,648 -> 3,550,521 (5.90% worse), rejected: its repository proof
remains unchanged. Matched scratch passed and both candidate declarations
had only propext, Classical.choice, Quot.sound. Only the accepted carrier-action
proof was integrated. Final leaf and actual-name axiom audit are pending.
Profiler output threshold is not a proof resource-limit change.

Both final repository leaf checks/cache generations now exit 0 without
warnings. The integrated optimized proof matches the measured accepted body
exactly. New observer-transfer leaf matches checked scratch apart from trailing
blank-line whitespace. Actual repository-name axiom audit of the one changed
carrier-action proof is the only remaining check before scratch cleanup.
Global lint remains blocked by pre-existing unrelated unwired RHTower modules;
neither edited leaf is among the reported errors. No git, subagents, dependency
builds, full builds or umbrella builds used.

Actual-name axiom audit passed: the changed carrier-action declaration uses
only propext, Classical.choice, Quot.sound. All owned Lean/search/lint handles
have exited; temporary scratch files are now being removed. No heartbeat or
recursion budget changes, disabling tricks or counting wrappers introduced.
The accepted optimization is maintenance, not scientific-frontier progress.
The matched-moment Cauchy theorem is a closed deterministic bridge, not novel
ensemble suppression. Next mathematical attack remains the fixed physical
complete-circuit projector's same-draw growing-replica covariance/action,
with budget-dependent initial cutoff, occupation and fibre sheets retained.

## 2026-10-02: measured covariance and activation optimization

Continued the explicit request to optimize Lean without resource-limit hacks.
Four proof bodies changed in three existing wired leaves; all theorem statements,
definitions, imports and umbrella imports unchanged. Shared one typed coordinate
function in the covariance-diagonal proof; replaced nonlinear arithmetic and
ring normalization with direct order/equality lemmas in quartic activation;
narrowed the fourth-moment envelope's column-norm simplification and combined
its two redundant finite-sum algebra steps. The nonnegativity proof now uses
explicit finite-sum and even-power positivity lemmas.

Matched synchronous native profiling, baseline and candidate in one scratch file:
covariance diagonal 1,189,605 -> 770,094 raw proof-body elaboration ticks (35.26%);
quartic activation 4,772,180 -> 2,796,405 (41.40%);
fourth-moment envelope 6,188,302 -> 2,671,269 (56.83%). Whole-leaf baseline for
the unchanged envelope was 6,191,860, within 0.06% of its matched scratch baseline.
The nonnegativity candidate also passed its scratch check; its comparison was
not paired, so no precise performance percentage is claimed for that change.
No whole-project wall-clock improvement is claimed under current machine contention.
Profiling options only enabled observation and filtered trace output; no maxHeartbeats,
maxRecDepth, disabled limit or heartbeat-counting wrapper was introduced.

All candidate proofs passed with only propext, Classical.choice and Quot.sound.
Integrated source matches measured scratch exactly after replacing theorem names
and removing blank lines. Final leaf/cache checks are running one at a time;
actual-name axiom audit is prepared in scratch and remains pending.
Lint currently reports 11 unrelated unwired RHTower modules, none in edit scope.
No full/umbrella/dependency build, git or subagent work was used.

Covariance and centered-kurtosis repository leaf/cache checks have both exited 0
without warnings. Observer-transfer leaf/cache check is the single owned Lean
process now running; actual-name axiom audit follows only after its completion.

This is verified maintenance, not a new mathematical or physics claim. The
decisive ordinary-ensemble complete-circuit incidence-action bound is still open.

Final repository checks/cache generations for all three edited leaves exit 0
without warnings. Actual-name axiom audit of exactly the four changed declarations
also exits 0: each uses only propext, Classical.choice and Quot.sound. All owned
Lean, search and lint handles have exited. Temporary benchmark/audit sources
have been removed; the empty owned scratch directory is being removed as well.
The explicit rmdir succeeded; the owned scratch directory is now removed.
The engineering adversarial check explicitly rejects whole-project speedup claims
and checks source/scratch identity rather than relying on cached proofs alone.

## 2026-10-02: coherence-floor receiver optimization

Continued requested proof optimization without changing any theorem statement,
definition, import, heartbeat limit or recursion limit. Hybrid corpus search
completed against the current cached index; direct Lean inspection identified
the coherence-floor leaf's nonlinear square-root comparison and redundant
denominator clearing. The local l7 investigation, adversarial critique and
synthesis preceded edits. Both candidates were measured against original
bodies in one synchronous native-profile scratch file.

In fixed_error_receiver_lt_coherence_floor_aux, direct Real.one_le_sqrt and
Real.sqrt_le_self_iff replace the squared-root identity and nlinarith step.
Proof-body elaboration ticks: 7,683,394 -> 5,505,551, a 28.34% reduction.
In returnExcisedStaticChoiPairPurity_exceeds_fixedError_receiver, inverse-factor
normalization replaces field_simp and its unnecessary nonzero side conditions.
Proof-body elaboration ticks: 3,345,688 -> 1,829,899, a 45.31% reduction.
Only matched proof-body improvements are claimed, not whole-project wall-clock
improvement under shared-machine contention. Diagnostic trace settings observe
cost and filter output; they do not alter proof resource budgets.

Both scratch candidates passed, with only propext, Classical.choice, Quot.sound.
Integrated bodies match measured scratch exactly after declaration/helper-name
renaming. The actual repository leaf/cache check exited 0 without warnings,
using lake --old env lean and producing only that leaf's cached olean. Its
existing umbrella import remains intact. No full/umbrella/dependency build,
git operation or subagent was used. Global lint reports 12 unrelated unwired
RHTower modules; none mentions the edited leaf. Actual-name transitive axiom
audit of the changed public capstone (including the changed private helper)
is pending before scratch cleanup.

This is verified maintenance, not new scientific knowledge. The quenched
complete-circuit action bound, with budget-dependent cutoff, occupied image
and all source fibre sheets retained, remains unproved. No optimization result
is being substituted for that missing same-draw ensemble producer.

Actual-name transitive axiom audit now exits 0: only propext, Classical.choice,
Quot.sound. Both changed proof bodies are covered by this public capstone's
dependency closure. All owned Lean/search/lint handles have exited. The three
owned scratch sources and their empty directory have been removed. Explicit
process inspection found no remaining owned Lean process.

## 2026-10-02: projected replica-stable exceptional-source floor

Proof chain remains: budget-dependent cutoff -> quenched occupied-rank action
bound -> continuous complete-circuit exclusion -> same-draw lifecycle. The
last verified optimization is maintenance, not closure of this hard producer.
Requested fields-medalist skill is absent; the fully read local hgtl7 backup
provided the conjecture / falsification / proof / classification workflow.

Fresh hybrid and deep searches completed against the vector-backed cached
index, including observer covariance, commutators, shared-source replication,
slow-source coarea and arbitrary late returns. Some searches are partial;
compiler coverage is mostly source-only, and proposed method groups are not
proofs. One deep method group offered zero-generator evolution as a general
late-return argument; this is inapplicable and was rejected. Direct source
inspection, not search ranking, determined applicability. Latest primary
arXiv work on Kikuchi/partial-commutation spectra gives no transfer to the
fixed-q complete-circuit action producer. No novelty conclusion follows from
empty or partial searches.

Conjecture: growing replicas cannot make exceptional source mass arbitrarily
small at fixed size, clock window and source-independent cutoff, even when
the actual physical target projector and occupied rank are retained. Proof:
T = 1+4|a|+u^2, M = sum of local generator operator norms, and
rho = 1/(2*T*(M+1)). Every coefficient vector in the zero-centred sup-norm
box has T*norm(H) <= 1/2. Duhamel and Choi contraction imply identity Choi
distance <= 1/2 throughout physical times [3*T/4,T], outside the removed
initial interval. This block has surviving Gaussian time mass >= g/4.
For every positive r the arbitrary-target occupied-rank receiver therefore
gives N_inc*A_exc >= [(g/4)*(3/4)^r]^2. This exceeds the fixed-error threshold
[(g/(8*v*T))*(7/16)^r]^2 for v=1+norm(H). The same measurable coefficient
box works for all r and has Gaussian mass >= (2*g*rho)^m > 0.

Formalized public capstone takes data only: arbitrary continuous unitary
family with identity explicitly included, size, cutoff and time offset.
Both source-time restrictions and target projection are retained; there is
no full-purity replacement, independent-copy fiction or spectral-gap premise.
Conclusion is an outer-measure bound, not an unproved measurability assertion
about the rank-changing failure set. Source-dependent inverse-speed cutoffs
are outside the statement. This does not refute a high-probability producer.

Classification: BRIDGE. Continuity, Gaussian box mass and the existing coarea
receiver are known ingredients; this is a closed necessary-exception bound,
not a claim of externally novel science or Brown--Susskind growth. The stronger
ordinary-ensemble upper estimate on typical sources remains unproved.

Lean scratch passed at the default 200000-heartbeat budget. Initial monolithic
capstone exhausted that budget while scalar inference unfolded generator
norms. Explicit positivity and separate semantic scale/box lemmas eliminated
the timeout; no heartbeat/recursion setting or counting wrapper was added.
Integrated only OrdinaryTwoLocalGaussianReplicaStableActionFloorLaw and its
HTGeometry umbrella import. Actual leaf/cache check and new-capstone axiom
audit both exited 0, warning-free. Public statement has data only and the
transitive audit reports only propext, Classical.choice and Quot.sound.
Global lint reports 13 unrelated unwired RHTower modules; no finding names
the added leaf. No full/umbrella/dependency builds, git or subagents were used.

Next falsifiable test: the full Gaussian time measure also sees arbitrarily
late recurrence outside any finite observation horizon. For each fixed draw,
later positive-mass identity-capture windows would force receiver failure at
all sufficiently large r, even without a rare-source argument. This would
constrain replica selection, not refute a finite-r system-size law. Exact
same-draw statement and useful horizon-local positive replacement still need
Lean verification; neither is claimed proved here.

All owned Lean/search/lint handles have exited. Three scratch sources and the
empty owned scratch directory were removed; the verified leaf/cache remains.
Explicit process inspection found no remaining owned Lean process.

## 2026-10-02: continuity elaboration optimization, unchanged proof limits

Latest request is Lean optimization, not a claim to have solved the hard
incidence-action producer. Read L7 skill; investigation, hostile critique and
synthesis preceded edits. Broad deep corpus search returned partial results;
actual source and Lean profiling determined the optimization target.

Profiling identified state_continuous: composition inference unfolded the
ordinary Hamiltonian's finite coefficient sum while resolving a metavariable.
Explicit constants alone retained costly cold inference. A private continuity
helper over an abstract fixed matrix, with a typed parameter/time pair, avoids
that reduction; the ensemble-specific helper now applies it directly.
Original continuity proof-body profile: 2.203356 seconds. Verified abstract
helper plus wrapper: 0.125262 + 0.011782 seconds. These are diagnostic wall
times under shared-machine contention, not a whole-project speedup claim.

Scratch proofs passed under default resource limits. The new transitive axiom
audit reports only propext, Classical.choice, Quot.sound. Integrated source
matches verified scratch except its explanatory comment; public capstone
statement and body are unchanged. Actual leaf/cache check exited 0 without
warnings. Existing HTGeometry umbrella import remains intact; no umbrella,
full-project or dependency build was run. No heartbeat/recursion budget,
counting wrapper, git operation or subagent was used.

Final global lint reports 12 unrelated unwired RHTower modules, none naming
the edited leaf. All owned handles have exited. Four scratch sources and
their empty directory were removed; no owned Lean process remains.
This is verified maintenance. The quenched complete-circuit action estimate
and same-draw growth--plateau--first-recurrence goal remain open.
