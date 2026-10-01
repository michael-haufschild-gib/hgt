# PM multiplicity signature conjecture loop

- **ID:** pm-multiplicity-signature-2026-09-29
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md` §PM; `pm-physical-model-clock-reduction.md` PM-18/19a/19b
- **Statement:** The physical alternating Nyman witness form detects zero multiplicity, not only distinct zero locations.

## Goal

Advance recorded PM-19b without assuming RH, a zero-free region, simplicity, a source positivity law, or any new axiom. No numerical computations. Literal source identities and finite-dimensional algebra must supply every claimed direction.

User updated overarching goal: continue contributing significant PM knowledge until RH is proved or falsified unconditionally in Lean. Completing the multiplicity milestone does not complete that goal; continue the conjecture loop through exact index equality and then the source-side obstruction.

## Plan

- [x] Read PM frontier, source modules, relevant memories, and current instructions.
- [ ] Exhaust corpus search for logarithmic witnesses, confluent coupling, and signature count.
- [ ] Dependency-closed paper proof and public-literature novelty audit.
- [ ] Formalize exact surviving theorem in narrowly imported leaf modules.
- [ ] Direct `lake env lean` audit, axiom audit in `/tmp`, lint, umbrella wiring, cleanup.

## Conjectures and failures

1. Reverse dyadic Haar closure: technically open in local Lean, but card already derives it from bounded equivalent Nyman weight. Classical closure theory found in public sources. Rejected as contribution satisfying requested novelty; retain as infrastructure only if necessary.
2. Multiplicity-sensitive negative index: recorded PM-19b. Candidate: a zero of order `m` gives `m` literal logarithmic witnesses, whose coupling to `m` distinct spurious witnesses is confluent Cauchy and invertible. Their neutral completions produce exact physical Gram matrix `-I_m`. Stronger survivor to investigate: simultaneous hyperbolic signature `(m,m)`.
3. Exact multiplicity index: `witnessNegIndex = rightStripMultiplicityCount`. Lower side is now reduced to the audited literal hyperbolic construction. Upper-side candidate uses correlation-Mellin jets; their common kernel cancels every possible pole of the left dyadic defect, hence is self-similar and neutral. A negative orthonormal family maps injectively into those jets. Finite-dimensional rank bounds its size by total multiplicity; infinite total multiplicity makes the extended upper bound automatic.

## Evidence and limitations

- `FermiNymanWitnessNegativeIndex.lean` constructs `-I_n` for distinct right-strip zeros via `B_lj=(2^(-rho_j)-1/2)/(rho_j-d_l)`; spurious span is neutral.
- `FermiNymanWitnessSelfSimilarityCriterion.lean` localizes non-self-similar witness defects at meromorphic poles unconditionally (PM-19a).
- `MellinIteratedDerivative.lean` identifies all logarithmic source moments with Mellin derivatives for `MellinRapid` densities.
- First broad corpus search returned no lexical AND matches; available hybrid hits had complete source inventory but substantial stale/pending compiler coverage. Narrowed searches underway; applicability requires direct Lean verification.
- No finite search certifies absence from all public literature or training data. Novelty status remains provisional until scoped searches and comparison of exact statements.

## Working log

- 2026-09-29: initialized. Existing dirty files recorded and reserved; no commits/push, no dev server, no full/umbrella build.
- Tool availability: Serena available; `update_plan` and `multi_tool_use.parallel` absent from exposed tools. Plan tracked here; independent reads batched via `Promise.allSettled`.

## Next checkpoint

Read narrow search results; verify reusable Mellin and confluent algebra APIs in `/tmp`; first close all-order literal witness admission. Do not count this ingredient alone as significant final contribution.

## Paper mechanism (candidate, not yet audited)

Write `c(z)=2^(-z)-1/2`, nonzero for `Re z<1`. For a right-strip zero `rho` of order `m`, the functions `conj(d^j/dz^j[t^(z-1)/c(z)] at rho)`, `0<=j<m`, are finite combinations of literal log-power witnesses. Their coupling to spurious witness `g_k` is

`q(g_k,h_(rho,j))=(-1)^j j!/(rho-d_k)^(j+1)`.

Reason: logarithmic Mellin differentiation identifies all source moments; the order of the nonzero eta/source unit times zeta equals the order of zeta; dividing the coupling by `c` removes its triangular jet multiplier. Distinct zero nodes and injective imaginary spurious nodes permit the corpus's complex Cauchy-jet controllability theorem. Thus finite combinations `g_s` of spurious witnesses can satisfy `q(g_s,h_t)=delta_st`, while `q(g_s,g_t)=0`.

For `Q_st=q(h_s,h_t)`, set `v_s^- = h_s - (1/2) sum_t (Q_st+delta_st) g_t` and `v_s^+ = h_s - (1/2) sum_t (Q_st-delta_st) g_t`. Sesquilinearity gives `q(v_s^-,v_t^-)=-delta_st`, `q(v_s^+,v_t^+)=delta_st`, and `q(v_s^-,v_t^+)=0`. This supplies the exact hyperbolic block, hence negative index at least the sum of zero multiplicities in every finite packet.

Audit obligations: all-order L2 log admission; analytic source order; exact conjugation convention; normalized-jet coupling; spurious controllability; no omitted zero or simplicity condition; no computation-backed axiom.

- First ingredient passed scratch Lean: `isFermiNymanWitness_logPower_of_order` admits every log-power jet strictly below zeta analytic order. Source leaf `FermiNymanLogarithmicWitness.lean` created; targeted `lake --old build` underway. No numerical experiments or evaluator-backed proofs used.
- Public comparison: Burnol, *On Fourier and Zeta(s)* (2001), Theorem 7.1, already uses zero multiplicity to characterize jet-vector orthogonality. Logarithmic admission alone is therefore not claimed novel. Exact dyadic-form hyperbolic completion is the candidate distinction.
- A duplicate scratch Lean process was accidentally launched while previous check remained active; older owned process was terminated and its exit verified. Subsequent Lean checks are strictly sequential.

- Narrow PM-jet search returned existing PM-18/19a only, with partial method coverage; exact source searches found no log-power witness or multiplicity-index bridge.
- Serena symbol lookup reports Lean path ignored by configured Python project. Source reads and new-file edits use standard tools.

- All-order admission leaf targeted build passed. Normalized-coupling scratch under audit: compactly supported spurious cuts are MellinRapid; their logarithmic Mellin derivatives compute the literal dyadic pairing. Normalize by the reciprocal of `2^(-s)-1/2` before applying confluent controllability.
- Refined construction avoids choosing an arbitrary finite square confluent matrix: the existing infinite-node complex control map is surjective, yielding finite spurious combinations dual to every finite multiplicity packet. Candidate strengthened to two mutually orthogonal signed families with exact Gram matrices `-I` and `+I`.
- Next capstone is unconditional `rightStripMultiplicityCount ≤ witnessNegIndex`, where the count is the supremum of finite sums over the actual right-strip-zero subtype. Analytic order finiteness will be discharged through the existing xi/zeta order bridge, not assumed.

- Exact normalized-jet/spurious coupling passed scratch Lean without warnings. `FermiNymanConfluentCoupling.lean` created and targeted dependency build started. Reciprocal differentiation uses the toolchain's proved iterated-derivative formula; no numerical computation, evaluator tactic, new premise, or heartbeat increase.
- Import refinement: the multiplicity capstone can prove zeta order finiteness directly by analytic continuation on the punctured complex plane and nonvanishing at `2`. This avoids importing the much broader completed-prime-flux module solely for its xi/zeta bridge.
- Public exact-statement searches (`Nyman-Beurling` with `negative index`, `inertia`, `indefinite`, `dyadic`, `multiplicity`) found no matching physical dyadic theorem. The public 2026 Weil-form inertia framework concerns a different form and compression mechanism; it does not by itself supply the literal Fermi witness construction. Absence from all public literature/training data remains uncertifiable.

## Upper-bound paper mechanism (new conjecture)

For each right-strip zero `rho` of multiplicity `m`, attach the `m` coordinates
`J_(rho,j)(w) = conj(iteratedDeriv j (correlationMellin (conj ∘ w)) rho)`, `j<m`.
The map is complex-linear on finite sums of witnesses: correlation integrates the real alternating generator against `conj(w)`; its bounded compact support makes every Mellin derivative legitimate.

If all coordinates vanish, the analytic order of the correlation Mellin transform at `rho` is at least `m`. The prefactor in the left dyadic defect is analytic, while the entire zeta denominator has order exactly `m`. Thus the quotient has no pole there. Every possible left-half-plane pole corresponds to a right-strip zero: nonvanishing on `Re s >= 1` excludes the rest. Existing unconditional removability then gives self-similarity of `w`, and its dyadic quadratic form is zero.

On a negative orthonormal family, a nonzero coefficient vector gives quadratic form `-sum |c_i|^2 < 0`. Therefore the jet-coordinate map on its span is injective. If total multiplicity is finite, the target has exactly that dimension, proving the upper index bound. If total multiplicity is infinite, the extended-natural upper bound is immediate. This is a dependency-closed paper mechanism; formal obligations remain all-order coordinate linearity, local order cancellation, and finite/infinite counting glue.

- Literal multiplicity signature scratch passed without warnings. New leaf `FermiNymanMultiplicitySignature.lean` then passed targeted `lake --old build` (192s for the new leaf; dependencies replayed). Intrinsic capstones `exists_rightStripMultiplicity_hyperbolic` and `rightStripMultiplicityCount_le_witnessNegIndex` have no hypothesis parameters. All three finished leaves are wired into `RHTower.lean`; no umbrella/full build run.
- Final direct leaf audits, axiom audits, index regeneration, lint and owned scratch cleanup remain outstanding for this milestone.
- Upper-bound scratch `/tmp/pm_upper.lean` now tests analytic local order cancellation and `selfSimilar_of_correlation_order`. No upper bound or index equality is claimed yet.

- Milestone direct audits: `lake env lean` on each of the three actual new leaves returned exit 0 without warnings. `/tmp/pm_axioms.lean` returned exit 0; four key proofs depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Ran documented index command; API, gaps and overview regenerated and search index refreshed. `lint --check-generated` returned exit 1 solely for 15 unrelated modules unreachable from their umbrella (plus existing large-file warnings). None of the PM additions was reported. Preserve concurrent scopes; rerun gate only after further source changes justify it.
- Paper/theorem card moved to `3-formalized/pm-fermi-multiplicity-hyperbolic-signature.md`; full RH goal remains active. Upper scratch now includes correlation-density rapidness and exact complex-linear correlation jet coordinates, under audit.

- Upper coordinate/order scratch passed exit 0 without warnings. New leaf `FermiNymanCorrelationJets.lean` created; targeted old-mode dependency build underway. Proved mechanism: clearing correlation order at every actual right-strip zero forces self-similarity via existing removability; conjugated jets are complex-linear on finite witness sums.
- `/tmp/pm_upper_index.lean` now contains the matching index upper-bound draft: zero jet packet is neutral, negative families inject into finite multiplicity coordinates, finite/infinite type split yields `witnessNegIndex = rightStripMultiplicityCount`. Not yet compiled; no equality claim yet.

- Correlation-jet leaf targeted build passed (252s new leaf, cached dependencies replayed), now wired into `RHTower.lean`. Upper-index scratch launched; final correlation direct audit remains outstanding.
- Next candidate to audit after index closure: algebraic rank of the literal dyadic defect `w(t/2)-w(t)` equals right-strip multiplicity; its nonneutral quotient should carry the actual dyadic Jordan action. Search corpus before accepting this as new. This is a structural candidate, not a source proof of rank zero or RH.

- Upper-index scratch passed exit 0 without warnings after correcting a sum-negation rewrite, identity scalar hom simplification and local sigma-type unfolding. `FermiNymanMultiplicityIndex.lean` now contains the unconditional equality; targeted old-mode leaf build underway. Final actual-leaf and axiom audits remain pending.
- Critique of the next candidate: self-similar witnesses need not lie in the form radical; spurious witnesses are self-similar yet have nonzero pairing with zero jets. The zero correlation-jet packet implies self-similarity, but the converse is not established and must not be assumed. A dyadic-defect rank argument needs its own exact dilation/correlation transfer, rather than identifying these two kernels.

- `FermiNymanMultiplicityIndex.lean` targeted old-mode build passed (70s leaf); wired into `RHTower.lean`. Final direct correlation-jet audit passed exit 0 without warnings. Direct multiplicity-index audit underway.
- Dyadic-difference rank paper mechanism closed without a converse kernel theorem: any negative Gram family has independent literal differences, because a vanishing difference combination is self-similar and therefore has zero quadratic form. Any independent-difference family injects into correlation-jet coordinates because zero jets imply zero difference. Thus `ind₋(q) ≤ rank(D) ≤ M`, and exact index equality closes both. Full proof recorded in `3-formalized/pm-dyadic-defect-rank.md`; draft `/tmp/pm_defect_rank.lean` awaits compiler audit.
- Broad source-cancellation search returned useful source receiver hits with `partial: true`; inventoried coverage complete but compiler coverage mostly pending/stale. No independent half-mass positivity producer surfaced. Scoped rank/public searches found classical dilation and jet work, not an exact matching alternating-Fermi difference-rank theorem. Novelty remains provisional.

- Final actual-leaf multiplicity-index audit passed exit 0 without warnings. Intrinsic equality now has both targeted build and direct `lake env lean` verification; axiom audit underway.
- Next kernel conjecture paper mechanism: continuous dyadic self-similarity makes a witness bounded on `(0,1]`, by reducing each point to the compact interval `[1/2,1]`. A bounded witness has Mellin exponent zero. The literal Fubini factorization then holds near every right-strip zero and factors correlation as zeta times an analytic function. Hence all submultiplicity jets vanish. Together with the new forward cancellation theorem, zero jet packet, boundedness and dyadic self-similarity are equivalent. Corpus search returned existing forward implications but no converse packet classification; `partial: true` limits coverage claims. This mechanism is separate from the form radical and does not produce universal boundedness or RH.

- Upper-stage axiom audit passed exit 0: local cancellation, coordinate linearity and unconditional `witnessNegIndex_eq_rightStripMultiplicityCount` depend only on `propext`, `Classical.choice`, `Quot.sound`. Exact equality recorded in the formalized theorem card and PM frontier. Difference-rank scratch now compiling; kernel paper proof recorded in `3-formalized/pm-correlation-jet-kernel.md` with draft `/tmp/pm_kernel.lean` pending.

- Difference-rank scratch reported one error solely in the generic API probe (`have := @Fintype.linearIndependent_iff` left universe levels unconstrained); every mathematical declaration elaborated without a reported error. Probe fixed with explicit universe levels. New actual leaf `FermiNymanDyadicDifferenceRank.lean` omits the probe and is in its targeted old-mode build. Actual build/direct/axiom audits are required before claiming the rank theorem complete.
- New source conjecture's arithmetic proof closed: for any continuous dyadically self-similar `w`, every literal generator pairing is `-(1/a) integral_(1/2)^1 w(t)/t dt`, `a≥1`. Half-dilation converts the first fractional-part integral to twice the lower half of the second; their difference is the upper half, where the fractional part is exactly `1/(2at)`. Bounded actual witnesses are therefore exactly continuous self-similar profiles with zero logarithmic mean. Corpus/public searches found individual spurious modes and rigidity, but no matching all-profile source identity; corpus result partial and novelty provisional. Proof recorded in `3-formalized/pm-bounded-spurious-classification.md`; implementation queued after current rank/kernel work.

- Difference-rank actual leaf targeted old-mode build passed; wired into `RHTower.lean`. Final direct actual-leaf and axiom audits remain pending. Kernel scratch `/tmp/pm_kernel.lean` now compiling. Bounded-spurious source-classification draft written to `/tmp/pm_periodic.lean`; it awaits the planned actual kernel module before compiling.

- Kernel scratch failed only at local analytic composition (`AnalyticAt.comp` takes the analytic inner-map proof directly) and a redundant argument to `zero_le`; also three unnecessary-simpa warnings. Corrected those in the draft. Actual `FermiNymanCorrelationKernel.lean` created with an unconditional intrinsic set-equality capstone `fermiMultiplicityJetKernelSet_eq_boundedFermiWitnessSet`; targeted old-mode build underway. `boundedFermiWitnessSet` lives in this kernel leaf and is reused by the queued arithmetic classification, avoiding duplicate definitions.

- Kernel leaf targeted old-mode build passed (8.6s leaf), now wired. Mean-classification scratch `/tmp/pm_periodic.lean` launched against that actual module. Final actual-leaf/axiom audits for rank and kernel remain queued; no completed-milestone claim for those stages yet.
- Future conjecture, not accepted yet: weighted dyadic signature tomography. For a weight `t^(2α)` with `-1/2<α≤0`, the matching form subtracts `2^(-1-2α)` times full weighted mass. Admission threshold is `Re rho>1/2-α`; Mellin exponent is `a=1/2+α`, matching the existing general removability receiver. Candidate exact index is the analytic-multiplicity count beyond that threshold. Corpus search initiated before any weighted implementation; no weighted theorem claimed.

- First mean-classification scratch returned formal API/inference errors: `Measure.integrableOn_of_bounded` needs global measurability, whereas continuity supplies restricted measurability. Replaced with the verified `IntegrableOn.of_bound`. Added explicit pointwise function reductions, explicit self-similarity type and the missing product inequality `(a-1)t≥0`; fixed conjugate-function rewrite matching. Revised scratch compiling. No mathematical counterexample to the source identity found.
- Weighted corpus search reported `partial: true`: hits expose existing `L^p` exclusion and general Mellin-exponent removability, plus current unweighted index, but no weighted multiplicity-index theorem. Preferred parameterization is `0<a≤1/2`, weight `t^(2a-1)`, form coefficient `2^(-2a)`, zero threshold `Re rho>1-a`. Weighted spurious coupling should be `2^(1-2a) c(rho)/(rho-(d_l+1-2a))`; this follows directly by integrating the power exponent. No weighted theorem claimed or implemented yet.

- Mean-classification scratch passed exit 0 without warnings after explicit Pi reductions and replacing a recalled unavailable name with the verified `div_lt_one`. Actual `FermiNymanBoundedSpuriousClassification.lean` created, including unconditional bounded-class and full jet-kernel set equalities. Targeted old-mode leaf build underway; then final actual-leaf/axiom audits of rank, kernel and this source classification.
- Weighted candidate now has its own `3-formalized/pm-weighted-multiplicity-tomography.md` card. Extended parameter range `0<a<1` is proposed, with an explicit warning that `a>1/2` uses a new weighted witness class rather than ordinary `L²` membership. No weighted source file edited yet.

- Mean-classification actual leaf targeted old-mode build passed (118s leaf); wired. Direct final actual-leaf audit of `FermiNymanDyadicDifferenceRank.lean` underway, then kernel/classification audits and combined `/tmp/pm_structural_axioms.lean`. No full or umbrella build.
- Hardy search returned `partial: false`, no lexical conjunction hits but useful source candidates. Actual `HardyDyadicWindowTheorem.lean` declares unconditional `exists_riemannZeta_line_zero_dyadic` and `exists_pow_le_xiPosCriticalZeroCount`; inspected proof mechanisms and exact types. These support a proposed weighted index cliff for `a>1/2`, once weighted admission/pairing are proved and this dependency is compiler/axiom-audited. No cliff theorem claimed yet.

- 2026-09-30 resumption: current Stage-3 rank/kernel/classification certificates confirm prior progress. Continued in `pm-weighted-multiplicity-tomography.md`. New `FermiNymanWeightedWitness` and `FermiNymanWeightedSignature` are built, directly audited, axiom-audited and wired. Exact power admission, all-order sufficient log admission, source-neutral weighted Cauchy pairing and finite negative blocks are proved; unconditional Hardy zeros give infinite index for `1/2<a<1`. At `a=1/2` canonical PM index is recovered, still uncontrolled. Stage-3 card: `pm-weighted-critical-index-saturation.md`. Deep cross-corpus energy search completed; full-line dilation isometry and moving-boundary Ramaré covariance do not supply the missing PM source estimate. Full weighted multiplicity equality and RH remain active objectives; no goal-completion claim.

- 2026-09-30 — full weighted multiplicity tomography is now Stage 3. Three new leaves prove weighted Mellin/correlation cancellation, exact normalized logarithmic coupling, multiplicity hyperbolic blocks, and `weightedWitnessNegIndex a = weightedStripMultiplicityCount a` for every `0<a<1`. All targeted builds and three final actual-leaf checks passed; all 48 new declarations have only the standard three axioms. Final global lint fails solely for 17 unrelated unwired modules, with generated indexes current. Source positivity at `a=1/2` remains unproved. Next conjecture/card: `pm-weight-zero-domain-boundary.md`. Goal remains active.

- 2026-09-30 — zero-weight domain boundary formalized in `FermiNymanWeightDomainBoundary`: source witnesses vanish on `(0,1]` for every `a≤0`; nontrivial witnesses exist iff `a>0`. Fixed spurious mode energy is exactly `1/(2a)`, unbounded in every positive neighborhood of zero. Targeted build, final direct actual-leaf audit and all eight axiom checks passed; only standard axioms. Global lint flags 11 unrelated unwired modules. Endpoint card promoted to Stage 3. Two complete deep source-approximation searches returned transfers and mean-value estimates, not an independent producer. Existing raw Möbius critical-energy obstruction suggests the next candidate: exact Fermi Haar head with an unavoidable positive tail floor. New card `pm-raw-mobius-haar-tail-floor.md`; no raw-Fermi Lean code yet.
- 2026-10-01 — raw Möbius Fermi convergence is unconditionally false. The exact head, shrinking support, lower bound `(N+1)H_N²/6`, and cofinal positive error floor are formalized in `FermiNymanRawMobiusTailFloor` (24 declarations, 339 lines). Targeted old-mode build, final direct leaf audit and all axiom checks passed; only the standard three axioms. Leaf wired and indexes current; global lint flags 12 unrelated unwired modules. Card moved to `5-failed/pm-raw-mobius-haar-tail-floor.md` with its exact positive survivor. Three complete deep searches now inspect logarithmic smoothing, its divisor/Chebyshev head identity, and possible prime-discrepancy energy producers. Active card: `pm-log-smoothed-mobius-haar.md`; RH goal remains active.
- 2026-10-01 — logarithmic smoothing has an exact continuous source bridge in `FermiNymanLogMobiusHead` (13 declarations, 217 lines): finite real-floor inversion, literal Chebyshev head error, and complete head/tail energy decomposition. Targeted build, final actual-leaf and all standard-axiom audits passed. Canonical error decay is not proved. A partial variance search located unconditional Chebyshev-error integrability; together with the inspected linear Barban–Vehov mass bound, it supports a new weighted `t dt` endpoint candidate with explicit rate. Card `pm-log-mobius-weighted-endpoint.md` records the paper argument; no endpoint Lean yet. Further complete weighted search found no matching convergence theorem in reviewed hits. RH goal remains active.

- 2026-10-01 — weighted logarithmic Möbius Fermi convergence proved unconditionally: `∫t|h-A_N|² ≤ (N+1)^(-2)+(C+9)/(log N)² →0`. `ChebyshevDyadicWeightedEnergy` and `FermiNymanLogMobiusWeightedEndpoint` add 23 declarations / 325 lines. Targeted build, final direct actual-leaf checks and every axiom audit passed; standard axioms only. Leaves wired, indexes refreshed, all API/name checks passed. Global lint flags 11 unrelated unwired modules, listed on the promoted Stage-3 card. Two complete follow-up searches locate `B_N→1` but no critical variance rate. Next audited paper candidate `pm-log-mobius-auxiliary-variance.md` retains the exact finite variance and its possible mean/variance decomposition. Canonical norm and RH remain open; goal remains active.

- 2026-10-01 — canonical logarithmic auxiliary variance formalized: exact reciprocal tail energy, lower bound `V_N/log²N≤6 E_Fermi(N)`, and decomposition into scalar normalization and intrinsic prime-profile variance. `FermiNymanFiniteCoefficientError` plus `FermiNymanLogMobiusAuxiliaryVariance`: 31 declarations / 378 lines; targeted build, both final actual-leaf checks and all standard-axiom audits passed. Card promoted to Stage 3. Final plain lint flags only 12 unrelated unwired modules. Four complete corpus queries supplied no critical variance upper producer. Next paper candidate `pm-weighted-source-input-power-boundary.md` classifies explicit power profiles admitted by the analytic inputs; positive optimal-variance survivor recorded, no model Lean yet. Actual canonical convergence and RH remain open; goal active.

- 2026-10-01 — analytic-input power boundary fully formalized: 46 declarations / 543 lines in three leaves, exact optimal variance and unique minimizer, sharp half-exponent threshold, arbitrary-centering divergence, unconditional input obstruction. Three old-mode targeted builds and final actual-leaf checks passed; every axiom audit standard only. Imports/names/API entries unique, indexes refreshed. Lint reports 11 unrelated unwired modules only. Positive survivor recorded; card moved to `5-failed/pm-weighted-source-input-power-boundary.md`. Actual arithmetic candidate and RH remain open. Two further complete searches identify the actual Λ-weighted Selberg recursion and signed prime-work balance; next card `pm-selberg-recursion-power-response.md`.

- 2026-10-01 — PM-28 complete: literal Λ-weighted power floor operator classified,
  with exact series response and full half-interval initial-cell correction.
  Explicit same-constant Selberg counterexample retains divergent canonical
  variance. Three leaves / 45 declarations / 541 lines; all targeted builds,
  final actual-leaf and standard-axiom audits passed. Names/imports/API unique;
  index current; lint only 10 unrelated unwired modules. Card moved to
  `5-failed/pm-selberg-recursion-power-response.md`, retaining its positive
  survivor. Next PM-29 rescaled-response scratch is under verification. A
  separate corpus audit tests whether fixed logarithmic coefficients force
  critical simplicity; no implication claimed. Actual RH goal remains active.

- 2026-10-01 — PM-29 complete: exact affine actual-prime floor response, unique
  positive cancelling amplitude, preserved analytic bounds and quantitative
  finite-cell variance comparison. Explicit sublinear response coexists with
  every-centering variance divergence and both unchanged Selberg inequalities.
  Two leaves / 32 declarations / 387 lines; all builds, final actual-leaf and
  standard-axiom audits passed. Wiring/names/API/body checks passed, indexes
  current; lint only 11 unrelated unwired modules. Stage-5 card retains the
  exact positive survivor. Next actual-source candidate is fixed logarithmic
  coefficient convergence versus critical-zero multiplicity; no implication
  formalized yet. RH goal remains active.

- 2026-10-01 — PM-30 first ingredient fully audited:
  `PMLogMobiusMellinPair` (161 lines / 11 declarations), exact coefficient
  Mellin pair and finite-cutoff bridge. General arithmetic dilation interchange
  also passes targeted/direct-leaf/axiom checks; remaining name/index/lint audit
  pending. Prime mean transform scratch now checking. Reused the existing
  exact coefficient unit-cell identity and public harmonic boundedness theorem.
  Full fixed-coefficient simplicity implication remains unproved; actual RH
  goal stays active.

- 2026-10-01 — PM-30 now has five fully audited leaves / 56 declarations:
  exact literal transforms, sharp unit-cell transfer, continuous little-o budget
  and analytic continuation of the cleared identity under canonical error
  convergence. Quadratic Abel draft checking; actual-source simplicity assembly
  drafted but unchecked. No proof of canonical convergence or RH.

- 2026-10-01 — PM-30 closed in Stage 3: six leaves / 64 declarations / 1,196 lines, all targeted/direct-leaf/standard-axiom audits passed. Canonical fixed logarithmic error convergence implies critical simplicity. Literal transforms, continuous budget, analytic continuation and quadratic Abel transfer are certified. Canonical convergence and unconditional RH remain open. Higher-log and damped-source corpus searches supplied no canonical bound; alternate-source investigation remains preparation only.
- 2026-10-01 — PM-31 source ingredient fully audited: `PMPowerDampedMobiusSource`,
  250 lines / 14 declarations, literal finite source, pointwise Haar limit,
  Chebyshev parameter derivative and canonical `MemLp` for `ε>1/2`. All targeted,
  final actual-leaf and standard-axiom checks passed. Exact Mellin scratch now
  checking. Admission at arbitrarily small positive damping remains the proposed
  producer; no RH proof. Card: `pm-power-damped-mobius-haar.md`.

- 2026-10-01 — PM-31 Mellin leaf fully audited: exact arithmetic quotient with
  absolute convergence; explicit canonical `MemLp` gives the analytic transform
  on `Re s>1/2`. Two leaves / 450 lines / 28 declarations now certified. The
  pole-cleared continuation and cofinal-admission RH criterion are next; no
  small-positive-damping norm bound or unconditional RH proof.

- 2026-10-01 — PM-31 receiver fully audited: `PMPowerDampedMobiusCriterion`,
  146 lines / 5 declarations; combined 596 lines / 33 declarations. Cofinal
  positive canonical admission implies RH; failure of RH forces an interval
  of nonadmission. Targeted build, final actual leaf and all standard-axiom
  checks passed. Endpoint `ε=1/2` investigation now uses existing unconditional
  Mertens and modular-energy logarithmic savings. Small damping remains open.

- 2026-10-01 — PM-31 full-prefix energy leaf fully audited: 342 lines / 17
  declarations, combined 938 lines / 50 declarations. Exact reciprocal carrier
  identity and harmonic correction yield unconditional arbitrary logarithmic
  savings for literal Fermi square energy relative to N. All targeted/direct-leaf/
  standard-axiom checks passed. Endpoint Abel/Fatou scratch now checking; no RH.

- 2026-10-01 — PM-31 endpoint leaf fully audited: 246 lines / 12 declarations;
  combined five leaves / 1184 lines / 62 declarations. Abel summation and Fatou
  prove canonical admission for every `ε≥1/2`. All targeted/direct-leaf/standard-axiom
  and exhaustive body/name/API/import checks passed. The Gram investigation now
  separates exact summable diagonal geometry from unresolved signed cross terms.
  No arbitrarily small positive admission or RH proof.

- 2026-10-01 — PM-31 Gram diagonal fully audited: 259 lines / 18 declarations;
  combined six leaves / 1443 lines / 80 declarations. Exact norm `log(2)/a`,
  summable actual diagonal for every positive damping, and positive-block
  failure of coefficient-independent diagonal bounds. All targeted/direct-leaf/
  standard-axiom and exhaustive source/API gates passed. Signed arithmetic
  cancellation remains open; no RH claim.

- 2026-10-01 — PM-31 norm-floor and canonical prime-growth leaves fully audited:
  292 lines / 19 declarations, combined eight leaves / 1735 lines / 99 declarations.
  Every positive damping neighborhood contains a strictly increasing canonical
  prime step and a finite source exceeding any prescribed subunit norm budget.
  Exact finite-cutoff budget transfer and unit limiting budget floor are the
  positive survivor. Prime contraction retired on its failed-route card.
  Next: audit actual-source monotonicity in the damping parameter through a
  symbolic first-prime asymptotic. No small-positive admission or RH proof.

- 2026-10-01 — PM-31 actual-source damping monotonicity refuted and closed.
  `PMPowerDampedMobiusLargeDamping`: 415 lines / 22 declarations; combined nine
  leaves / 2150 lines / 121 declarations. Positive survivor: canonical first-prime
  expansion and `2^ε(E_ε−log 2)→−2κ`, `κ≥1/12`. All gates passed; formal lint
  has only 11 unrelated unwired modules. Next: exact all-positive canonical L¹
  mean and source/error energy decomposition toward the unproved unit budget.

- 2026-10-01 — PM-31 exact mean leaf fully audited, 203 lines / 12 declarations;
  combined ten leaves / 2353 lines / 133 declarations. Every positive damping
  admits canonical L¹ with mean log 2/ζ(1+ε) and slope log 2 at zero. The exact
  admitted L² source/error decomposition isolates the missing upper estimate.
  Next shrinking-error L¹ convergence scratch is checking. RH remains open.

- 2026-10-01 — PM-31 canonical L¹ Haar convergence fully audited: 260 lines /
  19 declarations; combined twelve leaves / 2917 lines / 181 declarations.
  The explicit finite reciprocal raw-error sum bounds L¹ error by Cε for all
  positive ε. Targeted186s/final leaf/standard3axioms/all-source/API audits passed.
  Global lint still has ten unrelated unwired modules and concurrent generated
  staleness. Next L¹ derivative scratch is running; no small-positive L² or RH.

- PM-31 derivative audit closed: `PMPowerDampedMobiusDerivative` (304 lines /
  29 declarations) passed targeted old build, final actual leaf, every axiom
  report (standard three only), exact body/API/name/unique-import gates.
  The actual difference quotients converge in canonical L¹ to the dyadic
  Chebyshev source, whose signed integral is log 2. Combined: twelve audited
  leaves / 2917 lines / 181 declarations. Small-positive L² admission and RH
  remain open; the derivative's proposed L² exclusion is not yet certified.

- PM-31 Hilbert-tangent obstruction audit closed: two additional leaves,
  `PMPowerDampedMobiusDerivativeMellin` (153/10) and
  `PMPowerDampedMobiusDerivativeBoundary` (226/6), passed targeted builds,
  both final actual leaf checks, every standard-axiom report, exact body,
  exhaustive name, public API and unique-import audits. Combined PM-31:
  fourteen fully audited leaves / 3296 lines / 197 declarations. The exact
  strong L¹ Chebyshev tangent is outside canonical L²; actual quotient norms
  exceed every finite budget arbitrarily near zero. Closed failed card:
  `5-failed/pm-power-damping-hilbert-tangent.md`, retaining the positive L¹
  convergence and exact mean log 2. Small-positive L² admission and RH remain
  open. Next: exact prime-two-deleted Haar resolvent and the all-subset unit
  ceiling, tracked in `pm-dyadic-prime-deletion-unit-budget.md`.

- Dyadic resolvent ingredient fully audited: `PMPowerDampedMobiusDyadicResolvent`
  (299 lines / 29 declarations), targeted old build 18s, final actual leaf empty,
  all standard-axiom/body/name/API/unique-import gates passed. Exact canonical
  energy 2, mean 0, norm sqrt 2 and pointwise support/recurrence uniqueness are
  certified. Combined PM-31: fifteen leaves / 3595 lines / 226 declarations.
  Odd-Möbius identification and all-subset budget obstruction remain pending;
  no closure of the prime-deletion no-go yet. Small-positive L² admission and
  RH remain open. Latest lint: twelve unrelated unwired modules and concurrent
  LEAN_API staleness; no owned or proof-debt finding.

- PM-31 prime-two deletion audit closed: `PMPowerDampedMobiusDyadicDeletion`
  (257 lines / 26 declarations), targeted old build 7.3s, final actual leaf
  empty, all bodies/names/API/unique-import/standard-axiom gates passed.
  The literal odd-Mobius source equals the Haar resolvent: canonical L2,
  exact energy 2, mean 0, norm sqrt 2. Every finite-prime all-subset budget
  below sqrt 2 fails arbitrarily near zero damping, with admitted actual
  finite sources as witnesses. Moved `pm-dyadic-prime-deletion-unit-budget`
  to `5-failed`, preserving the fully proved positive survivor. Combined:
  sixteen leaves / 3852 lines / 252 audited declarations. Latest global lint:
  twelve unrelated unwired modules; no owned or proof-debt finding.
  Next conjecture: `pm-finite-prime-deletion-energy` tests whether every
  finite all-subset budget fails via the nonnegative Haar Gram kernel and
  smooth-number harmonic energy. Canonical full cutoffs and RH remain open.

- PM-31 Haar Gram leaf fully audited: `PMPowerDampedMobiusHaarGram`
  (211 lines / 26 declarations), targeted old build 152s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  It proves K(a,b)=max(0,2/max(a,b)-1/min(a,b)), finite Haar-sum energy,
  diagonal lower bounds and energy monotonicity under finite inclusion.
  Combined PM-31: seventeen leaves / 4063 lines / 278 audited declarations.
  Latest lint: thirteen unrelated unwired modules; no owned/proof-debt finding.
  Hilbert-series scratch1045 is checking; smooth-source scratch1046 is
  prepared but unrun. The stronger all-subset budget no-go is not closed.
  Canonical small-positive admission and RH remain open.

- PM-31 Hilbert-series leaf fully audited: `PMPowerDampedMobiusHaarSeries`
  (151 lines / 16 declarations), targeted old build 92s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  Summable dilation norms identify the actual pointwise series with its
  Hilbert sum; exact energy is the iterated Gram sum and dominates every
  finite reciprocal diagonal. Combined: eighteen leaves / 4214 lines /
  294 audited declarations. Latest global lint: seventeen unrelated unwired
  modules and three concurrently stale generated files; no owned or proof-debt
  finding. Sixteen-declaration smooth-source scratch1046 checks next;
  nine-declaration arithmetic scratch1047 is prepared and unrun. The broader
  no-go and canonical small-positive admission/RH remain open.

- PM-31 smooth-source leaf fully audited: `PMPowerDampedMobiusSmoothHaar`
  (147 lines / 16 declarations), targeted old build 4.6s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  Each fixed smooth-number Haar source is canonically L2/L1, supported in
  (0,1], with zero mean and exact nonnegative Gram energy. Its energy
  dominates the harmonic sum and diverges with the prime cutoff. Combined:
  nineteen leaves / 4361 lines / 310 audited declarations. Latest global
  lint: ten unrelated unwired modules and three concurrent generated-file
  changes; no owned/proof-debt finding. Full 23-declaration arithmetic/budget
  scratch1047 checks next. The broader all-subset no-go is not closed yet.
  A separate paper candidate `pm-canonical-prime-aperture-threshold` tests
  divergence at fixed epsilon<1/2 even for canonical prime cutoffs, paired
  with explicit all-subset bounds for epsilon>1/2. No Lean proof of that
  stronger candidate is claimed. Actual small-positive admission/RH stay open.

- PM-31 arithmetic/deletion leaf fully audited: `PMPowerDampedMobiusFiniteDeletion`
  (283 lines / 23 declarations), targeted old build115s, final actual leaf empty,
  every exact-body/name/API/unique-import/standard-axiom gate passed. Literal
  deleted Mobius sources equal smooth Haar sums. For every finite budget and
  every positive damping neighborhood, an admitted actual finite prime source
  exceeds that budget. Combined: twenty leaves / 4644 lines / 333 declarations.
  Global lint: eleven unrelated unwired modules and three concurrently stale
  generated files; no owned/proof-debt finding. The strongest arbitrary-finite-set
  positive survivor is prepared in scratch1050 (22 declarations), now checking.
  No-go closure awaits that exact generality; actual small-positive admission
  and unconditional RH remain open.

- PM-31 arbitrary finite-deletion survivor fully audited:
  `PMPowerDampedMobiusFiniteSmoothSource` (220 lines / 22 declarations), targeted
  old build7.7s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. For every finite E, the literal deleted-Mobius
  source equals its strongly summable smooth Haar series, is canonically L2/L1,
  has zero mean and exact nonnegative double-Gram energy, with reciprocal Euler
  product diagonal lower bound. Combined: twenty-one leaves / 4864 lines /
  355 audited declarations. Global lint: thirteen unrelated unwired modules
  and two concurrently stale generated files; no owned/proof-debt finding.
  Retired `pm-finite-prime-deletion-energy`: every finite all-subset bound
  uniform in damping near zero is impossible, with the exact arbitrary-finite-E
  positive survivor now on paper and in Lean. This does not exclude a finite
  C(epsilon), canonical-only bounds, or actual small-positive admission.
  Next candidate: `pm-canonical-prime-aperture-threshold`; scratch1051 checks
  the upper boundary and real Euler decay, while1053/1055 remain unrun.
  Unconditional RH/negRH remain unproved.

- PM-31 canonical prime threshold fully audited: `PMPowerDampedMobiusPrimeThreshold`
  (436 lines / 22 declarations), targeted old build197s, final actual leaf empty,
  all exact-body/name/API/unique-import/standard-axiom gates passed. For every
  fixed0<epsilon<1/2, canonical prime-aperture norms tend to infinity and
  eventually exceed every finite budget. The exact positive survivor is the
  explicit common finite budget `3 sum_d d^(-epsilon-1/2)` for epsilon>1/2,
  valid for every finite integer aperture, together with the proved finite
  Mellin identity and bounded-cofinal Mellin transfer. Endpoint1/2 unclassified.
  Combined: twenty-two leaves /5300 lines /377 audited declarations. Latest
  global lint: eleven unrelated unwired modules and two concurrently stale
  generated files; no owned/proof-debt finding. Retired canonical prime-budget
  producer with the strict-interval classification fully proved on paper and
  in Lean. Actual source admission at arbitrarily small positive damping and
  unconditional RH/negRH remain open. Next card:
  `pm-centered-divisor-haar-criterion`, an exact mean-centered discrepancy
  energy criterion with paper argument and corpus audit; no new Lean yet.

- PM-31 centered-divisor arithmetic leaf fully audited:
  `PMPowerDampedMobiusDivisorHaar` (295 lines /29 declarations), targeted old
  build24s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. Positive divisor coefficients have exact
  Euler factors; their summatory mean is `1/zeta(1+epsilon)`. The actual
  Fermi source is both a finite weighted Haar sum and the dyadic difference
  of its mean-centered reciprocal summatory remainder. The backward boundary
  vanishes and the finite dyadic sums converge pointwise to that literal
  centered source. Combined: twenty-three leaves /5595 lines /406 audited
  declarations. Global lint has ten unrelated unwired modules and three
  concurrently stale generated files; no owned/proof-debt finding.
  Scratch1063 now checks reverse L2 admission with constant `1+sqrt2`,
  forward admission, and reciprocal weighted-energy equivalence. The actual
  small-positive arithmetic energy bound remains open; RH/negRH unproved.

- PM-31 centered-energy criterion fully audited:
  `PMPowerDampedMobiusCenteredEnergy` (226 lines /22 declarations), targeted
  old build119s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. For epsilon>0, actual Fermi-source canonical
  L2 admission is equivalent to integrability of the literal centered divisor
  discrepancy squared against dx/x^2. Backward finite-sum norms have the
  explicit bound (1+sqrt2) times the source norm; Fatou identifies the actual
  boundary-normalized remainder. The reciprocal energy identity, inherited
  epsilon>=1/2 admission, and cofinal weighted-energy RH receiver are proved.
  Combined: twenty-four leaves /5821 lines /428 audited declarations.
  Global lint has eleven unrelated unwired modules and three concurrently
  stale generated files; no owned/proof-debt finding. The energy receiver's
  small-positive premise remains open. New producer card:
  `pm-centered-divisor-dyadic-energy-budget`; scratch1068 checks the exact
  pointwise absolutely summable damped Nyman/fractional-part representation.
  No RH/negRH proof or small-positive geometric energy bound is claimed.

- PM-31 literal Nyman-series leaf fully audited:
  `PMPowerDampedMobiusNymanSeries` (95 lines /11 declarations), targeted old
  build34s, final actual leaf empty, every exact-body/name/API/unique-import/
  standard-axiom gate passed. The centered discrepancy is the negative
  damped fractional-part series, pointwise absolutely summable at every
  positive damping and positive physical time. Its natural integer prefixes
  converge pointwise to the actual centered source; the density is real.
  Combined: twenty-five leaves /5916 lines /439 audited declarations.
  Global lint: eleven unrelated unwired modules and three concurrently stale
  generated files; no owned/proof-debt finding. The actual small-positive
  dyadic/cumulative energy bound remains open. Next: exact unrestricted
  discrete weighted-energy/covariance bridge, then the signed arithmetic
  bound. No global L2 interchange or RH/negRH proof is asserted.

- PM-31 unrestricted discrete-energy leaf fully audited:
  `PMPowerDampedMobiusDiscreteEnergy` (224 lines /18 declarations), targeted
  old build143s, final actual leaf empty, every exact-body/name/API/unique-
  import/standard-axiom gate passed. Unit-cell integrability and countable
  assembly remove the old bounded-sequence premise. For every epsilon>0,
  actual canonical admission is equivalent to summability of
  D_epsilon(n)^2/(n(n+1)), where D is the cumulative centered divisor
  coefficient. Equivalently, its exact finite signed maximum-index
  covariance has a common bound in the cutoff. The epsilon>=1/2 range is
  unconditional; cofinal small-positive budgets would imply RH but remain
  unproved. Combined: twenty-six leaves /6140 lines /457 audited declarations.
  Global lint reports eleven unrelated unreachable modules; no owned or
  proof-debt finding. No RH/negRH proof is claimed.

- PM-31 positive-divisor Haar prefix leaf fully audited:
  `PMPowerDampedMobiusPositiveHaarPrefix` (239 lines /21 declarations),
  targeted old build64s, final actual leaf empty, all exact-body/name/API/
  unique-import/proof-debt/standard-axiom gates passed. The exact clipped
  counts give stabilization to the actual source and the initial plateau
  -C_epsilon(N), with energy contribution C_epsilon(N)^2/(2N). Rescaled
  prefixes converge pointwise to alpha_epsilon times the universal boundary
  profile beta, with common 3min(1,1/u) envelope. Each finite prefix has zero
  integral. Combined: twenty-seven leaves /6379 lines /478 declarations.
  Strong L2 profile/leading energy is checking in scratch1080; do not retire
  this cutoff candidate until that positive survivor is fully audited.
  Actual small-positive source admission and RH remain open. Global lint:
  eleven unrelated unwired modules and concurrent generated-document
  staleness, no owned or proof-debt finding.

- PM-31 universal boundary profile fully audited: `PMPowerDampedMobiusHaarBoundaryProfile`
  (292 lines /19 declarations), targeted old build46s, final actual leaf
  empty, all exact-body/name/API/unique-import/proof-debt/standard-axiom
  gates passed. Rescaled raw positive-Haar prefixes converge strongly in
  L2 to alpha_epsilon*beta; integral beta^2=2-2log2 and integral beta=-log2.
  Their energy divided by the cutoff tends to the strictly positive
  |alpha_epsilon|^2*(2-2log2), so raw-prefix common budgets fail at EVERY
  positive damping. Their L1 error is at least |alpha_epsilon*log2|.
  This does not refute actual-source admission. The exact positive survivor
  closes this no-go; the raw cutoff card is retired. Combined: twenty-eight
  leaves /6671 lines /497 audited declarations. Follow-up: centered Haar
  cutoff/endpoint-trace criterion; the small-positive signed energy
  producer and RH remain open. Global lint: eleven unrelated unwired
  leaves and concurrently stale generated docs, no owned/proof-debt finding.

- PM-31 clipped Haar source fully audited: `PMPowerDampedMobiusClippedHaarSource`
  (242 lines /22 declarations), targeted old build49s, final actual leaf
  empty, all exact-body/name/API/unique-import/proof-debt/standard-axiom
  gates passed. Subtracting alpha_epsilon*N*beta(Nt) gives exactly the
  dyadic difference of R_epsilon(min(N,1/t)); every finite corrected
  prefix is admitted and stabilizes pointwise to the actual source.
  Its primitive energy is exactly truncated divisor energy plus
  |R_epsilon(N)|^2/N. Generic dyadic difference norms lie between
  (sqrt2-1)||f|| and (sqrt2+1)||f||. Combined: twenty-nine leaves /6913
  lines /519 audited declarations. The endpoint convergence and cofinal
  selection proofs are in scratch, not yet certified. Small-positive
  arithmetic admission remains open. Global lint: ten unrelated unwired
  modules and stale LEAN_GAPS/LEAN_OVERVIEW, no owned/proof-debt finding.

- PM-31 cutoff trace/cofinal criterion fully audited:
  `PMPowerDampedMobiusHaarCutoffTrace` (324 lines /16 declarations),
  targeted old build15s, final actual leaf empty, all exact-body/name/API/
  unique-import/proof-debt/standard-axiom gates passed. Under actual
  admission, both clipped-primitive and density-repaired-prefix L2
  convergence are equivalent to |R_epsilon(N)|^2/N tending to zero.
  Actual admission supplies a strict cofinal trace-zero sequence, and is
  equivalent to a common cofinal repaired-prefix norm budget. The exact
  criterion card moves to formalized. Combined: thirty leaves /7237 lines
  /535 audited declarations. Full-sequence endpoint-atom correction is
  the next paper-proved conjecture; actual small-positive energy admission
  and RH remain open. Global lint: ten unrelated unwired leaves, all three
  generated docs concurrently stale, no owned/proof-debt finding.

- Endpoint correction fully audited: `PMPowerDampedMobiusEndpointHaar`
  (215 lines /17 declarations), targeted old build294s, final actual-leaf
  check with empty diagnostics, all17 standard-axiom reports, exact body,
  exhaustive names/API, unique import and proof-debt checks passed. Its
  exact truncated-source identity removes the endpoint trace, giving
  full-integer-cutoff L2 convergence under actual admission and an exact
  full-sequence energy-budget criterion. Global lint still reports twelve
  unrelated unwired leaves, no owned/proof-debt issue. Combined: thirty-one
  leaves /7452 lines /552 audited declarations. The actual small-positive
  signed energy bound remains open. Next: divisor second-moment density.
