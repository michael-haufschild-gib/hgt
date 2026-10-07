# WP02 evidence

## Corpus searches (2026-10-07)

- `research "exposing ray" --json`: complete response; older coverage snapshot and semantic coverage unavailable; ranked near matches included irrelevant rays. Source verified manually.
- `research 'WeilDualBound' --mode lexical --exact --per-module 0`: exact definition and receivers located.
- `research 'exposing ray archimedean threshold tail bound' --mode deep --module Weil --budget-seconds 300 --json`: partial=false, semantic coverage unavailable; existing exposing receiver and threshold identity recovered. Candidate lemmas, source arguments, proof ideas and ingredient sets inspected; no closing estimate found.
- `research 'ground state transform Weil archimedean Riemann kernel Dirichlet energy' --mode deep --module Weil --budget-seconds 120 --json`: partial=true; available sources checked. Exact rg located `RiemannKernelGroundStateZeroIdentity`.
- `research 'archimedean energy positive difference kernel jump' --mode lexical --any --module Weil --json`: located the archimedean jump representation and sign-changing full kernel.
- `research 'WeilDualBound exposingTail cofinal transport' --mode deep --module Weil --budget-seconds 90 --json`: partial=false, semantic coverage unavailable; parent linear-duality receiver recovered; no explicit cofinal tail transport located.
- `research 'prime blind Haar marginal logarithm torus archimedean positivity' --mode deep --module Weil --budget-seconds 120 --json`: partial=true; did not supply the required sign law. Source inspection found nonpolar negative prime-blind Fejer test, so a frequency-only relaxation is inadequate.

Search coverage is not a proof of novelty or absence. Compiler applicability is checked separately. Most search hits are source-only.

## External audit

- Connes–Consani, *Weil positivity and Trace formula, the archimedean place*, https://arxiv.org/abs/2006.13771 (abstract opened): semilocal trace framework and archimedean case, not WP02's endpoint producer.
- Zhu, *Weil positivity in compact windows*, https://arxiv.org/abs/2608.24827, v2 2026-09-02 (abstract opened): certified bounded-window estimates and limitations of pointwise-symbol certificates. No numerical procedure reused.
- Groskin, *A finite Guinand–Weil dictionary and archimedean tail order*, https://arxiv.org/abs/2607.02828, v3 2026-08-14 (abstract opened): finite Galerkin identities and tail certification; no global RH claim.
- Connes–Consani survey, https://ems.press/content/serial-article-files/37042 (opened).
- Exact mechanism searches for exposing rays / Weil ground-state transforms did not locate a stronger external result. Some searches returned irrelevant results. These searches do not establish novelty; the tail repair is explicitly classified BRIDGE under the corpus's own parent theorem.

## Reused declarations

From `WeilPositivityPrimeBlindDuality`:
`resonatorMass_pos`, `isPolarTest_twoPointResonator`, `atomCoeff_twoPointResonator`, `archEnergy_twoPointResonator_le`, `atomLevel_le`.

From `WeilPolarConeExposedDuality`:
`exposingWeight`, `exposingMajorant`, `exposingMajorant_nonneg`, `summable_exposingTail_terms`, `exposingTail`, `tendsto_exposingTail`, `exposingWeightTrunc` and the existing final RH receiver.

The normalization is checked exactly: alpha=|w(n)|/(4*pi*mass(n)); the dual atom convention has the extra factor 2*pi.

## Verification log

- `lake --old env lean /tmp/wp02_names.lean`: exit 0; this-toolchain symbol checks succeeded.
- New leaf compilation: exit 0; details below.
- Axioms: standard three only; details below.
- Umbrella wired; lint exit 1 on unrelated modules, detailed below.

## Completed verification

- Final targeted source audit: `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayTailRepair.lean`, exit 0, no warnings.
- `/tmp/wp02_axioms.lean` contained the exact source plus four `#print axioms` commands; `lake --old env lean /tmp/wp02_axioms.lean`, exit 0.
- `exposingRepair_sum_atoms`, `exposingRepair_energy_le_tail_sub`, `exposingRepair_uniform_vanishing`, `exposingRepair_level_le`: each `[propext, Classical.choice, Quot.sound]`.
- RHTower import added beside `WeilPolarConeExposedDuality`. Other existing umbrella edits preserved.
- `scripts/formal_tools.py lint`, exit 1: unreachable RHTower modules `WeilWorkDeficitRecovery`, `WeilWorkHigherDenominatorCentralTest`, `WeilWorkPBAPNullRepair`, `WeilWorkQuantizationBoundaryPhase`, `WeilWorkQuantizationKernel`, `WeilWorkSingularArithmeticSharpReciprocal`; unreachable HTGeometry modules `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. Numerous existing large-file warnings. No WP02 error. This is current unrelated state, not an assertion that all eleven errors predated the session.
- No full umbrella build run.

## Further novelty audit

Exact per-atom cost search `research 'twoPointResonator archEnergy logarithmic asymptotic sharp cost' --mode deep --module Weil --budget-seconds 120 --json`: partial=false, older coverage snapshot and semantic coverage unavailable. Existing upper bound located; no matching lower bound located. One source hit was this session's newly indexed repair module and was excluded as independent prior evidence.

`research 'logarithmic uncertainty support measure Fourier density energy' --mode deep --budget-seconds 90 --json`: partial=true, weak near matches; no useful exact lemma. `research 'polar inverse integer sampling archimedean positivity' --mode deep --module Weil --budget-seconds 120 --json`: partial=false, older coverage snapshot; exact rg identified `CCMRestrictedWeilPolarInverse`.

Laptev–Weth, *Spectral properties of the logarithmic Laplacian*, https://link.springer.com/article/10.1007/s13324-021-00527-y , Theorem 4.1 and Remark 2 read. Its support-volume lower bound and Beckner ancestry are the relevant parent theory for logarithmic repair costs. Hence the proposed generic uncertainty mechanism cannot be presented as new scientific knowledge.

- `scripts/formal_tools.py index`: exit 0; refreshed generated API, gaps, overview and lexical index.
- Scoped `git diff --check`: exit 0. Owned temporary search, scratch and audit files removed; no owned process left running.


## Collective packet cycle — in progress

Corpus deep queries: collective archimedean logarithmic lower bound; polar autocorrelation spectral factorization; critical harmonic Toeplitz residual; shrinking-bump coercivity; negative-Sobolev polar inverse mass; atom-coefficient Fourier-mass bound. Available candidate lemmas and source arguments inspected. Coverage was partial or from older snapshots; several queries returned no exact applicable result. No absence or novelty conclusion drawn from retrieval.

Parent declarations checked in source: `paperFT_gC`, `integral_gR_sq_ge`, `integral_d2_sq_pos`, `weilTest_translates_log`, the Plancherel cosine identity, `re_digamma_vertical_ge`, and the existing Toeplitz upper-bound proof. The harmonic vector does not supply the target exposing trace. Krein factorization's classical parent (Lawton, https://arxiv.org/abs/2104.08917, abstract opened) does not provide the missing sign or automatically preserve C² regularity.

External logarithmic-uncertainty literature inspected through Laptev–Weth and primary-source search. No numerical experiment, sampled matrix or finite certificate used. `PACKET-PROOF.md` records the complete direct one-dimensional proof before formalization.

Lean optimization: an elaboration timeout occurred at a generic autocorrelation rewrite. Heartbeat limit was left unchanged; explicit specialization and proof restructuring are being used. No mathematical premise was added.


## Packet verification results (latest)

- Final `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayPacketCoercivity.lean`: exit 0, no warnings. No heartbeat override. Generic function inference inside an autocorrelation `change` was replaced by an explicit function; remaining normalization was handled by exact algebra.
- New leaf wired directly after `WeilWorkExposingRayTailRepair` in RHTower. No umbrella build.
- `scripts/formal_tools.py index`: exit 0, four changed index entries; generated API/gaps/overview refreshed.
- Latest formal lint: exit 1, seven unrelated reachability errors: RHTower `WeilWorkDeficitSharedMass`, `WeilWorkHigherDenominatorSpectralSubtraction`; HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. Neither WP02 module is named. Earlier eleven-error report above is historical, not the latest workspace state.
- `/tmp/wp02_packet_audit.lean` contained the exact final source plus this-toolchain name checks and `#print axioms`; exit 0. `exposingPacket_fourier_multiplier`, `exposingPacket_inverse_mass`, `exposingPacket_archimedean_coercivity` each depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Scoped tracked-file whitespace check passed. No-index checks of the four new/owned outputs emitted no whitespace diagnostics (exit 1 denotes differing files against `/dev/null`).
- Owned temporary searches, scratch files and audit logs removed after their results were recorded. No owned Lean build remains running.

## Cycle 4 source audit

- Revalidated current working card, compiled packet capstone source and live RHTower imports before continuing.
- Deep corpus queries covered polar convolution/energy approximation, current exposing-ray source bounds, constrained ground-state Poincare mechanisms, reciprocal-resolvent convexity, analytic strip sampling and polar-primitive logarithmic quadrature. Available candidate lemmas and source arguments inspected. Responses were partial or used older coverage snapshots; semantic coverage was unavailable. No absence/novelty conclusion follows.
- `SuzukiHlogMollifiedFormCore.suzukiHlogMollifiedFormVector_tendsto_inward` proves convergence in the actual weighted form norm. `WeilFullConeConvolutionPositivity` supplies exact convolution/Fourier/autocorrelation interfaces. These were used to audit the topology required in the overlap no-go paper proof.
- `CCMRestrictedWeilPolarMultiplier` supplies the existing `CCMComplexSmoothInteriorSource.polarMultiplier`, its smooth compact support, exact differential expression and polar constraints. The full smooth compact primitive inequality uses this interface directly.
- Merkle, *Reciprocally convex functions*, Journal of Mathematical Analysis and Applications 293 (2004), 210–218, https://www.sciencedirect.com/science/article/pii/S0022247X04000393: primary search abstract inspected; opening full page returned 403. The abstract identifies negative Stieltjes transforms as a reciprocal-convexity parent class. No claim based on inaccessible full text.
- `CCMRestrictedWeilPolarGroundVariance` already gives an exact source variance law and a countermodel showing that variance plus shifted positivity does not exclude an arithmetic zero ground. Avoid repackaging that mechanism as a missing producer.
- Scratch names `/tmp/wp02_overlap_names.lean`: exit 0. Arbitrary-overlap version of the leaf: `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayPacketCoercivity.lean`, exit 0. Full compact-interface extension is undergoing its separate audit.


## Cycle 4 completed verification

- `/tmp/wp02_compact_audit.lean` contained the exact extended source, new-name checks and axiom commands: exit 0. `exposingOverlap_archimedean_primitive_bound` and `exposingCompact_archimedean_primitive_bound` each use only `propext`, `Classical.choice`, `Quot.sound`.
- Final `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayPacketCoercivity.lean`: exit 0, no warnings. No heartbeat changes, computations or full builds. The new source theorem uses the existing smooth compact polarMultiplier interface; regularity coercions are explicit because C-infinity is below the separate analytic top in this toolchain.
- Existing umbrella import revalidated. `scripts/formal_tools.py index`: exit 0, four changed entries; generated files refreshed.
- Latest lint: exit 1, twelve unrelated reachability errors. RHTower: `WeilWorkDeficitLeakageIntegral`, `WeilWorkDeficitMassBounds`, `WeilWorkDeficitPoissonLeakage`, `WeilWorkSingularArithmeticMellinMass`, `WeilWorkSingularArithmeticQuotient`, `WeilWorkSingularArithmeticWeightedZeta`. HTGeometry: `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`, `CrouzeixObservationEnergy`. Neither WP02 module is named. Older lint results above are historical.
- Whitespace check of seven owned source/report/card files: clean. Owned temporary files removed after recording results; all owned tool/build processes completed.

## Cycle 5: literal tail audit (formal validation complete)

- Rejected near-threshold upper-witness existence as a new research claim: existing `exists_weilPositive_ge_iff_forall_weilDualBound` plus exposure already supplies its abstract dual consequence. No wrapper added.
- Critical-rate sampling parent inspected: `PrimeBlindCarlsonThreshold.fourier_eq_zero_of_integerMoment_eq_zero_room`, plus the actual Fourier normalization in `RiemannAutocorrFourier`. This was not used as an unproved premise in the selected argument.
- Selected source argument: `riemannLeadTerm_ge` and `riemannKernelReal_sandwich` in `WeilFullConeMinorantRigidity` give two-sided theta envelopes. The actual `polarExposingKernel` expands into positive shifts up to distance two and negative shifts up to distance one. This yields eventual positivity and the candidate exact exponential coefficient rate `2*pi*exp(-2)`; TAIL-SIGN-PROOF.md records the complete paper argument and its limitation.
- Corpus searches included exact gamma/arithmetic residual, literal kernel sign, finite matched feasibility, prime-blind sampling, critical Xi decay and theta autocorrelation tails. Several deep searches reported unavailable/deadline-expired semantic retrieval; no scientific novelty claim rests on missing hits. Exact source searches found no separate exposing-weight rate theorem at the time of this audit.
- External primary parents read: [Pila, Note on Carlson's theorem](https://people.maths.ox.ac.uk/pila/carlson.pdf); [Shi, Real-rooted Pólya-like approximations](https://arxiv.org/abs/1502.06844); [Redmond–Ryavec, BesselK series](https://arxiv.org/abs/1710.09987). Pila supplies general uniqueness context; the two arXiv abstracts concern theta-tail approximations and Bessel representations. None is being cited as a proof of the literal exposing-weight asymptotic, nor does this narrow search certify novelty.

Final cycle-5 audit: `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayTailAsymptotic.lean` exits 0 with no warnings. Exact-source `#print axioms` checks for the two autocorrelation envelopes, exponential upper/lower coefficient bounds, eventual sign, logarithmic rate, exponential tail bound and strict tail positivity all report only propext/Classical.choice/Quot.sound. No numerical jobs, heartbeat overrides or umbrella/full builds were used.

- Latest lint exits 1 on seven unrelated unreachable modules: RHTower.WeilWorkDeficitArithmeticMean, RHTower.WeilWorkHigherDenominatorFiniteBoundary; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No WP02 module is flagged. Global lint is not clean; unrelated files were preserved.

## Cycle 6: uniform source truncation

- Two deep corpus searches (finite natural-aperture matching; weighted theta truncation) finished without partial flags. Compiler coverage remained mostly source-only/stale; results were checked against exact source. Candidate/proof-idea sections returned known receivers and fixed-shift convergence, not a global lower producer.
- Source parents: theta sandwich, cutoff values in [0,1], correlation envelope lemma, exact double polar shift, summable von Mangoldt/n^2, actual near-radical ratio estimate, exact archimedean energy split. All named APIs were inspected and checked in the current toolchain.
- Complete scratch `/tmp/wp02-cycle6-proof.lean`: exit 0, no warnings. Initial failures were pointwise-function subtraction coercions and an over-eager `gcongr`; no mathematical assumption or heartbeat change was introduced.
- Primary audit: [Connes–Consani](https://arxiv.org/abs/2006.13771); [Zhu v2](https://arxiv.org/html/2608.24827v2), including its upper-bound section, limitations and reference ancestry; [Freedman](https://arxiv.org/abs/2606.29555). These establish context, not the literal theorem. The inspected finite-window work uses computations, which were not run here. Literature novelty is unestablished.
- New paper sharpening: the next finite realization can achieve E+(1+epsilon)*tau_N at a fixed additive aperture overhead, for every epsilon>0 and sufficiently large N. The shift cutoff is finite and all residual integer traces are repaired. This remains paper only.

- Final installed command `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayUniformTruncation.lean` from `formal/`: exit 0, no warnings. The initial invocation from repo root had only a path error; corrected cwd and completed the actual audit.
- `scripts/formal_tools.py index`: exit 0, one changed entry. Latest lint: exit 1, eight unrelated unreachable modules: RHTower.WeilWorkQuantizationRadialContour, WeilWorkQuantizationRadialGrowth, WeilWorkSettledPhaseMellinTrace; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No WP02 finding. Owned whitespace checks clean.

- Exact-source `/tmp/wp02-cycle6-axioms.lean`: exit 0; all four public capstones report only propext, Classical.choice, Quot.sound. All owned build/search processes completed. Owned temporary inputs and diagnostic outputs cleaned after this record. No numerical jobs, full/umbrella builds, heartbeat changes, commits, or pushes.

## Cycle 7: exact finite realization audit

- Current uniform-truncation capstone and all four umbrella imports revalidated. Deep search for exact finite matched realization completed without partial flags; source arguments return the existing RH receiver and tail lower envelope, not the quantitative realization theorem.
- Primary source refresh: [Groskin, finite Guinand–Weil dictionary, v3](https://arxiv.org/html/2607.02828), abstract and finite-dictionary/tail organization inspected. Its Galerkin-to-zero-side identity and archimedean cutoff correction concern a different truncation from the literal exposing-ray residual construction here. No external theorem or computation is used as an unproved premise, and no exhaustive novelty claim is made.
- Necessary own dependencies compiled individually to cache: `WeilWorkExposingRayUniformTruncation.lean` and `WeilWorkExposingRayTailAsymptotic.lean`, each with `lake --old env lean -o ...`; both exit 0. No full or umbrella build.

- Complete exact-source scratch `/tmp/wp02-cycle7-proof.lean`: exit 0 without warnings. Public repair, at_cutoff, and natural_aperture use only propext, Classical.choice, Quot.sound. Final installed command `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayFiniteRealization.lean`: exit 0, no warnings. All checks ran in foreground, one own Lean process at a time.
- Latest lint: exit 1 on eight unrelated unreachable modules: RHTower.WeilWorkDeficitProjection, WeilWorkHigherDenominatorPoissonBoundary, WeilWorkSettledPhaseThetaTrace; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No WP02 module flagged.
- Opposite-ray and cone-uniqueness deep searches completed without partial flags. The inspected cone results require exposure equality or coefficient order, so they do not close the next candidate. OPPOSITE-RAY-CONJECTURE.md records the exact statement and first unpaid source-production step. No conditional receiver added.

## Cycle 8 — opposite-ray attack and polar-leakage survivor

- Revalidated `ExposingRayRealization.natural_aperture` and all five owned umbrella imports.
- Deep corpus searches: opposite exposing trace; cone uniqueness and critical-zero support; negative archimedean polar tests; far polar correction leakage; logarithmic sampling. All five returned `partial=false`, no search errors. Coverage snapshot had 68,382 indexed files, with substantial source-only/stale compiler metadata; applicability is checked in Lean separately. Candidate lemmas, source arguments, proof ideas and proposed ingredient sets were inspected. The proposed ingredient sets did not prove the missing analytic hypotheses.
- Exact sources inspected: `WeilConeCriticalZeroCarriedRigidity` (support premise indispensable), `WeilFullConeNearNullPositiveDefinite` (positive definiteness does not establish vanishing), `WeilNullPotentialSignPartRigidity` (one sign part requires a block bound), STATUS MUST-818/CANNOT-496, and bohr-route-detection row 71 (near-null uniqueness reduction already audited). No cone nonemptiness or uniqueness assumed.
- `WeilPositivitySparseWeightsObstruction` already contains the actual far-polar source, its complete two-window cosine formula, and negative limiting-energy estimate. `WeilSymbolMertensExpansion.integral_normSq_paperFT_mul_cos_eq` fixes the factor of two in atomCoeff. `WeilPositivitySummableWeightsObstruction` supplies the autocorrelation lower bound and linear drop estimate. These are prior results, not new contributions.
- New paper candidate: full weighted absolute atom budget is bounded above and below by positive constant multiples of X exp(X). The second window near exp(2X) dominates; keeping only the first window gives the wrong scale. See POLAR-LEAKAGE-PROOF.md.
- External primary sources opened on 2026-10-07: Connes–Consani, https://arxiv.org/abs/2006.13771; Suzuki, https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms.12785 (RH criteria and partial unconditional results); Kim et al., https://arxiv.org/abs/2607.24830v3 (2026-09-28 revision, abstract explicitly disclaims an RH proof). These do not supply an opposite-ray producer. Exact-mechanism search did not locate this repair-budget estimate; that is not an exhaustive novelty claim. No numerical methods from these sources used.
- Anti-theatre: opposite-ray production remains OPEN. A uniqueness reformulation is REDISCOVERED. The leakage estimate is a concrete analytic route obstruction and quantitative survivor, not a universal lower bound and not a lower bound on arbitrary coherent repair energies.

### Cycle 8 completed verification

- `lake --old env lean /tmp/wp02_cycle8_leakage.lean`: exit 0, no warnings. Four axiom audits (`trace_eq`, `negative_energy_and_uniform_trace`, `budget_bounds`, `matchingBudget_lower`) all return exactly `[propext, Classical.choice, Quot.sound]`.
- Final audit: `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayPolarLeakage.lean`, cwd formal, exit 0, no warnings. New leaf has 358 lines. Wired beside the five earlier owned leaves. No full or umbrella build.
- `scripts/formal_tools.py lint`: exit 1, no WP02 finding. Ten unrelated unreachable modules at this snapshot: RHTower.WeilWorkDeficitZeroTransport, WeilWorkHigherDenominatorAxisPolynomial, WeilWorkHigherDenominatorLogMoments, WeilWorkSettledPhaseAbelRigidity, WeilWorkSingularArithmeticReciprocalMeanSquare; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. Existing large-file warnings. Lint was repeated once to capture stderr diagnostics without truncation.
- `scripts/formal_tools.py index`: exit 0; refreshed API/gaps/overview and two changed index entries.
- Scoped whitespace audit passed; new leaf has no trailing whitespace. No heartbeat changes, numerical jobs, new axioms, or commits/push.
- A mistaken installation working-directory prefix failed before writing a project file; corrected using absolute paths. The final installed audit above is authoritative.

## Cycle 9: finite coherent completion

- Corpus searches audited compact spectral factorization, Fejer–Riesz/polar root allocation, continuous completion/quadrature, and positive discrete Green filters. These searches returned useful source hits but were partial because semantic/decomposition deadlines expired. Candidate lemmas, source arguments, proof ideas, ingredient sets and source/compiler coverage were inspected; no absence or exhaustive novelty claim is made. Exact source search of every `farPolarTest` use found the existing sparse-weight source and the owned leakage module, without an existing coherent producer among those uses.
- Primary source inspected: Wayne Lawton, *Note on Spectral Factorization Results of Krein and Levin*, [arXiv:2104.08917](https://arxiv.org/abs/2104.08917), including Lemma 5 in the full text. Compact spectral factorization is classical; allocating both polar zeros and preserving the required regularity are separate obligations. The selected finite geometric/variance proof uses no external factorization theorem as a premise.
- Actual Fejer profile uses `Real.smoothTransition`; its existing C2 statement is not an intrinsic smoothness limit. Selected construction only needs the existing C2 interface.
- Paper construction was completed before Lean in COHERENT-COMPLETION-PROOF.md. Fourier mean, translated polar support, spectral variance, uniform filter-mass bound, exact energy identity and full atom identity have compiled at default heartbeat limits. Full capstone audit is still pending at this checkpoint.
- Follow-up small-aperture search returned `partial=true` (decomposition deadline), with complete file inventory but substantial source-only/stale compiler metadata. All 20 candidate lemmas and 20 source arguments were inspected. `CCMRestrictedWeilPolarGroundState.exists_small_aperture_polarGroundEnergy_pos` and `WeilPrimeFreeFamily.exists_small_aperture_primeFree_energy_pos` are existing results. Their unspecified small-aperture threshold does not automatically establish a sign at the selected aperture 17/50+s. No zero-cost limit follows from the new bounded-cost proof.


### Cycle 9 completed formal verification

- Full exact-source scratch audit: exit 0, no warnings. `#print axioms RHTower.ExposingRayCompletion.bounded_coherent_completion` reports only `[propext, Classical.choice, Quot.sound]`.
- Final installed command, cwd formal: `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayCoherentCompletion.lean`, exit 0, no warnings. The installed import was narrowed from WeilPolarConeExposedDuality to the definition-bearing WeilPositivityPrimeBlindDuality; the complete final audit verifies this smaller dependency choice. No theorem body changed after the axiom audit.
- 478-line leaf wired beside the six prior owned leaves. Scoped `git diff --check` passed; no heartbeat changes, numerical jobs, added axioms or full/umbrella builds.
- Latest `scripts/formal_tools.py lint`: exit 1. Six unrelated unreachable modules: RHTower.WeilWorkSettledPhaseCanonicalDisorder; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No WP02 finding; unrelated files preserved.
- `scripts/formal_tools.py index`: exit 0, one changed entry; generated API/gaps/overview refreshed. Final scoped whitespace audit clean. New source has no trailing whitespace or prohibited declarations/options.

## Cycle 10: uniform small-shift tail audit

- Corpus-first audits covered cone uniqueness, the small-aperture gap, polar derivative tails, and the compact Green identity. The cone, polar-tail and Green searches were non-partial. The small-aperture search was partial (source retrieval interrupted); the current frontier map and direct source supplied the stronger exact `one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo` result. Generic retrieval did not define the frontier.
- A subsequent broad Green/coherent-residual deep query was partial (`semantic_retrieval`, local runtime deadline). All 20 candidate lemmas and 20 source arguments were inspected. Its proposed ingredient set joined unrelated finite-graph Green and xi-zero-coordinate objects; it did not prove an exposing-ray estimate. A query containing the exact small-aperture ground theorem and farPolarTest then completed non-partially and returned both relevant direct parents. Coverage snapshots had about 68,400 inventoried files, but mostly pending/stale/source-only compiler metadata. No absence claim or blanket applicability assumption.
- External primary audit: [Csordas, arXiv:1309.0055v2](https://arxiv.org/html/1309.0055), including definitions and Theorems 3.2–3.7, supplies classical autocorrelation/positive-definite and admissible-kernel context. Those inspected statements do not supply the literal uniform small-polar-shift tail bound proved here. Also checked the abstract of [Planat–Sole, arXiv:2608.19160](https://arxiv.org/abs/2608.19160); its second-level concavity work is not a WP02 lower-energy producer. No numerical component used. External scientific novelty remains unestablished.
- The actual differential source F=(D²-1/4)Phi is represented by the full cusp series, whose degree-four polynomial has leading coefficient 16*pi^4. Its global upper envelope and eventual lower envelope are proved analytically, retaining the infinite sum. A common signed-autocorrelation estimate integrates the negative parts explicitly; no positivity is presumed.
- Exact finite-interval Green identity passes through normalized positive averages. The shift-dependent total Green weight cancels before envelope comparison; this is what makes the threshold uniform down to c=0. The final quantitative target has a quartic c^4 prefactor, not a falsely uniform positive constant as c tends to zero.
- Paper proof and normalized-transfer addendum: POLAR-UNIFORM-TAIL-PROOF.md. Complete final Lean verification is recorded separately below when finished.

### Cycle 10 verification checkpoint

- Complete 700-line scratch exits 0 without warnings. Seven exact capstone axiom audits report only propext/Classical.choice/Quot.sound: differential-source lower and upper bounds, signed differential-autocorrelation lower bound, exact Green identity, common negative source tail, common positive polar autocorrelation tail, and uniform quartic lower bound. No sorryAx in any successful capstone audit.
- Installed `WeilWorkExposingRayUniformPolarTail.lean` (707 lines), with identical proof bodies and a scope header, into the RHTower umbrella. No numerical experiment, heartbeat increase, full build or umbrella build. The final installed-source process is still pending at this checkpoint.
- `scripts/formal_tools.py lint`: exit 1 with fifteen unrelated unreachable modules, none WP02. RHTower: WeilWorkHigherDenominatorFinitePoleMellin, WeilWorkHigherDenominatorQuotientMellin, WeilWorkHigherDenominatorThetaDefect, WeilWorkPBAPCriticalCoefficients, WeilWorkPBAPCriticalDatum, WeilWorkPBAPCriticalKernel, WeilWorkPBAPCriticalLaplace, WeilWorkPBAPCriticalResonator, WeilWorkPBAPCriticalWindow, WeilWorkQuantizationPowerRigidity. HTGeometry: ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. Existing large-file warnings remain. Unrelated files preserved; no assertion these findings predated this session.

Cycle 10 final verification: `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayUniformPolarTail.lean` exits 0 with no warnings. Installed proof bodies match the successful seven-capstone scratch audit; only the module header and removal of scratch `#print axioms` differ. Index exits 0 (five changed entries, zero removed); generated API/gaps/overview refreshed. All eight umbrella imports verified. Owned source and scoped tracked-file whitespace checks clean. Main WP02 receiver remains unproved; no goal-completion claim.

## Cycle 11: refinement-invariant coherent gap

- Fresh corpus searches covered the C2/CCM bridge, zero-frequency finite geometric multiplier, small-aperture source gap, and possible local-seed capacity extension. Available candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. Refinement query partial due semantic timeout and malformed judge output; next-source query partial due reranking deadline. Inventories complete (68,446 and 68,449 files), compiler applicability mostly source-only/stale, background freshness incomplete. No absence or novelty claim.
- Exact parents verified in source: `one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo`, `ccmRestrictedWeilSourceQuadratic_halfLogTwo_eq`, weighted CCM support-kernel definition, Fourier Plancherel compatibility, actual `flatBump_eq_one`, and the owned finite `geometric_multiplier`/`energy_identity`. The earlier smooth-core admission needs C-infinity, so the literal C2 admission is proved directly.
- Primary context refreshed: [Suzuki, Weil’s quadratic form via the screw function, v3](https://arxiv.org/abs/2606.09096), 23 September 2026. No external numerical certificate used; no literature-level novelty claim.
- Full bridge/short-source scratch exits 0 with no warnings. `c2_halfLogTwo_coercivity` and `short_source_energy_floor` each report only propext/Classical.choice/Quot.sound. One support-expression elaboration timeout was resolved using the existing MemLp interface, with default heartbeat limit unchanged. No mathematical assumption was added.
- Installed ninth owned leaf `WeilWorkExposingRayCoherentGap.lean`; umbrella wired. Necessary leaf cache generation and the exact completion-capstone audit are in progress; final installed verification is not yet claimed.

- Latest formal lint exits 1 with 18 unrelated reachability findings and no WP02 finding. Exact modules: `GaloisForLFunctions.RHTower.WeilPaperCauchyDeficitSampling`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalAbel`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalBoundary`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalCoefficients`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalDatum`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalDensityLaplace`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalKernel`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalLaplace`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalResidue`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalResonator`, `GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalWindow`, `GaloisForLFunctions.RHTower.WeilWorkQuantizationQuietScales`, `GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolePerron`, `GaloisForLFunctions.HTGeometry.ApertureConeCalculus`, `GaloisForLFunctions.HTGeometry.ApertureConeWinding`, `GaloisForLFunctions.HTGeometry.ApertureLogTranslation`, `GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal`, `GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra`. Existing large-file warnings remain. Unrelated files preserved.
- Full completion scratch passes without warnings. `mass_defect_identity`, `geometric_completion_energy_floor`, `geometric_completion_uniform_positive_floor` and `geometric_completion_fixed_step_gap` use only standard three axioms. The positive threshold is arbitrary X0>0; the macroscopic X0=4 and original compact-step statements are both covered.
- Scoped whitespace audit clean; neither edited Lean leaf contains prohibited declarations, proof holes, decision computations or heartbeat/recursion-limit overrides. Final cache audit refreshes only the changed target leaf; no dependency/umbrella/full build.

- Both final installed sources passed in foreground with `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean GaloisForLFunctions/RHTower/<leaf>.lean`, exit 0, no warnings. Leaves: WeilWorkExposingRayCoherentGap and WeilWorkExposingRayCoherentCompletion. The target-only output refresh leaves no stale owned completion cache and performs no dependency build. The 550-line completion body matches the successfully audited scratch exactly.
- `scripts/formal_tools.py index`: exit 0, two changed entries; generated API/gaps/overview refreshed. Imported-cache axiom audit passed for all eight new public theorems, using only a /tmp scratch file; each has exactly propext/Classical.choice/Quot.sound.

## Cycle 12: unequal local seeds and literal Riemann capacity

- Fresh capacity deep query completed `partial=false`, no errors, inventory 68,462/68,462 files. All candidate lemmas, source arguments and proposed ingredient sets were inspected. Compiler metadata remains predominantly pending/stale; background refresh was incomplete. Exact source applicability was verified in Lean. The generated equal-modulus variance/Fourier recipe did not establish the unequal-seed result.
- Actual parents: `ExposingRayCoherentGap.c2_halfLogTwo_coercivity`, `WeilSpectral.norm_paperFT_real_le`, `paperFT_translate'`, `paperFT_polarRiemannDifference`, `bulkCutoff_eq_one`, and strict positivity/compact support of the actual truncated Riemann kernel. Translation/polar admission and every signed-symbol integral were proved explicitly.
- Primary context rechecked on 2026-10-07: [Suzuki v3, 23 September 2026](https://arxiv.org/abs/2606.09096) and [Connes–Consani](https://arxiv.org/abs/2006.13771). No numerical method or external theorem was imported as an unproved premise. Generic finite variance and Cauchy–Schwarz are classical; external novelty is unestablished.
- Full `/tmp/wp02_cycle12_capacity.lean` scratch audit exits 0 without warnings. Six audited capstones, including the literal unit-shift source and full finite exposing mixture, use exactly propext/Classical.choice/Quot.sound. Earlier elaboration failures concerned integral-expression association and finite-sum coefficient inference; explicit types/algebra resolved them with default heartbeat limits.
- Installed 389-line `WeilWorkExposingRayLocalCapacity.lean`, wired as the tenth owned leaf. Proof bodies match the successful scratch exactly. Final leaf/cache audit is in progress at this checkpoint. No full/umbrella build, numerical job, decision computation, new axiom or heartbeat/recursion override.
- `scripts/formal_tools.py lint`: exit 1, seven unrelated reachability findings, no WP02 finding. Modules: `GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonQuarter`, `GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorWeightedQuarter`, `GaloisForLFunctions.HTGeometry.ApertureConeCalculus`, `GaloisForLFunctions.HTGeometry.ApertureConeWinding`, `GaloisForLFunctions.HTGeometry.ApertureLogTranslation`, `GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal`, `GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra`. Existing large-file warnings remain; unrelated work preserved.
- Next-source search on discrete blind completion was partial (local semantic/reranking deadlines), with 68,468-file complete inventory and incomplete compiler freshness. All 20 candidates, 20 arguments, two proof ideas and the ingredient set inspected. Its proposed pole-residual pairing does not cancel integer traces. Lexical rephrase recovered prime-blind duality and the existing dilation-free measure bound; neither produces the unpaid signed floor.
- Common-profile lattice search completed non-partial, inventory 68,469 complete, compiler/background freshness partial. All returned candidates/arguments inspected. Direct source confirmed `WeilWorkDeficitGeometricRadicalObstruction.logValue_geometric_radical_eq_zero_iff`: coherent translates of a sufficiently broad truncated Riemann kernel on an integer-base logarithmic grid already cannot cancel all base powers. A further lattice nonexistence receiver alone would be redundant. The pending candidate must supply its exact sampled polar mass identity for the actual narrow Fejer profile and arbitrary real spacing; no novelty claim or Lean implementation for that candidate yet.

Cycle 12 final installed audit: `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkExposingRayLocalCapacity.olean GaloisForLFunctions/RHTower/WeilWorkExposingRayLocalCapacity.lean`, cwd formal, exits 0 with no warnings. Only the target cache was refreshed. Installed proof bodies match the successful scratch exactly. All ten owned imports and scoped whitespace/prohibited-declaration checks pass. Imported-cache axiom audit for all nine public theorems is in progress; main WP02 receiver remains OPEN.

Cycle 12 closure: imported-cache axiom audit exits 0 for ALL nine public theorems, each depending exactly on propext/Classical.choice/Quot.sound. `scripts/formal_tools.py index` exits 0, two changed entries and zero removed; generated API/gaps/overview refreshed. Final scoped whitespace audit is clean. All owned Lean/search/lint/index processes have exited. No claim of universal positivity, cone nonemptiness, or RH.

## Cycle 13: exact rounded-sample mass and stability

- Revalidated cycle12 literal Riemann-source/full-mixture capacity, ten umbrella imports and the exact universal receiver at WeilPolarConeExposedDuality:604. Mission remains its unconditional lower inequality, not this restricted family.
- Fresh targeted query `Fejer polar translated packet integer sampling autocorrelation mass`, deep/Weil/180s, returned partial=false and no errors. Inventory 68,474/68,474, compiler mostly pending/stale, background refresh incomplete. All 20 candidate lemmas, 20 source arguments and proposed ingredient sets inspected. It recovered actual Fejer, Gram-packet repair and owned source results; generated truncation-error recipe does not prove sampled mass recovery. No absence or exhaustive novelty claim.
- Direct parents: exact `WeilSpectral.weilTest_sum_transl`; actual fejerTest support/correlation and its analytic drop bound; actual Fourier translation; continuous polar cancellation. The existing geometric radical outer-support/injective power-sampling theorem was rechecked as prior research. Primary context reopened [Connes–Consani](https://arxiv.org/abs/2006.13771); broad external mechanism search returned no useful matching primary theorem. No external result or numerical method imported as a premise; external scientific novelty unestablished.
- Dependency-closed paper argument written first in LATTICE-REPAIR-PROOF.md. Exact defect identity retains arbitrary complex coefficients. The actual profile's half-pole multiplier is a strictly positive exponential-weighted integral, so one half-pole suffices for the polar specialization. This strengthening was sent back through the paper audit before the Lean specialization.
- Current scratch /tmp/wp02_cycle13_lattice.lean proves analytic ceiling/log rounding, every separated correlation window, complete covariance/atom formula, exact finite pole pairing, mass recovery, weighted stability and classification. One final complex-exponential rewrite correction is under full scratch/axiom audit at this checkpoint. No project leaf installed yet; no claim of final formal closure yet.
- Follow-up query on discrete exponential polar moments and geometric Riemann translates completed non-partial, inventory 68,482/68,482, compiler/background freshness incomplete. All candidates, arguments and proposed ingredient sets inspected. It recovered the actual sampled convolution in WeilWorkDeficitGeometricRadicalObstruction. GEOMETRIC-POLAR-MASS-CONJECTURE.md records the next candidate: a physical-mass law at integer-base powers retaining ALL overlaps of the literal Riemann profile. Its value beyond the known no-go remains to be audited; no new Lean for it.

Cycle 13 formal closure: full scratch exits 0 without warnings; all seven public theorems have exactly `[propext, Classical.choice, Quot.sound]`. Installed 440-line leaf `WeilWorkExposingRayLatticeMass.lean`, namespace ExposingRayLattice, as the eleventh owned umbrella import. Final foreground command `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkExposingRayLatticeMass.olean GaloisForLFunctions/RHTower/WeilWorkExposingRayLatticeMass.lean`, cwd formal, exits 0 without warnings. Only this target cache refreshed; installed proof bodies match successful scratch exactly. No full or umbrella build.

Formal lint exits 1 with ten unrelated reachability findings and no WP02 finding. Exact modules: `GaloisForLFunctions.RHTower.WeilPaperGammaEnergy`, `GaloisForLFunctions.RHTower.WeilWorkDeficitRepairCost`, `GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonAnalytic`, `GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorSpatialDefect`, `GaloisForLFunctions.RHTower.WeilWorkPBAPJointConvex`, `GaloisForLFunctions.HTGeometry.ApertureConeCalculus`, `GaloisForLFunctions.HTGeometry.ApertureConeWinding`, `GaloisForLFunctions.HTGeometry.ApertureLogTranslation`, `GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal`, `GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra`. Existing large-file warnings remain; unrelated work preserved. Scoped whitespace and prohibited-declaration/options checks clean.

Cycle 13 index/cleanup checkpoint: `scripts/formal_tools.py index` exits 0 (zero changed/removed entries at this snapshot), generated API/gaps/overview refreshed. All eleven owned umbrella imports verified; final scoped whitespace check clean. Every owned Lean/search/lint/index process has exited. Main goal remains ACTIVE, with no RH or cone-nonemptiness claim.

## Cycle 14: source utility audit and differential parity

- Revalidated cycle13 capstones/eleven umbrella imports and the exact unchanged WP02 receiver. Overlapping geometric mass deferred after checking the actual Fourier translation multiplier: repeated half-pole zeros are an extra infinite source restriction. Its finite-convolution norm identity remains a paper diagnostic, not an energy estimate.
- Two broad deep searches were partial (reranking worker disconnection/Qdrant deadline): complete 68,489-file inventory, predominantly pending/stale compiler data, incomplete background refresh. Candidate/source statements, proof excerpts and proposed ingredient sets inspected. Generated recipes confuse lower tail bounds with the universal signed inequality and are not proofs.
- Targeted all-order derivative search completed non-partial with 68,491-file inventory, also predominantly pending compiler metadata/background refresh incomplete. It recovered the exact cusp-series source, k=0 tail theorem, pole-cancelling derivatives and transform/radical identities. Its evenness/decay ingredient set does not close the all-order signed tail. No absence or scientific novelty claim.
- Primary external audit opened Connes–Consani's 2021 paper, https://alainconnes.org/wp-content/uploads/Selecta.pdf, pp.1–2: exact convolution/polar conventions and the distinction between archimedean-window and full finite-prime positivity. Follow-up derivative/autocorrelation searches returned no applicable primary tail theorem; this is not a novelty verdict.
- Complete paper proof recorded before code in DIFFERENTIAL-PARITY-PROOF.md. /tmp/wp02_cycle14_parity.lean contains the new all-order source/positive-cusp-envelope/signed-convolution proof and literal Fourier/pole/radical identities. No installed new leaf yet. Existing owned UniformPolarTail exposes its already-proved general integrability/error-absorption helpers for reuse; target-cache audit currently running, no heartbeat or full build.
