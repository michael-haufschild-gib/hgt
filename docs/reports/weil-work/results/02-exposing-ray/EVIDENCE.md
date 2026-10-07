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
