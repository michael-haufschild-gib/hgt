# WP05 evidence

## Corpus searches

All queries were run directly through `scripts/formal_tools.py research`, with JSON results inspected for declarations, candidate lemmas and source arguments. Coverage summaries are retained in `search-coverage.json`.

- `settled atomic phase --module Weil`: exact atomic/AP receiver found.
- `fractional mass power growth --module Weil`: existing sublinear-power, two-sided and mixed receivers found.
- `arithmetic phase settlement linear mass rational resonance --mode deep --budget-seconds 300`: no useful closing theorem; returned one ingredient set, no proof ideas. Broad semantic matches are not evidence of relevance.
- `cumulative phase counting bounded perturbation quantization --module Weil`: no lexical declarations; semantic hits were existing receivers and unrelated transport results.
- `Poisson lattice coth exponential sum`: Poisson summation machinery found; not pursued as a new RH mechanism.
- `sublinear variation linear Abelian twist logarithmic growth --module Weil`: partial result; semantic runtime deadline expired. No absence claim inferred.
- `phase transport chord cumulative atoms integral`: no exact packet estimate located; routine mechanism already described in settled-atomic module.
- `AbelianTwist radialError strip bound --module Weil`, `fractional atoms horizontal edge Herglotz weighted mass --module Weil`, and `atom horizontal contraction Herglotz singleton --module Weil`: supplemented by direct source searches and exact reads of the contour and horizontal-potential results.

Initial inventory: 68,275 files inventoried, no pending source files; compiler status mostly pending/stale; semantic coverage not measured. `partial=false` does not certify full semantic coverage or compiled validity. Normal background source indexing is active. No full index regeneration or umbrella build was requested or run.

## Exact internal sources

- `WeilConeSettledAtomicPhase.lean:61`: `vonMangoldt_and_riemannHypothesis_of_settled_atomic_phase`; exact Poisson representation and power-rate dyadic L1 hypothesis.
- Same module `:179`: AP receiver; not selected as active target.
- `WeilFractionalMassTailRigidity.lean:566`: strict `phaseSum` convention.
- `WeilAbelianTwistPowerRigidity.lean:685`: `fractional_mass_power_growth_rigidity`.
- `HamburgerAbelianTwistContour.lean:672`: `exists_norm_radialError_le_of_strip`; fixed exponent loss epsilon^(1-nu).
- `WeilAbelianTwistRigidity.lean:131`: `norm_setIntegral_layer_le_of_profile`.
- `WeilFullConeHorizontalPotential.lean:137`: exact horizontal log-potential identity.
- `WeilProducerReciprocalZetaAtomOrder.lean:135`: asymptotic radial atom order.
- `bohr-route-detection.md`, rows 35, 57, 59, 60 and 79: existing power wall, phase receivers and failed line-only degree argument.

These source reads establish interfaces, not a new compilation audit of all their imported dependencies. The new packet module imports only mathlib.

## External primary-source audit

- Andrew Booker, [L-functions as distributions](https://arxiv.org/pdf/1308.3067), Definition 1.3(A3): discreteness and all but finitely many integral masses are hypotheses. Its degree-one classification cannot establish WP05's missing atomicity/quantization.
- Thomas Oliver, [Notes on Low Degree L-Data](https://arxiv.org/html/1601.05009): adjacent classification framework; no producer of those missing hypotheses located.
- Nir Lev and Alexander Olevskii, [Fourier quasicrystals and discreteness of the diffraction spectrum](https://arxiv.org/abs/1512.08735): uniformly discrete support is assumed; not an atomicity theorem for arbitrary canonical Weil measures.
- Sergii Favorov, [Generalized Fourier quasicrystals and almost periodic sets](https://arxiv.org/abs/2308.07585): locally finite support and integer masses are inputs.

No novelty claim rests on a failed web search. No experimental or numerical computation was performed.

### Cycle 2 primary-source and corpus audit

- Jean-François Burnol, [Deux extensions de Théorèmes de Hamburger](https://arxiv.org/pdf/1106.4749), Theorem 1: global single-valued meromorphic continuation with finitely many poles is an input. It does not license fractional branch monodromy.
- Ghaith Hiary and Fadi Saraeb, [Functional Equations Characterize Dirichlet Characters](https://arxiv.org/pdf/2607.00332), Theorem 1.1: assumes periodic finite-order coefficients and functional equations for specified powers. Neither is supplied by our boundary phase lock.
- Kannan Soundararajan, [Moments of the Riemann zeta function](https://annals.math.princeton.edu/wp-content/uploads/annals-v170-n2-p17-p.pdf), Proposition and Corollary C: established polynomial-majorant method for Littlewood bounds under RH for zeta. The method here is not claimed new; the corpus already supplied its full-cone analogue.
- `WeilProducerLittlewoodBound.lean:232` explicitly adds `|lam(n)| <= kappa log n`. `WeilConeSoundararajanMoments.lean:820` assumes the Littlewood estimate as input. Neither supplies the coefficient-free statement.
- Source searches for atom-zero contour control, sublinear fractional density, mean-square producer control, uniform growth, Soundararajan bounds, and a deep transfer query were completed. No closing source-derived phase estimate was found. Metadata is retained in `cycle2-search-coverage.json`; incomplete semantic measurement and stale compiler snapshots are not treated as verified theorem coverage.

## Lean verification

- `/tmp/wp05-api.lean`: verified mathlib names against installed toolchain; final exit 0. Initial universe-inference errors in generic `have` checks were repaired by explicit universes.
- Initial packet-module audit found one addition-order mismatch and style warnings; repaired without raising heartbeats. Subsequent `lake env lean` exited 0 before the final two obstruction statements were added.
- `lake --old build +GaloisForLFunctions.RHTower.WeilWorkSettledPhasePackets:olean`: exit 0; new leaf built successfully (35 seconds reported). No umbrella target.
- Final `lake env lean GaloisForLFunctions/RHTower/WeilWorkSettledPhasePackets.lean`: exit 0, empty output, no warnings.
- `lake env lean /tmp/wp05-axioms.lean`: exit 0. All seven inspected capstones use exactly `[propext, Classical.choice, Quot.sound]`. Full output retained in `axioms.txt`; no added axiom, computational oracle, or heartbeat override.
- `git diff --check -- formal/GaloisForLFunctions/RHTower.lean`: exit 0. New files inspected for trailing whitespace; umbrella contains exactly one import of the new module.
- `scripts/formal_tools.py lint`: exit 1; 11 unreachable-module errors, all outside WP05. No error names `WeilWorkSettledPhasePackets`. Large-file warnings are pre-existing/shared-tree issues. This is not a clean global lint gate.
- Umbrella import added under the user's explicit requirement to wire finished modules; no unrelated umbrella edits made.

### Cycle 2 verification

- `lake --old build +GaloisForLFunctions.RHTower.WeilWorkSettledPhaseLittlewood:olean`: exit 0; new leaf reported built in 175 seconds. Dependency logs were replayed. No full or umbrella build requested.
- Final `lake env lean GaloisForLFunctions/RHTower/WeilWorkSettledPhaseLittlewood.lean`: exit 0, empty output. No source changes followed this audit.
- `lake env lean /tmp/wp05-cycle2-axioms.lean`: exit 0. Both new declarations and the reused Soundararajan source theorem have only `propext`, `Classical.choice`, `Quot.sound`. Installed mathlib API checks in the same scratch file passed. Output retained in `cycle2-axioms.txt`.
- The printed capstone type has only the assigned `hW : WeilPositiveFull lam` as source premise; positive C is included in the conclusion. No added coefficient, spectral or settlement hypothesis.
- `git diff --check -- formal/GaloisForLFunctions/RHTower.lean`: exit 0; new source has no trailing whitespace and exactly one umbrella import. Other agents' umbrella additions preserved.
- `scripts/formal_tools.py lint`: exit 1, seven unrelated unreachable modules. No WP05 module is named. Exact errors retained in `cycle2-lint-errors.txt`; global lint is not clean.
- No numerical experiments, heartbeat overrides, new axioms, commits, or pushes. Owned temporary search/audit files removed after evidence retention; owned foreground Lean processes completed.

### Cycle 3 corpus and proof audit

- Searches covered logarithmic phase disorder, arithmetic phase quantization,
  atomicity, producer moments and canonical boundary traces. Exact query and
  coverage metadata are retained in `cycle3-search-coverage.json`.
- The arithmetic-quantization query was partial after a Qdrant deadline; the
  atomicity query was partial after interrupted text/source retrieval. Available
  hits were used. Neither partial result supports an absence claim.
- `WeilConeSettledLockRigidity.lean:530` gives the pointwise producer comparison;
  `:715` supplies integrability and `:732` the weighted block receiver. These
  combine with the new source-wide Littlewood theorem to yield the obstruction.
- `WeilConeSettledAtomicPhase.lean` supplies the exact fractional product and
  reflection identity used for the actual strict-cutoff phase. Atomic
  representation and support assumptions remain visible in the new declaration.
- `WeilConeSoundararajanMoments.lean:896` and `:1024` retain both coefficient-size
  and rest-weight summability assumptions. Removing the Littlewood coefficient
  premise does not remove those independent inputs to the moment proof.
- For the next conjecture, `WeilProducerZetaQuotientBohrRecurrence.lean:358`
  provides a primitive for the actual source; `WeilProducerReciprocalZeta.lean:43`
  demonstrates `isExactOn_rightHalfPlane` with a normalized value. The canonical
  interval-phase limit is in `WeilWorkQuantizationBoundaryPhase.lean:62`.
  These are inspected source interfaces, not a completed trace/contour proof.

### Cycle 3 verification

- The new source passed `lake env lean` after scalar sign and rewriting repairs.
- `lake --old build +GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDisorder:olean`
  passed. Required dependencies were rebuilt; the new leaf took 6.6 seconds.
  The build requested only this leaf, not the RHTower umbrella or a full build.
- Global lint exited 1 with 13 unreachable modules outside WP05. Exact errors
  are retained in `cycle3-lint-errors.txt`. No WP05 error was reported.
- The umbrella has exactly one import of the new module. `git diff --check`
  passed; the source has no trailing whitespace. Other umbrella changes were
  preserved.
- `lake env lean /tmp/wp05-cycle3-axioms.lean` exited 0. All three new declarations
  have exactly `[propext, Classical.choice, Quot.sound]`. Printed types and axiom
  lists are retained in `cycle3-axioms.txt`. No assumed phase-rate premise appears.
- Source SHA-256 at the compiled/axiom audit:
  `4ca21a5e562827dcd4d1f8a379a649cf51f1c0cc9e123d24795f8126dcd64267`.
- Final `lake env lean GaloisForLFunctions/RHTower/WeilWorkSettledPhaseDisorder.lean`
  exited 0 against the rebuilt dependencies. Output contains one informational
  `ring_nf` suggestion at the exponential-cancellation proof, with no warning or
  error. Source hash is unchanged. No heartbeat override or new axiom was added.
- No empirical computation, full build, umbrella build, commit or push was run.
  Owned temporary search/audit files were removed after retaining the evidence;
  all owned foreground Lean and search processes completed.

### Cycle 4 evidence under audit

- Revalidated the unchanged cycle-3 source hash and reread the assigned WP05
  requirements. Main representation and settlement obligations remain open.
- Fresh corpus query `canonical producer boundary trace phase primitive` returned
  `partial=false`; its broad semantic matches did not supply the trace theorem.
  Direct source inspection supplied normalized half-plane exactness, conjugation,
  the canonical interval phase limit and the exact coefficient receiver.
- Gesztesy--Tsekanovskii, [On Matrix-Valued Herglotz Functions](https://arxiv.org/pdf/funct-an/9712004),
  equation (1.4) and Section 2, give the classical Stieltjes inversion mechanism
  with half endpoint masses. Boundary inversion is not a new method here. The
  proposed corpus contribution is the actual normalized Weil producer's trace
  and local L1 passage without atomicity or a support gap.
- `WeilHerglotzPhaseLockRigidity.lean:470` uses boundary continuity to invoke
  `HamburgerTwistedCriticalLine.lean:406`. Its two inverse-Mellin steps still
  require a genuine extension to the new trace. This extension has not been
  assumed or claimed proved.
- Installed API checks in `/tmp/wp05-cycle4-api.lean` passed after replacing an
  unavailable helper name. A scratch source audit exposed missing direct imports,
  a coefficient-normalization equality and real-module elaboration mismatches;
  these were repaired before the complete source audit. No heartbeat override.
- The complete local trace source audit exited 0 after four elaboration repairs.
  The source was then extended, after a new paper proof, to global L1 convergence;
  that stronger version still requires its final audit.
- Fresh query `critical line inverse Mellin measurable boundary trace local L1
  convergence` returned `partial=false`, no search errors. The snapshot reports
  stale and pending compiler entries, so absence of a theorem is not asserted.
  Its relevant hit is `HTGeometry.HamburgerCriticalLine:142`; direct inspection
  shows the continuity-dependent contour shift at :212. The even defect theorem
  `HamburgerCriticalLineEvenDefect:31` calls this inverse Mellin theorem twice.
- `WeilFractionalMassAtomicRigidity:582` derives the polynomial-times-Gamma
  right-edge decay from summability alone. `ZetaSpectrumAtomicSeries:531` and
  `CrystallineProducerRigidity:341` turn it into an integrable C/(1+y^2) bound.
  No atomic representation hypothesis occurs in these selected declarations.
- Deep query `shift a holomorphic contour to an almost everywhere boundary trace
  by dominated convergence without boundary continuity` returned `partial=false`
  with `coverage_snapshot_older_generation` and `semantic_coverage_unavailable`
  warnings. Candidate/source-argument lists and the proposed ingredient set were
  inspected. It found `HTGeometry.DecayingStripVerticalShift:22`, whose source
  supplies the interior shift directly. The proposed ingredient set is unverified;
  it is not a proof of the trace extension. Query/coverage metadata for all three
  cycle-4 searches is retained in `cycle4-search-coverage.json`.
- The canonical-measure identification query also returned `partial=false` with
  snapshot/semantic warnings. Inspected `WeilWorkHigherDenominatorMultiplicity:42`
  and :51: given full positivity for von Mangoldt, singleton masses equal natural
  zero multiplicities and every bounded interval has integer mass. Inspected
  `WeilConditionalConstantSignRigidity:481`: this measure is carried by critical
  ordinates. These support the proposed order of obligations after rigidity;
  they do not derive lambda=Lambda for an arbitrary source.

### Cycle 4 verification

- The global extension's first targeted build found one right-edge cast
  normalization mismatch; an explicit coordinate equality repaired it.
- `lake --old build +GaloisForLFunctions.RHTower.WeilWorkSettledPhaseTrace:olean`
  then exited 0. The repaired new leaf took 136 seconds. Required interval-kernel
  and interval-phase dependencies had rebuilt in the preceding attempt. The
  target was this leaf; no umbrella or full-project target was requested.
- The RHTower umbrella now contains exactly one import of this finished leaf.
  No other imports were removed. Source contains no heartbeat/recursion override,
  forbidden declaration, or trailing whitespace. Targeted `git diff --check`
  passed.
- Compiled source SHA-256:
  `5a47a5d09597bf4fdfff282bfefd2d96ddeb77ffb47e648dc645854f1d145ab7`.
- Final `lake env lean GaloisForLFunctions/RHTower/WeilWorkSettledPhaseTrace.lean`
  exited 0 with no diagnostics against the rebuilt dependencies.
- Global lint exited 1 with 12 unreachable modules outside WP05. No WP05 error
  was reported. Exact errors are retained in `cycle4-lint-errors.txt`.
- `lake env lean /tmp/wp05-cycle4-axioms.lean` exited 0. All nine audited
  declarations use exactly `[propext, Classical.choice, Quot.sound]`; their
  types and axiom lists are retained in `cycle4-axioms.txt`. The global trace
  theorem's only source input is the original full positivity hW.
- Source hash remained unchanged through the final source and axiom audits.
  No empirical computation, full/umbrella build, commit or push was run. All
  owned processes completed. Fourteen owned scratch/search/audit files were
  removed after retaining the evidence.
