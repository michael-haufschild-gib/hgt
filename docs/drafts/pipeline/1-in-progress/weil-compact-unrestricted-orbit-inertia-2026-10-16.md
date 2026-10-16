# Compact polar realization of unrestricted finite Xi orbit inertia

Status: paper argument completed; formalization started. Uncounted under the
100-theorem goal until exact statement, builds, axioms, and significance audit.

## Target and significance test

For any finite family of distinct nonreal centered-Xi symmetry orbits, produce
a complex subspace of actual compact C2 tests of the same dimension, with both
polar Fourier samples exactly zero and strictly negative complete Weil form.
One finite support interval and one positive L2-relative negative margin work
for the entire subspace, hence for every larger support window. No spacing,
isolation, height, visibility, or simplicity premise is allowed. The family
consists of actual Xi zeros; the theorem does not assert off-line zeros exist.

The inspected finite-level lower bounds still impose separation and visibility
conditions, and one construction loses two dimensions when enforcing poles.
Removing those restrictions would give unrestricted finite orbit realization,
not a new RH equivalence. A routine restatement of existing cardinal planes or
continued-Cauchy source transport will not be counted.

## Source evidence inspected

- `CHMDCardinalGraphGeometry.lean`: actual original-graph cardinal frames;
  complete multiplicity removal, primitive status, exact positive/negative
  form, and zero cross-pairing within one nonreal orbit.
- `CHMDUniversalCardinalPairing.lean`: pairings with every graph vector are
  literal cosine samples; readouts outside the selected orbit vanish.
- `CHMDBirmanSchwingerBound.lean`: continuous bounded Weil bilinear form;
  negative definiteness survives finite compact-core perturbation. Its
  existing approximation theorem does not preserve exact polar samples.
- `CHMDPolarPlane.lean`: actual independent polar graph vectors. Neither a
  compact right inverse nor constrained compact-core density is yet audited.
- `ZetaWeilFiniteLevelInertia.lean`: `weilNegIndex` uses complex C2 compact
  tests with both exact polar cancellations and an L2-relative negative gap.
  Its lower theorem assumes separated isolated visible pairs and loses two
  dimensions. `WeilNyquistInertia.lean` improves this under further explicit
  window/depth/spacing conditions.
- `XiWeilMultiOrbitSourceInertia.lean`: exact negative diagonal transport to
  continued-Cauchy prime-Gamma source packets, explicitly not semilocal
  compact-support realization.
- `HTGeometry/DenseCoreHyperplane.lean`: explicit rank-one correction of a
  dense algebraic core using a normalized core vector. A finite-constraint
  extension may supply the missing compact correction.
- `CHMDTranslatedCardinalDetection.lean`: small translated cardinal sources
  recover full Fourier samples. A possible second parity direction per orbit
  requires a separate signed-form audit; do not assume or count it.

Whole-corpus hybrid searches completed with usable Lean hits, `partial=false`,
stale coverage snapshot warnings, and unavailable semantic-coverage metrics.
Only Lean results were used as mathematical evidence. No web or numerical work.

## Proposed proof, with outstanding audits explicit

1. Choose one imaginary cardinal graph vector for each distinct nonreal
   symmetry orbit. Universal pairings give an exact negative diagonal across
   the family. Full multiplicity is retained; no simple-zero premise occurs.
2. Put all desired finite samples, including both poles, into one continuous
   finite-dimensional real evaluation map P. The compact C2 core D is a dense
   linear subspace of the original graph. P(D) is a linear subspace of a
   finite-dimensional space, hence closed; density gives P(D)=P(H). Choose a
   linear right section S with image in D, continuous because its domain is
   finite-dimensional. Correct any approximant d by
   `d - S(P(d)-P(p))`. This remains in D, matches all selected samples of p,
   and converges to p in the complete graph norm. This general proof needs
   toolchain/API verification and exact source-map instantiation.
3. Apply that construction simultaneously to the finite negative family.
   Continuity of the signed Weil form preserves a strict negative gap on its
   real coefficient sphere. Exact polar cancellation avoids dimension loss.
4. Audit real-source polarization and complexify the negative family: the
   complex Weil quadratic form should split into the real and imaginary
   coefficient energies. This identity must be checked, not presumed from
   pointwise real-valuedness.
5. A finite union of compact supports gives a common interval. A bound on the
   L2 norm of finite combinations converts the coefficient gap into a positive
   L2-relative margin. Negative definiteness proves linear independence.
6. If exporting an inequality for `weilNegIndex`, establish the required
   boundedness of its defining set before using `le_csSup`; natural-number
   `sSup` is not automatically monotone for an unbounded set. The actual
   subspace existence theorem is primary and avoids this definitional trap.

## Attacks and limits

- Exact zeros at every other Xi zero are impossible for a nonzero compact
  source of finite exponential type. Only a finite prescribed sample set is
  preserved; the full signed energy is controlled through graph convergence.
- Do not infer jump-domain admission from uniform/L2 approximation. All
  approximants and limits must live in the already proved full CHMD graph.
- Nonquantitative existence does not retain the explicit support budgets of
  the Nyquist theorem. No effective threshold is claimed.
- This is a new candidate, not a completed paper proof or counted theorem.

## Plan

1. Finish local novelty and exact-hypothesis audit.
2. Prove finite constrained compact-core density and the precise orbit theorem
   on paper; attack symmetry, dimension, domain, and support claims.
3. Formalize only the dependency-closed statement in new owned leaf files.
4. One targeted Lean process at a time; audit all public axioms, wiring, lint,
   significance, and source hashes before any count change.

## Paper-proof closure checkpoint, 2026-10-17

The full compact C2 core is already a linear subspace and dense in the exact
maximal graph (`CHMDFullJumpCoreDensity.compactTests` and `dense_compactTests`).
Both polar readouts are continuous (`CHMDStripFourierReadout`). The real and
imaginary Weil-energy split follows from the arithmetic explicit formula and
`re_weilFullFunctional_split`, as already used in `CHMDBoundStateInertia`.
Thus no remaining analytic admission premise is needed in steps 1--5 above.

Normalize each imaginary cardinal vector by the inverse square root of its
strictly positive orbit mass. Its signed Gram is exactly minus identity:
diagonal follows from `CardinalGraphFrame.im_energy`, off-diagonal from the
universal pairing and zero outside-orbit readouts. Choose the finite observation
map to include both polar points and all desired finite Xi samples. Corrected
compact approximants retain those observations exactly. Their Gram matrices
converge entrywise to minus identity. Finite matrix perturbation gives the
uniform bound `Q(c) <= -||c||^2/2` for one sufficiently accurate common stage.
Here the coefficient norm is any chosen fixed finite-dimensional norm, with
the bound adjusted by norm equivalence if necessary.

The selected compact representatives have a common finite support interval.
Their complex linear combination map into ordinary L2 is bounded, say by C.
Taking `epsilon = 1/(4*(C^2+1))` converts the coefficient negative gap into a
strict L2-relative gap for every nonzero coefficient vector. Exact polar
cancellation identifies that signed Gram form with the complete Weil form;
the real/imaginary split proves the complex identity. Negative definiteness
implies linear independence. All larger support windows contain the same
subspace. This proves the primary existence statement without using sSup.

New supporting leaf started:
`formal/GaloisForLFunctions/HTGeometry/DenseCoreFiniteConstraints.lean`.
Its two lemmas concern finite image equality and norm approximation with exact
finite observations. They are bookkeeping for this contribution, never counts.
Toolchain name probes exposed two guessed helper names and unresolved universe
levels in unused polymorphic `have` probes; those are being corrected. No
successful build of this new supporting leaf is claimed yet.

The frontier-map report is read-only by user instruction; it is not an output
of this work. All other concurrent worktree edits remain outside this candidate.

## Formalization checkpoint, 2026-10-17

`DenseCoreFiniteConstraints.lean` passed its targeted Lean build with exit 0
and an empty log. The exact finite-observation correction is now verified.

Four downstream leaves are drafted, not yet verified:

- `CHMDCompactOrbitInertia.lean`: normalized cardinal Gram, exact-polar compact
  approximation, and the retained negative coefficient gap.
- `CHMDCompactTestSynthesis.lean`: literal complete Weil form of a finite
  complex combination equals the signed original-graph Gram.
- `WeilCompactNegativeSubspace.lean`: the synthesis range has the full complex
  dimension, common compact interval, and a strict ordinary-L2-relative gap.
- `WeilCompactOrbitInertia.lean`: the primary unrestricted Xi orbit theorem,
  including the same subspace in every larger window.

The first compact-Gram build exposed a missing strip-readout import and
function-versus-matrix notation. Both are corrected; the next targeted build
is still running. No axiom audit, umbrella wiring, or count change yet.

A fresh whole-corpus hybrid search returned `partial=false`, 73,035 indexed
files and 1,081,325 declarations, with compiler coverage still a mixed/stale
snapshot. Both `candidate_lemmas` and `source_arguments` were inspected.
Direct comparison confirms that `WeilNyquistInertia` already avoids isolation
and polar dimension loss but still assumes height separation and an explicit
window/tail budget. The candidate's new claim is unrestricted finite-family
compact realization; the support threshold is non-effective. Its coefficient
gap-to-subspace helper is not itself a new counted research contribution.

The revised compact-Gram argument passed its portion of two combined scratch
checks; its final standalone leaf build is still pending. Those scratch runs
found coercion errors and default-heartbeat exhaustion in the downstream test
synthesis and support/L2 proof. The coercions are corrected, and the argument
is split into separate real/imaginary Weil, envelope, support, and L2 lemmas.
No heartbeat limit was increased. Another combined check is in progress.

Additional source comparison: `XiWeilCauchyCoreMultiplicity` already identifies
the fibrewise mean-zero annihilator of the Cauchy core, and
`XiWeilSpectralFoldIndexConservation` already classifies finite continued-Cauchy
negative blocks by distinct off-real spectral locations modulo conjugation.
Those observations are prior work, not new contributions. The present target
remains actual compact polar test realization. Its dimension is one per
selected fourfold Xi symmetry orbit; it does not claim the maximal index or
one independent direction per multiplicity copy.

`CHMDCompactOrbitInertia.lean` now has a final standalone targeted build with
exit 0 and empty log. The downstream synthesis leaf is building next. Verified
source hashes so far:

- Dense finite constraints:
  `64da85a6ad61667ad6b98245a0820e3a05b8d2b9534502e09762ce4c94522107`.
- Compact orbit Gram:
  `e7df0f59e4756fba579e229babcdf42e21a7c7fdf983b1b67f1061ee3823db01`.

Count remains unchanged pending the actual-test theorem and all remaining gates.

`CHMDCompactTestSynthesis.lean` also passed its final standalone targeted build
with exit 0 and empty log. Its source hash is
`844b7eb299a04b72824da066c2bc21ed351d07be8fe5097b780d37d2f1adace4`.
The support/L2 leaf's remaining default-heartbeat failure was localized to
elaboration of squared compact support through composition. Its proof now
uses the direct product-support lemma, with explicit function types; the
limit remains unchanged. The next standalone check is running.
