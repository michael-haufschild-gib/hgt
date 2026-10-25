# Q-III: actual escape states and the Kronecker curve

- **ID:** q-iii-escape-state-classification
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / existing-proof formalization in progress
- **Source:** `docs/reports/review-2410/opus.md`, Q-III and Mechanism A.
- **Statement:** Classify every actual common cofactor limit of the damped Möbius receiver, its signed data, Wiener annihilator, spectral hull, and index; decide generation by translated off-line zeros on the Kronecker curve.

## Goal and remaining mathematical gaps

**Full Q-III remains open. Do not mark the persistent goal complete.**
Current authorized scope: finish started Lean work and all existing paper
proofs, then pause. The [completion ledger](q-iii-existing-findings-lean-completion.md)
supersedes historical queue and session instructions below. Edit Lean directly;
invoke each compiler command directly. No source-generation or build scripts.
The attachment is `/Users/michael/.codex/attachments/4336a717-ce0a-4c1f-8abb-88688fc210a7/pasted-text-1.txt`.
It and the complete report have been read. No hgtl7 skill, numerical experiments,
new analytic assumptions, or unproved interfaces are allowed.

The following still require an answer, not merely structural necessary conditions:

- Which kernels actually occur along escaping Möbius receiver subsequences?
- Is the module annihilator equal to the paid ideal or its closure? What is the exact hull relation?
- Are hull points on the Kronecker curve, in a closure of translated zero points, or elsewhere?
- Which dimensions occur, and how do arithmetic zero multiplicities enter an index?
- What source property controls mixed dilation scaling and nonzero moving translations?

Search the Lean corpus before mathlib, inspect source statements, and keep
generic calibrations separate from actual source realizations. No-go closure
requires its strongest positive survivor, final source checks, and axiom audits.

## Established structural results

`ActualCofactorLimit ε` stores only a strictly increasing horizon subsequence,
a real kernel, and convergence of the actual Gram table. Unit mass, symmetry,
radius, positivity, and sharp packet contraction are derived from that source.
Every such limit has a cyclic complex Hilbert realization, a contractive critical
Wiener representation, a proper closed annihilator, and a nonempty module hull.
On escape, the complete paid ideal, including infinite-support kernels,
annihilates every actual limit. Therefore module hull is contained in obstruction
hull. This proves A1–A2 universally; it gives neither ideal equality nor zero-hull
containment. Chosen-limit APIs are thin specializations.

The full paid-kernel proof uses scalar covariance convergence. The radius
`|K_T(j,k)| <= 1/sqrt(j*k)` gives a summable Wiener majorant. Dominated convergence
passes every kernel through the common limit. A paid action has bounded source
norm, so its covariance is `O(E_T^(-1/2))`. Its limiting vector is orthogonal to
all Gram generators, hence zero; commutativity gives operator annihilation.
Finite paid truncations are never assumed dense.

For a real critical Wiener kernel, exact prefix convolution is
`A_(g*c)=D_g A_c + m_c A_g`. The correction is globally paid. This proves payment
equivalent to boundedness of the full dilation row and gives normalized vanishing.

Every normalized PSD kernel has a unique antipodal extension: the new vector is
exactly `-v_1`, so all its pairings are forced. White noise `K(j,k)=delta_jk/j`
satisfies all compactness packet constraints and this extension. This calibration
does not realize an actual Möbius escape or exclude one.

## Index and spectral distinctions

The closed annihilator quotient is Banach. Baire excludes countably infinite
Hamel dimension. The quotient identifies algebraically with the dense cyclic
image. It is finite-dimensional iff the Hilbert module is, with equal finite
dimensions. Countable Gram generators also make the Hilbert module separable.
These are checked statements, not claims that an actual infinite branch occurs.
The paid ideal has not been proved closed and cannot replace this annihilator.

A stronger dependency-closed paper proof gives exactly continuum Hamel rank in
the infinite case. Choose an orthonormal sequence in the cyclic image with
source preimages x_n. The summable curves
`sum 2^(-n)t^n x_n/(1+||x_n||)`, `0<t<1`, have independent images by Dedekind
independence of the characters `n -> t^n`. Conversely Wiener coefficients inject
into complex sequences. The generic proof and every-actual-limit application
passed with standard axioms. They are promoted to
`HTGeometry/InfiniteHilbertImagesHaveContinuumRank` and the existing actual-index
module; both final source checks passed. See
[index card](../3-formalized/closed-wiener-annihilators-have-no-countable-hamel-index.md).

Weighted white kernels `delta_jk*j^(-2σ)` have exact dilation norm `p^(-σ)`,
full mixed homogeneity, and faithful action of every Wiener algebra W_τ with
τ<=σ. Their annihilator hull is the full Bohr polydisk. Thus stronger operator
contraction does not shrink the whole annihilator hull. For σ>τ the all-one
character is not bounded in the represented operator norm. This family is a
calibration, not an actual source counterexample.

The positive replacement is the nonempty operator hull
`{ω : forall a, |bohrEval a ω| <= ||pi(a)||}`. It lies in the annihilator hull and
obeys the exact operator coordinate radii. A closed representation image makes
the two hulls equal; this applies to finite-dimensional actual modules. Closed
image is sufficient, not necessary. Weighted critical packet geometry, power
norms, Gelfand radii, and closed-image hull equality passed with standard axioms.
The generic operator hull, weighted family, and actual specialization are now
promoted and wired; all three final source checks passed. See
[spectral card](../3-formalized/strong-dilation-contraction-does-not-shrink-the-annihilator-hull.md)
and the [retired generic inference](../5-failed/operator-decay-alone-controls-the-annihilator-hull.md).

The existing `UnpayabilityCarriesMultiplicity` shows that smooth power and
logarithmic smooth power can have the same hull but different paid ideals; the
latter is non-radical with quotient rank at least two. Leading escape
normalization may lose lower logarithmic orders. A filtered multiplicity index
remains a conjecture, not an actual Möbius theorem.

A dependency-closed finite-branch refinement is on
[the joint multiplicity card](../3-formalized/finite-cofactor-index-counts-joint-spectral-multiplicity.md).
The corpus's `MatrixPrincipalSymbolAbelianSpectrum` supplies independent,
exhaustive joint generalized eigenspaces for commuting finite-dimensional
families. Their nonzero joint functions are algebra characters, and a finite
annihilating product proves they exhaust the actual module hull. The finite
index is the sum of their positive sector dimensions. All three canonical
Lean leaves and transitive axiom audits passed;
identifying these module multiplicities with arithmetic zero orders remains open.

Numeric horizon order now holds on the complete module:
`p*||D_p x||^2` is antitone in the ordinary integer order. Every hull character
of a finite-dimensional actual module has a common eigenvector, hence
augmentation or one tied radial modulus. A single sequence of half-plane
evaluations approaches it on every Wiener element. These results passed
canonical Lean checks and standard-axiom audits; see
[finite-hull approximation](../3-formalized/finite-cofactor-hulls-approach-the-half-plane-curve.md).
They supply no approximation by arithmetic zeros or infinite-hull classification.
The next source audit is recorded in
[visible poles and module multiplicity](q-iii-visible-poles-and-module-multiplicity.md).
The inspected literal Fermi Mellin quotient has both numerator and shifted
denominator zeta factors. Further inspection found the direct paid-receiver
cleared continuation identity already in AOT
`TheOffLineZerosObstructTheMoebiusReceiver`. Its existing noncancellation
criterion now has a checked kernel zero-order lower bound by the denominator
order minus the numerator order in `PaidKernelsCoverVisibleTranslatedZeroOrders`.
`CriticalBoundaryPolesObstructPaidKernels` covers the boundary value obstruction.
Finite Wiener jet interpolation and the independent interior multiplicity bound
also passed their final canonical checks with standard axioms in
`FiniteWienerJetsCanBePrescribed` and `VisiblePoleJetsBoundThePaidIndex`.
These constrain the paid quotient; identifying the hull of each individual
actual module remains open.

## Translation and signed data

Checked: `|A(n)| <= (3+13/ε)n^(1-ε)`, hence A(n)/n tends to zero. The recentered
defect `r_k(n)=A(n+k)-A(n)-A(k)` obeys `|r_k(n)|<=min(n,k)`. Its exact capped
pronic cost for T>=k is `2k-H_k-k²/(T+1)`, sharply tending to `2k-H_k`.
The raw displacement has energy at most `4k+2A(k)²=o(k²)` uniformly in T.
Therefore all raw translations with bounded k²/E disappear on escape.

The head/middle/tail proof of uniform o(k) recentered energy and bounded k/E
collapse passed Lean with standard axioms. It is now in
`RecenteredSuccessorsVanishAtTheEnergyScale`, using the reusable
`HTGeometry.UniformSmallBudgetsVanishAfterNormalization`. Both final source-only
checks passed.

A stronger complete paper proof uses the actual all-damping
Vinogradov–Korobov prefix bound to obtain A(n)=o(n^a), a=1-ε in (1/2,1).
An arbitrarily small envelope `|A(n)|<=b*n^a+B` gives recentered head cost
at most `8b*k^a+6B+2` and tail cost at most `4b*k^a/(1-a)+3B`.
Thus recentered energy is uniformly o(k^a), and raw energy uniformly o(k^(2a)).
The corresponding bounded k^a/E and k^(2a)/E translations vanish. The full
stronger proof passed Lean with standard axioms and is now promoted to
`TheSourcePowerSavingControlsMovingSuccessors`; its final source check passed. See
[power-scale card](../3-formalized/the-source-power-saving-enlarges-the-invisible-translation-scale.md).

Preserve three origin conventions. Recentered shifts vanish on the above scale.
Reset-only-origin shifts are `A+r_k+A(k)u`, with u(0)=0 and u(n)=1 for n>=1.
If A(k)/sqrt(E) tends to b, their receiver-scale Gram is `K+b²/max(j,l)`;
their own normalized Gram divides this by 1+b². The step orbit is faithful,
so its projection forces full hull even without claiming a direct-sum cyclic
space. Raw unreset boundary contributes a constant Gram and a dilation-invariant
component, which conflicts with zero-origin critical contraction when nonzero.
The reset/raw Gram formulas, faithfulness, full hulls and constant-boundary
exclusion passed canonical Lean checks. Escape records realize every positive
squared origin mass; this is an admission-or-realization theorem and asserts
no particular escaping damping. The step and positive-mixture modules also
have checked infinite dimension and continuum annihilator-quotient index.
See [origin/translation card](../3-formalized/square-root-energy-translations-still-disappear.md).

For receiver A, renormalized residual R, and paid forcing remainder F, R=F-A
exactly and all three origins vanish. The complete fixed signed limiting table is
`[[K,-K,0],[-K,K,0],[0,0,0]]` on the same subsequence. Mixed forcing errors are
O(E^(-1/2)), forcing Gram errors O(E^(-1)), and normalized fixed pole traces vanish.
Unscaled pole trace remains nonzero and fixes the subtraction; no continuous
trace on the escape Hilbert space is asserted. Full signed table and trace
vanishing passed with standard axioms and are now in
`TheSignedCofactorGramHasNoExtraCoordinates`, whose final source-only check passed.
See [signed card](../3-formalized/the-full-signed-escape-gram-is-forced-by-the-cofactor-kernel.md).

Existing source modules already prove harmonic pole-trace weights, trace-domain
invariance, a uniformly paid residual/dilation commutator even for moving
dilations, and reconstruction from residual plus trace. Do not duplicate them.
The commutator source already includes
`admits_or_moving_cofactor_commutator_vanishes`, not merely the finite norm bound.
It supplies the residual-operator comparison directly; do not reprove it.
Its missing olean is now built, and `/tmp/qiii-commutator-axiom-audit.lean` passed
with standard axioms for both the exact commutator and moving normalized
vanishing. The signed card is now in `3-formalized`. The signed source needed
no change for this separate existing theorem.

## Unit transport and admitted branch

Full Wiener pair covariance is a second dominated sum of the already proved
single-coordinate covariance. The exact bound retains both Wiener weights.
Its limit is `<pi(b)v,pi(a)v>`. The double limit and exact finite-cell source
identity passed Lean with standard axioms and are now in
`CompleteWienerPairingsFollowTheCommonCofactorLimit`; final source check passed.

For a Wiener unit g, w=pi(g)v is nonzero and cyclic. Exact convolution adds only
a paid correction. Thus transformed energy divided by original energy tends to
||w||²>0 and transformed normalized Gram is that of `V_j w/||w||`. Equal-Gram
total-family unitaries identify the full modules and preserve annihilator, both
hulls, and dimensions. The actual Möbius–Liouville square-indicator unit is already
proved. Source comparison, transport, positive energy ratio, escape
preservation and the Möbius–Liouville specialization passed their final
canonical Lean checks; see
[unit card](../3-formalized/wiener-units-transport-the-complete-escape-module.md).

Further paper consequence: on admission, the common Gram limit is unique and
its Wiener action faithful. The source first cell is nonzero. If a coefficient
row first becomes nonzero at m, its finite-cell dilation at m equals that
coefficient times A(1). Full pairing convergence plus bounded admitted energy
would force every fixed cell to vanish when the limiting vector is zero,
contradicting this triangular identity. This avoids constructing a separate
global Hilbert realization. Faithfulness, full hull, and the escape
contrapositive passed with standard axioms and are now in
`AdmittedCofactorModulesAreFaithful`. Its final source check passed.
It explains why the paid-ideal bridge is explicitly an admission-or-annihilation
dichotomy: admission makes the paid ideal whole, without making the normalized
common-limit Hilbert space zero.
The complete paper proof and its dimension/uniqueness consequences are now on
[the admitted-module card](../3-formalized/admitted-cofactor-modules-are-faithful.md).
The dimension and uniqueness consequences passed canonical checks in
`AdmittedCofactorModulesAreFaithful` and `TheAdmittedCofactorKernelIsUnique`.
The unitary transport, full-source dilation and paid-correction Gram estimates
also passed canonical checks, as recorded on the admitted and unit cards.

## Scaling and parallel programme evidence

Every positive cofactor diagonal has an actual contracted state with kernel
`K(pj,pk)/K(p,p)`. Its module is the closure of the dilation range, with
full Wiener intertwining and annihilator `I:delta_p`. Contractions compose;
zero diagonals force finite dimension. Finite quotient index drops by the
exact dilation nullity, and every defined rank-one contraction fixes its
kernel and annihilator. All eleven canonical leaves passed direct Lean
checks and standard-axiom audits; see
[actual cofactor contractions](../3-formalized/contracting-horizons-acts-on-actual-cofactor-states.md).

Exact pronic fibre dilation at complete blocks compares K_T(pj,pk) with the
state at T/p. Scalar regular variation can determine diagonal scaling without
identifying mixed horizon states. Logarithmic horizon averages may restore
stationarity; they need not be individual source tangents. No actual regular
variation or mixed-stationarity premise is available.

The independently formalized Biarithmetic `DiagonalScalingCountermodel` supplies
a rank-three calibration with all critical constraints and exact diagonal
scaling but unequal mixed scaling, plus a stationary averaged positive survivor.
The parallel [logarithmic-chirp source-tangent project](biarithmetic-logarithmic-chirp-tangents.md)
has checked phase rigidity, phase-group and strict Cauchy-kernel components;
its source asymptotic and complete tangent classification remain unverified.
Q-III uses none of those unverified claims. Neither calibration is an actual
Möbius counterexample. The weighted faithful family above separately
refutes inferring annihilator-hull radii from operator growth alone.

The golden Beurling datum at q=5 is not itself an integer-prefix source. The
parallel `biarithmetic-golden-digital-module.md` develops an explicit arithmetic
source and distinguishes its infinite ordinary-floor module from a rank-one
intrinsic norm-lattice module. Its full tangent/hull classification and critical
paid-ideal nonclosedness remain unverified. Preserve that work; do not import
paper conclusions or identify the two ambient actions. Parallel paid-source
perturbation ideal stability is formalized; full Gram stability is still paper.

## Historical verification notes — superseded

The notes below preserve the development record only. Their active-session,
scratch-path, script and pending-status instructions are obsolete. Use the
[completion ledger](q-iii-existing-findings-lean-completion.md) for current
state. Do not execute any historical source assembler or compilation script.

**One active sequential Lean command: session `82907`,**
`/bin/zsh /tmp/qiii-unit-finite-and-core-checks.sh` from `formal/`.
Poll before any new Lean process. The admitted olean passed in session `1288`.
The active script checks `/tmp/qiii-unit-and-finite-check.lean`, then checks the older
core source modules sequentially even if the new scratch has local errors.
It returns the scratch failure status after successful core checks.
The combined scratch was assembled by
`/tmp/qiii-assemble-unit-and-finite-check.py`, with separate scopes for every
component. It includes the new real convolution, Liouville, action transport,
finite-character, normalized-Bohr, and actual-index drafts. Do not edit the
assembled file while its check runs.

Session `51754` finished: all four oleans and all eight promoted final source
checks passed. The scratch checked complete source dilation and the unit Gram
unitary/dilation intertwining with standard axioms. Remaining errors were
complex inner-product casts and an omitted vector argument, a unit-Gram rewrite
order, the zero coefficient of a zero arithmetic function, beta reduction in
pronic norm monotonicity, and an unavailable absolute-value triangle lemma.
These are fixed for the next scratch. The new finite-dimension-implies-escape
corollary is also included; it was added after the preceding assembled check.

Session `63953` stopped at the first generic continuum source with a docstring
placed before `omit`; that ordering is fixed. The retry passed all promoted
final source checks. The older core checks are prepared in
`/tmp/qiii-old-core-final-checks.sh` but have not been launched.
Further unqueued unit-transport drafts are `/tmp/qiii_real_wiener_source_body.lean`
(exact real convolution, mean correction, uniform norm bounds) and
`/tmp/qiii_paid_convolution_gram_body.lean` (paid correction vanishes from the
actual normalized source Gram). Neither has been checked yet.
The subsequent unqueued drafts are
`/tmp/qiii_real_unit_convolution_limit_body.lean` (positive transformed energy
ratio and the unit Gram limit for actual real convolution),
`/tmp/qiii_mobius_liouville_module_body.lean` (canonical mean and the existing
square-indicator unit specialize this to the actual Liouville receiver), and
`/tmp/qiii_unit_action_transport_body.lean` (the total-family unitary intertwines
the complete Wiener action and preserves its annihilator, operator hull, and
dimensions). These are unverified drafts, not established source results.
The finite-character draft `/tmp/qiii_finite_joint_characters_body.lean`
now includes multiplicativity via the existing two-operator common-eigenvector
lemma, the joint dimension sum, and a finite-product proof that every kernel
character is one of the joint characters. It is unverified. Its actual Bohr
specialization must use characters or the section `omega(0)=0`: the existing
`BohrPoint` type leaves the zero coordinate free, and `bohrEval_congr` reads
only positive coordinates. The finite-index paper card now states this exact
convention; summing over raw Bohr representatives would duplicate the all-one
positive character.
The normalized Bohr section and actual finite-index specialization are now
drafted in `/tmp/qiii_normalized_bohr_characters_body.lean` and
`/tmp/qiii_actual_finite_index_body.lean`. The latter includes the unconditional
finite joint-multiplicity sum or continuum-index alternative. Neither draft
has been checked. `/tmp/qiii-assemble-unit-and-finite-check.py` assembles these
with the source/unit drafts for the next check; the preceding feedback is now
incorporated and the combined file is assembled. Its import of the canonical
admitted module uses the successful olean from session `1288`.

Session `33559` finished. The missing commutator olean and axiom audit passed.
The actual operator-hull wrapper, entire power-translation argument, full
double/source pairing, admitted faithfulness/full hull/escape contrapositive,
and unit Gram unitary/dilation intertwining passed with standard axioms.
Remaining errors were scalar evaluation for arithmetic functions, typed
conditional branches and missing point-mass reduction in the exact source
dilation proof, plus one nonzero unit-vector unfolding. These are fixed.
`/tmp/qiii-promote-source-pairings-and-power.py` promoted the three passed source
layers; it is consumed and must not be rerun. All three imports are wired.

Session `89895` completed. The uniform-budget olean and all three refinement
source-only checks passed. The weighted family's complete geometry/spectrum,
closed-image hull equality, generic continuum rank, actual finite-or-continuum
dichotomy, and double Wiener covariance convergence passed with standard axioms.
Remaining errors were the missing ACCE namespace in the operator-hull dichotomy,
an unreduced function composition in the source-power estimate, a PNat coercion
in the finite pairing, and local admitted-faithfulness sum/limit rewrites.
Those are corrected for the current check. The two new unit/source-dilation
drafts are being checked for the first time.

The checked spectral/index parts were promoted by
`/tmp/qiii-promote-spectral-and-index.py`; do not rerun this consumed generator.
New canonical files: `ArithmeticOrientationTheory/TheOperatorHullOfAWienerAction`,
`ArithmeticOrientationTheory/WeightedOrthogonalCofactorsHaveTheFullHull`,
`ArithmeticDefectRigidity/TheCofactorOperatorHullObeysItsDilationRadii`, and
`HTGeometry/InfiniteHilbertImagesHaveContinuumRank`. The actual index file now
includes the continuum extension. Imports are wired; final checks remain.

Sessions `55967` and `95027` ended with local errors. In `95027`, uniform-budget,
full linear translation, full signed Gram, normalized traces, weighted power
norms/Gelfand radius/unbounded character, and antipodal uniqueness all passed
with standard axioms. Remaining errors were missing namespace qualifications,
two square-root/rpow rewrites, a range-norm type annotation, the orthonormal
preimage function equality, and finite-cell sum bookkeeping. These are fixed
for the current retry. The new admitted faithfulness draft has not yet run.

Previous sequential session `98252` ended with linear-translation errors:
misindented triangle proof, a numeric simplification, and missing compensation
namespace. All were corrected; its last epsilon proof now uses the shared
uniform-budget lemma. Spectral/signed/power stages did not run in that session.
The Baire and separability oleans and generalized index source check **passed**.
Baire standalone imports now explicitly include complex scalars and
`Mathlib.Topology.Baire.CompleteMetrizable`.

Canonical source modules already wired, with successful scratch/source-olean
checks and standard axiom audits unless noted:

- ADR: `RepairingKernelsVanishOnEscape`, `WhiteNoiseAndAntipodalEscapeData`,
  `TheCofactorLimitCarriesACyclicDilationAction`, `TheCofactorLimitIsAWienerModule`,
  `WienerCovariancesFollowTheCommonCofactorLimit`, `PaidWienerKernelsAnnihilateTheCofactorLimit`,
  `TheOriginTraceControlsMovingSuccessors`.
- HTGeometry: `AntipodalKernelExtension`, `RealPositiveKernelComplexification`,
  `BoundedKernelReindexing`, `CountableAlgebraicDimensionForcesFiniteDimension`,
  `CountableGramHilbertSpacesAreSeparable`.
- AOT: `BoundedMultiplicativeSequencesActOnWienerAlgebras`.
- ACCE: `TheExactPronicCostOfACappedRow`.
- ADR `TheClosedCofactorAnnihilatorHasNoCountableIndex`: universal source-only
  check passed; latest finite-index/continuum audit still pending.

The three earlier refinements, generic continuum module, extended actual-index
module, generic operator hull, weighted family, and actual operator-hull wrapper
are wired and passed final source-only checks. Source power, complete pairings,
and admitted faithfulness passed too. The admitted olean passed; the combined
scratch and older core checks are now running sequentially in session `82907`.
Older core source-only checks listed above remain. Standard axioms are
`propext`, `Classical.choice`, `Quot.sound`. No umbrella was compiled. Remaining
active drafts are not yet promoted or wired. The operator-decay/annihilator-hull
no-go completed its gates with its exact positive survivor; the overall actual
classification remains open.

Consumed universal promotion/generalization generators must **not** be rerun;
they can overwrite later extensions. Current source files are canonical.
Delete own consumed scratch files only after verified promotion. Preserve other
agents' work and processes; external commits can absorb files, so clean git
status is not verification. Never use `scripts/check_axioms.sh`: it compiles an
umbrella and omits `--old`. Never `lake build` or raise Lean limits.

README and report corrections describe only checked source results. AOT
`AnIndexFormulaForTheActualReceiver` comments now accurately restrict its
empty-hull formula to above width; its all-damping TFAE includes hull emptiness.
No theorem in that source was changed.

### Current verification handoff: unit, finite-index, and order refinements

Session `82907` finished the assembled unit/finite draft with errors and is
continuing the sequential old-core final source checks. Do not start another
Lean process until that entire session exits. The assembled draft file must
remain unchanged while the session runs. Its part files were corrected for
namespace resolution, explicit submodule membership, complex casts, and
function application; these fixes remain unverified. Admitted full-horizon
kernel uniqueness, the positive-energy paid perturbation estimate, the real
convolution identity, and the uniform mean-correction bound passed the draft
with only the standard axioms. Source dilation and unitary Gram equivalence
also passed again. Finite-module escape had only a missing namespace, now
fixed in its part file. No downstream theorem with `sorryAx` is accepted.

New untested analytic drafts: `/tmp/qiii_cleared_continuation_body.lean` and
`/tmp/qiii_paid_kernel_zero_order_body.lean`; see the visible-poles card for
proof and exact remaining limits. The helper must eventually be extracted
into the existing source proof, not copied permanently.

Four checked draft components are now canonical and wired, with standalone
source checks still pending: `AOT/WienerCoefficientEvaluation`,
`ADR/CompleteWienerSourceRowsRespectDilation`,
`ADR/TheAdmittedCofactorKernelIsUnique`, and
`ADR/WienerUnitsTransportCofactorGrams`. Their definitions passed the previous
assembled check; changed import boundaries still need standalone validation.

After session `82907` exits, the prepared sequential command is
`/bin/zsh /tmp/qiii-followup-checks.sh` from `formal/`. It first builds exactly
these four required oleans, then independently checks unit-source transport,
finite joint multiplicities, and partial-cancellation order/jet constraints.
Each draft check writes its own log in `/tmp/qiii-*-followup-check.log`; draft
failure does not suppress the other independent checks. No umbrella build.
`/tmp/qiii-assemble-followup-checks.py` assembles the three scratch files; do
not regenerate a file while its check is running. The old assembled
`/tmp/qiii-unit-and-finite-check.lean` is superseded once its current session
ends. The next script has been prepared but NOT started.

### Moving-origin construction lead

Two new boundary cards separate the established source-power estimate from
new work:

- `3-formalized/resetting-the-moving-origin-adds-a-faithful-step-module.md`
  gives the dependency-closed paper limit and faithful-step argument when a
  moving origin trace is prescribed.
- `3-formalized/escape-records-realize-a-faithful-moving-origin-boundary.md`
  derives a candidate construction of that trace from escape itself using
  large prefix records and first energy crossings. This would be an
  admission-or-existence theorem for shifted origin-reset rows, not an
  unshifted Möbius escape counterexample.

The next check script now also includes a fourth, independent boundary
foundations scratch file. New parts are
`/tmp/qiii_common_limit_along_horizons_body.lean`,
`/tmp/qiii_step_gram_body.lean`, and
`/tmp/qiii_receiver_energy_crossings_body.lean`. They have not yet been
checked. They cover common Gram extraction along prescribed cofinal
horizons, the exact step Gram limit, and unit-overshoot energy crossings.

The unit operator-norm proof's timeout was traced to a missing explicit
operator argument in `ContinuousLinearMap.opNorm_le_bound`. The draft now
supplies both operators explicitly; no limit was raised. All four followup
scratch files have been reassembled, but the followup script has not started.
Session `82907` is still running the old-core final source checks; its first
eight entries passed and it reached the capped-pronic-cost module.

The old-core check progressed past the capped-pronic-cost and generic Baire
modules and into `TheOriginTraceControlsMovingSuccessors`. Thus the exact
index card's remaining final-check gate is closed; it has moved to
`3-formalized/closed-wiener-annihilators-have-no-countable-hamel-index.md`.
The four final old-core checks still need the running session's completion.

Boundary foundations now also include
`/tmp/qiii_escape_prefix_records_body.lean` (record-sequence construction)
and `/tmp/qiii_record_energy_negligible_body.lean` (normalized record energy
vanishes by dominated convergence). They remain untested and are included
in the prepared fourth scratch file. First-crossing sequence assembly,
weak orthogonality and the faithful mixed realization remain to be written.

The record-horizon construction is now dependency-closed on paper and moved
to `3-formalized/escape-records-realize-a-faithful-moving-origin-boundary.md`.
Its card records the exact `T+1` normalization and avoids unnecessary sign
extraction. It constructs a faithful mixed **shifted** boundary on escape;
it does not assert a faithful unshifted actual limit. Lean work remains.

### Core audit complete; refinement checks running

Session `82907` completed. All fourteen old-core final source-only checks
passed, including the complete paid-ideal annihilation and separability
modules. Its exit status 1 came from the earlier assembled scratch errors,
not these source checks. No umbrella was compiled.

The sequential `/tmp/qiii-followup-checks.sh` is now running from `formal/`.
It builds only the four new required oleans, then checks unit, finite-index,
order and boundary-foundation scratch files. Do not start another Lean
process while it runs. Boundary foundations now include the first-crossing
record horizons and a uniform absolute-pronic source bound. All new drafts
remain unverified. The latter gives a simpler bounded-row cross-term proof
using the existing subcritical source envelope, without a new weak-limit
construction.

The followup session is `21809`. Its coefficient-evaluation and complete
source-dilation olean checks passed with standard axioms; the sequential
check remains running. The boundary scratch now also includes generic
moving-Gram perturbation, exact reset-origin Gram convergence, own-energy
normalization and admission-or-realization for every positive boundary
mass. These are unverified drafts, listed in the current assembler.
The assembler now accepts a filename argument and can regenerate only one
scratch file; never regenerate a currently compiling file.

The [critical-boundary refinement](../3-formalized/critical-boundary-poles-also-obstruct-paid-kernels.md)
is now formalized. The actual Mellin identity, generic complex paid-energy
bound and radial rate, finite-order cancellation, boundary obstruction and
Wiener-unit/Liouville consequences all passed final canonical source checks
with standard axioms. The strict-interior order and jet card is likewise in
`3-formalized`. No actual module spectral identification follows.

### Unit and finite-check feedback

All four new required oleans passed in session `21809`; it has completed
the unit and finite scratch checks with errors and moved to the analytic
order scratch. Unit operator-norm equality, full-action intertwining, kernel
equality, operator-hull equality and rank transport passed with standard
axioms. They were appended to the canonical
`WienerUnitsTransportCofactorGrams` module. The admitted infinite-dimensional
and continuum-index consequences and finite-module escape theorem also
passed and were appended to `AdmittedCofactorModulesAreFaithful`. The
promoter `/tmp/qiii-promote-unit-action-and-admitted-index.py` is consumed;
do not rerun. These two changed canonical files need new import-boundary
checks and fresh own oleans for the written unit/finite checks.

Unit retry fixes: function quotients/compositions use pointwise `congr`;
misparsed typed lambda proofs are parenthesized; eventual monotone-atTop
arguments are ordered correctly. Finite retry fixes: finite generalized
eigenspaces rewrite through `genEigenspace_nat`; normalized Bohr equality
destructs the outer subtypes; zero-coordinate normalization uses a direct
simp; actual Bohr evaluation names are qualified against HTGeometry
collisions. These corrections remain unverified. The joint-sector dimension
sum already passed, but the normalized-hull identification did not.

The prepared next command is
`/bin/zsh /tmp/qiii-refinement-retry-and-foundation-audits.sh` from `formal/`.
It has NOT started. It rebuilds only the two changed own modules for their
written dependents, checks corrected unit and finite scratches, then performs
the five required canonical source-only audits. Current session `21809`
must finish first. Order/boundary feedback may require extending this queue.

Boundary scratch now includes the full reset-origin Gram draft, first-record
realization, unreset diagonal exclusion, a generic max-Gram coefficient
recovery theorem, dominated Gram comparisons, critical-kernel Wiener
integration and the step/mixed module faithfulness drafts. All are unverified.
The generic complex paid Mellin bound has now been included as the last part
of the analytic-order scratch. Do not regenerate that file while its current
check runs.

### Refinement retry and canonical audits

Session `21809` exited. Four foundational olean checks passed. The order
scratch exposed only redundant simplification, an addition-side mismatch,
and a trivial nonnegative-zero goal; those are corrected in its staged
parts. Boundary checking stopped before elaboration because the source-power
module's olean was missing. No boundary theorem has passed yet.

Session `32035` now runs `/tmp/qiii-refinement-retry-and-foundation-audits.sh`
from `formal/`, one Lean process at a time. It rebuilds the two changed own
modules, builds exactly the missing source-power olean, checks unit, finite,
order and boundary scratches independently, then runs five final source-only
canonical audits. Logs use `/tmp/qiii-*-retry-check.log`.

A stronger explicit cleared-Mellin helper is separately staged in
`/tmp/qiii-exact-cleared-helper-check.lean`. It identifies the analytic factor
with the actual receiver's `complexMellinPairing`, as needed at the critical
boundary. It has not been checked. After verification, extract this helper
into the original off-line obstruction module and shorten its old value
proof, instead of retaining duplicate continuation proofs.

### New exact diagonal invariant and next queue

The two changed canonical oleans (`AdmittedCofactorModulesAreFaithful`,
`WienerUnitsTransportCofactorGrams`) passed again with only standard axioms
in session `32035`. That session is now building the missing source-power
olean before the four scratch checks and five final canonical source checks.

A new dependency-closed paper result is recorded in
`3-formalized/cofactor-diagonals-read-horizon-energy-ratios.md`: every
actual common limit satisfies
`E(floor((T_m+1)/p))/E(T_m+1) -> p*K(p,p)`, and this scaled diagonal is
antitone in p. Complete pronic blocks plus bounded energy jumps prove the
escape case; full admitted convergence proves the other branch. This does
not assert regular variation or read the full operator spectral radius.
Its staged Lean proof is `/tmp/qiii-diagonal-energy-check.lean`.

The next queue `/tmp/qiii-explicit-mellin-and-diagonal-checks.sh` is PREPARED,
NOT STARTED. It checks the explicit cleared-Mellin helper, a generic
critical-boundary Mellin rate, and the exact diagonal invariant. The new
rate draft `/tmp/qiii_mellin_boundary_rate_body.lean` proves
`|u*Phi(s0+u)|^2 <= |s0+u|^2 E (2*u^2+u)` and hence `u*Phi -> 0`.
Do not launch another Lean process until session `32035` exits.

`/tmp/qiii-promote-verified-refinements.py` is PREPARED, NOT RUN. It writes
six canonical leaves for paid Gram perturbations, real unit source transport,
Möbius–Liouville transport, finite algebra joint characters, normalized Bohr
characters, and the actual finite index formula. Run it only after the unit
and finite retry logs are clean with standard axiom prints. It has guards
against overwriting existing files and adds umbrella imports only.

### Refinement local errors narrowed

The unit retry in session `32035` passed normalized unit source Grams,
positive-energy perturbation, exact source convolution and the paid mean
bound. It has two remaining local errors: a quotient-associativity rewrite
was reversed, and the convolution comparison needed a final definitional
`rfl`. Both staged parts are corrected and the unit scratch reassembled.
The same reversed rewrite was proactively fixed in record horizons before
the boundary scratch began.

The finite retry passed algebra joint characters, exhaustive decomposition,
its dimension sum and normalized Bohr-point injectivity. Remaining errors:
`omit` must precede doc comments; the shifted-power proof must rewrite
`f.commutes` before expanding the scalar algebra map; the correct character
namespace is `ArithmeticOrientationTheory.WienerAlgebraAt.bohrCharacter`.
These are corrected in staged parts. The two step/mixed hull uses of
`bohrCharacter_apply` were fixed in the same way before boundary checking.
No erroneous theorem has been promoted.

The next script now first builds exactly the missing white-noise olean,
then rechecks unit and finite refinements, checks the full critical-boundary
pole scratch, then checks the exact diagonal and its new consequences.
It remains NOT STARTED. The prepared six-leaf promoter remains NOT RUN.

New paper card:
`3-formalized/horizon-order-excludes-prime-deleted-white-noise.md`.
Deleting the even white-noise coordinates passes all original abstract
Gram constraints but violates the actual diagonal's numeric antitonicity
at 2 and 3. The positive consequence: one zero actual cofactor forces
finite dimension at most p-1; every infinite actual module has strictly
positive diagonal. Both are drafted in the next diagonal scratch, unverified.

The critical-boundary pole card has moved to `2-fully-proven`: its paper
argument now explicitly uses the already proved finite zeta orders and
closed-half-plane continuity from `WeilConeBoundaryDilation`. The assembled
new boundary-pole scratch is unverified and separate from the moving-origin
boundary scratch currently in the active queue.

### Analytic strict-interior check passed

The order retry completed cleanly in session `32035`, with standard axioms
for all order, jet, partial-cancellation hull and generic complex Mellin
bound prints. The active queue moved to the large moving-origin boundary
scratch (PID `86913` at last observation); after it finishes, the script
still has five canonical final source checks to run. Do not start the next
queue until the entire session exits.

The next critical-boundary scratch now also rechecks the strict-interior
results against the stronger explicit Mellin helper and includes general
Wiener-unit-orbit and Liouville applications of the interior jet and boundary
obstruction statements. Its new application part is
`/tmp/qiii_visible_poles_on_wiener_unit_orbits_body.lean`.

The completed rank-one classification is recorded in
`3-formalized/rank-one-cofactor-moduli-are-archimedean.md`: augmentation or
one power times a multiplicative real sign. It gives no sign selection or
Kronecker-curve membership.

### Boundary elaboration repair and next queue

The first moving-origin boundary scratch failed locally; no draft from it
has been promoted. Root repairs now staged: explicit typed common-limit
structure; explicit step-tail finset equality; additive-inequality namespace
collisions; explicit constant in record dominated convergence; denominator
nonzero proofs; composition reduction before rewrites; squared pronic norms
rewritten before `pow_two`; Wiener point mass at zero proved directly; and
`NNReal` notation scope. Mixed packets now use an explicit unreindexed
formula. These changes are reassembled and UNVERIFIED.

The five canonical final checks in session `32035` are still running
sequentially; last observed stage was `TheAdmittedCofactorKernelIsUnique`.
`WienerCoefficientEvaluation` and `CompleteWienerSourceRowsRespectDilation`
finished with standard printed axioms. The next script remains NOT STARTED:
`/tmp/qiii-explicit-mellin-and-diagonal-checks.sh`. It now includes the repaired
moving-origin scratch after unit, finite, critical-boundary poles and diagonal
checks. The diagonal scratch shares the repaired energy-jump proof and now
separates `pronicNorm_sq` rewriting from the general `pow_two` simplifier.

Corpus search for monotone completely multiplicative power classification
returned no usable theorem. The rank-one scalar extraction search surfaced
`HTGeometry.exists_smul_of_finrank_ker_eq_one` as a technique lead; inspect
its statement/source before applying the underlying finite-dimensional API.
The rank-one card remains a conjecture; no phase/Kronecker conclusion follows
from magnitude rigidity alone.

The rank-one card is now `3-formalized/rank-one-cofactor-moduli-are-archimedean.md`.
Canonical Lean checks prove the real cyclic character from K(p,1), the
augmentation-or-power magnitude classification, and the multiplicative-sign
factorization with exponent at least one half. No phase selection is claimed.

Prepared `/tmp/qiii-promote-verified-pole-refinements.py`, NOT RUN. It first
requires the full critical-boundary scratch to be error-free with no sorryAx,
then replaces the old duplicated cleared-continuation proof inside
`TheOffLineZerosObstructTheMoebiusReceiver` with the explicit actual Mellin
identity, existential wrapper and old value theorem. Five new leaves split
interior orders/jets, the generic Mellin boundary rate, generic boundary-order
cancellation, actual critical-boundary obstructions, and unit-orbit/Liouville
applications. All require own dependency builds and final source checks.

### Foundation audits complete; next queue live

Session `32035` has EXITED with status 3, exactly from the three known draft
failures (unit, finite, moving-origin boundary). All five canonical final
source audits PASSED with standard printed axioms, including admitted
continuum quotient index and finite-dimensionality forcing escape.
No canonical audit failure remains in this batch.

Session `84684` now runs `/tmp/qiii-explicit-mellin-and-diagonal-checks.sh`
from `formal/`. Its sequence: build the missing white-noise olean; corrected
unit; corrected finite; explicit Mellin/interior/boundary pole work; exact
diagonal, odd-white exclusion, finite cutoff and rank-one magnitude work;
corrected moving-origin boundary. One Lean process at a time. Do not launch
another until this entire session exits. All new scratches remain pending.

The next queue has finished the exactly missing white-noise olean and
entered corrected unit scratch (PID `99836` at last observation).
The diagonal scratch now also includes the augmentation model from
`/tmp/qiii_augmentation_gram_body.lean`, still UNVERIFIED. Its paper card is
`5-failed/rank-one-horizon-order-does-not-select-kronecker-points.md`.
It passes even numeric-order antitonicity and has one character outside all
finite half-plane points. This is only an abstract countermodel; no actual
Möbius realization is claimed. The mandatory positive survivors are the
actual finite-cutoff theorem and rank-one magnitude classification, both
in the same pending diagonal verification.

README and the Q-III correction block in `opus.md` now record only the
newly final-audited canonical facts: admitted infinite dimension/continuum
index, finite actual modules forcing escape, unique admitted kernel, exact
complete source-row dilation, and full abstract unit-action conjugacy.
Unverified source convolution, pole, moving-origin and diagonal additions
are not reported as formalized there.

Fresh frontier search surfaced the existing `receiverEnergy_succ_le` and
`abs_receiver_le_cell` in `EnergyQuantilesRetainDiffuseEscape`, whose olean
already exists. Removed the duplicate drafted prefix/jump proofs and their
unused successor identity; the pending crossing, record and diagonal parts
now consume that existing leaf. The absolute-level strict-overshoot theorem
remains new. Boundary and diagonal scratches were reassembled while the
queue was still checking unit transport.

New actual-state transport lead:
`3-formalized/contracting-horizons-acts-on-actual-cofactor-states.md`.
The generic mixed last-fibre error is drafted in
`/tmp/qiii_mixed_horizon_error_body.lean`, NOT YET IN A CHECK QUEUE. It is
intended to prove actual contracted-horizon realization
K_p(j,k)=K(pj,pk)/K(p,p) when K(p,p)>0, with a zero-operator/finite-dimensional
alternative at K(p,p)=0. No multiplicativity or fixed-state assumption.

### Actual unit source transport passed

The corrected unit scratch in session `84684` completed with no errors and
standard axioms for every printed theorem, including real Wiener source
normalization, positive limiting energy ratio, preservation of escape and
Möbius–Liouville Gram transport. Its only warning was a redundant `change`
in the nonnegative-energy perturbation proof; removed that no-op from the
staged source before canonical promotion. No recheck of the whole scratch
is needed solely for that removal; canonical leaf checks remain required.
The queue is now checking finite joint characters (PID `2732`). The guarded
six-leaf promoter remains unrun until that log is clean as well.

The mixed-horizon transport card now records its exact module consequence:
the new cyclic module is the closed D_p-cyclic range and has annihilator
I:delta_p. This gives Hull(I)\{omega(p)=0} subset Hull(I_p) subset Hull(I),
without claiming equality at zero coordinates. Contractions compose when
the normalizations are positive; nonaugmentation rank-one states would be
fixed. These paper deductions are not yet Lean proofs.

### Finite joint multiplicity passed; canonical promotion

The corrected finite scratch completed with standard axioms for the full
joint-character decomposition, normalized hull correspondence, multiplicity
sum and finite-or-continuum index theorem. The guarded six-leaf promoter
ran successfully, installing and umbrella-wiring the actual unit-source
transport and finite joint-character leaves. Canonical final audits remain
pending in `/tmp/qiii-refinements-canonical-audit.sh`; do not run while
session `84684` is active. That session has entered the critical-boundary
pole scratch, followed by diagonal and moving-origin scratches.

### Critical-boundary retry and contracted-horizon expansion

The explicit actual Mellin identity and all interior order/jet assertions
passed in the critical-boundary scratch. The new boundary parts had local
elaboration failures: unspecified continuity endpoints, analytic composition
inference, a local-definition rewrite, composition eta reduction, and two
redundant tactics. These are repaired in the staged parts and the critical
scratch reassembled. No boundary source promotion occurred. Session `84684`
has proceeded to the first diagonal check; moving-origin remains next.

The contracted-horizon draft now includes an actual Gram isometric
embedding, equality of full Wiener annihilators with the principal quotient,
hull inclusions, the zero-dilation/finite-cutoff alternative and composition
laws. Its scratch is still UNVERIFIED. The existing private finite-packet
identity `packet_gram_eq` in `CountableCofactorCovariancesHaveACommonLimit`
was made public without changing its proof, so the new matrix-order
application can reuse it. This changed foundation needs its own source
audit and dependent olean before the contracted scratch.

### Formalization is the completion criterion

The user explicitly reiterated: formalize every significant finding; paper
proofs do not count as proved. All pending boundary, diagonal, rank-one,
augmentation, contracted-horizon, range/index and matrix-order results remain
OPEN until their exact Lean statements pass, transitive axioms are clean,
canonical source checks pass and imports are wired. Paper-stage placement
tracks the repository pipeline only; it is not completion.

The normalized receiver profile dependency olean is actually absent despite
an earlier handoff assumption. `/tmp/qiii-next-refinement-checks.sh` now
builds exactly this missing module before the diagonal retry; any further
missing dependency must be resolved one at a time. Do not start this queue
until session `84684` exits (currently moving-origin foundations).

### Verification queue transition

Session `84684` exited with status 3 (unit and finite scratches passed;
critical-boundary, first diagonal and moving-origin scratches had the
recorded local errors). All those errors have staged fixes. No Lean process
from that session remains. New session `6979` runs
`/tmp/qiii-next-refinement-checks.sh` sequentially: repaired critical-boundary
scratch; changed packet foundation and six canonical unit/finite leaf audits;
exactly missing normalized-profile olean; repaired diagonal scratch; repaired
moving-origin scratch. Do not start another Lean process until it exits.

The latest moving-origin check independently verified actual cofinal limit
extraction, step-pairing convergence, all prefix-record and dominated-energy
lemmas, bounded cross-pairing, moving-Gram perturbations, max-kernel Wiener
faithfulness, critical-kernel action extension, and the origin-step module's
faithfulness/full hull. Its remaining errors were an implicit limit constant,
three reflexive conversion goals, a large scalar identity, a redundant tactic
and beta reduction before a rewrite; all have staged fixes.

The contracted-state scratch is assembled but NOT IN THIS CHECK QUEUE. It
now includes actual contracted limits, principal annihilator quotients, hull
inclusions, zero/cutoff alternative, composition, closed dilation range,
finite index loss by nullity, and matrix/operator horizon order. Pending
parts and exact statements are on its card. No claimed result may stop at
this draft or at a paper argument.

The packet foundation change now preserves the original private proof
and exports `pronicPairing_packet_energy_eq` as a public wrapper. This
reuses the existing proof without removing any original declaration. The
matrix-order draft consumes that public theorem.

### Critical-boundary scratch passed; canonical proof installed

Session `6979` completed its critical-boundary scratch with standard axioms
only, then entered the existing unit/finite canonical audit. The guarded
pole promoter ran: explicit actual Mellin identity refactored into its owner,
all five pole/order/boundary leaves installed and wired. Final source audits
are prepared in `/tmp/qiii-pole-canonical-audit.sh`, NOT STARTED while session
`6979` runs. All findings still require canonical completion before promotion.

### Canonical tracking and remaining paper-only boundary consequence

The admission card is now in `3-formalized`, reflecting the already completed
session `32035` source audits: admitted faithfulness/full hull, infinite
Hilbert dimension, continuum quotient rank, finite-module escape, and unique
full-horizon admitted kernel. No redundant rechecks were run for that move.

The new boundary promoter `/tmp/qiii-promote-verified-boundary-refinements.py`
is prepared but UNRUN. It checks the completed second-retry log before
installing the generic comparison/action, max-kernel faithfulness, records,
reset-origin Gram and faithful realization leaves. It reuses the shared
receiver-crossing module if diagonal promotion has already installed it.

The older translation card's unreset Gram formula still lacked Lean, even
though its algebraic exclusion theorem was already checked. A separate exact
draft is now `/tmp/qiii_unreset_origin_gram_body.lean`, assembled as
`/tmp/qiii-unreset-origin-check.lean`. It proves raw Gram K+c, own Gram
(K+c)/(1+c), and realization of every c>0 on escape with exclusion from the
actual zero-origin class. UNVERIFIED; canonical boundary imports are required.
The active Lean queue remains session `6979`; do not overlap it.

### Current verification state and additional exact drafts

Session `6979` built and source-checked the changed common packet foundation.
The six-leaf canonical audit then stopped at the real Wiener transport leaf:
it omitted the import owning `complexWienerEnergy` and
`wienerSourcePairing_self_re`. That import is now fixed. The resume script
`/tmp/qiii-refinements-canonical-resume.sh` skips the completed foundation and
existing dependency oleans, then runs all six final source checks. It has
NOT STARTED. The current session has built the previously missing normalized
receiver profile olean and is checking the diagonal scratch; the moving-origin
retry follows. No second Lean process may start while this session runs.

The next prepared queue `/tmp/qiii-common-vector-and-pole-audits.sh` now runs:
canonical unit/finite resume, common-family eigenvector scratch, Wiener jet
functional scratch, and pole canonical audit. Only start after `6979` exits.
The boundary canonical audit script is prepared separately, conditional on
its guarded promoter passing the completed second-retry log.

Further exact drafts, all UNVERIFIED:

- `/tmp/qiii_origin_boundary_index_body.lean`: origin-step and positive mixed
  modules have infinite Hilbert dimension and continuum Wiener quotient rank;
  assembled `/tmp/qiii-origin-boundary-index-check.lean`.
- `/tmp/qiii_rank_one_contraction_body.lean`: every defined positive horizon
  contraction fixes a rank-one actual kernel and its annihilator. Included in
  the pending contracted-state assembler.
- `/tmp/qiii_visible_pole_point_count_body.lean`: closed critical-half-plane
  visible point count, including positive order loss at the boundary.
- Wiener jet functionals, simple local parameters, separated masks, triangular
  interpolation and the strict-interior multiplicity-weighted paid quotient
  lower bound are now exact drafts. `/tmp/qiii-visible-jet-index-check.lean`
  assembles these with the point-count bridge. The mixed boundary/interior
  weighted count is still to be written.

No new arithmetic hull equality is asserted. All these drafts and paper
arguments remain OPEN until their own canonical Lean checks and axioms pass.

### Diagonal findings split by verified dependency closure

The diagonal retry completed. Exact dilation blocks, first energy crossings,
actual energy-ratio identification and numeric diagonal order, the
prime-deleted-white-noise exclusion, the monotone multiplicative power law,
and actual rank-one magnitude classification all passed with standard axioms.
The zero-cutoff branch failed only on an unavailable cancellation lemma; the
augmentation branch failed on two malformed one-line tactic blocks and a
no-progress simplification. All local fixes are staged.

The guarded partial promoter `/tmp/qiii-promote-verified-diagonal-foundations.py`
has RUN, installing and wiring the six independently verified leaves. Do not
rerun it or the obsolete all-eight promoter. Canonical foundation checks are
prepared in `/tmp/qiii-diagonal-foundations-canonical-audit.sh`. The two
remaining proofs have a small retry scratch importing the canonical
foundation: `/tmp/qiii-diagonal-cutoff-augmentation-check.lean`. Its guarded
two-leaf promoter is `/tmp/qiii-promote-verified-cutoff-augmentation.py`, UNRUN.

The next queue is now `/tmp/qiii-next-canonical-and-local-checks.sh`: it runs
the diagonal foundation audit and the two local retries, then the earlier
unit/finite/common-eigenvector/jet-functional/pole queue. Start only after
session `6979` exits; that session has entered its last moving-origin scratch.
The contracted-state assembler now imports the three canonical diagonal,
zero-cutoff and rank-one leaves instead of repeating their proofs; regenerate
it only once the remaining cutoff leaf is installed.

### Boundary passed and next sequential queue started

Session `6979` is CLOSED, exit 2: one canonical import failure and the two
recorded local diagonal branches failed; the full moving-origin scratch
passed, with standard axioms for every final target. Its harmless unused
closing tactics and completeness binder were removed.
`/tmp/qiii-promote-verified-boundary-refinements.py` has RUN and must not be
rerun. The thirteen installed modules are listed in
`/tmp/qiii-boundary-canonical-modules.txt`.

Current single Lean session: `90975`, parent shell PID `83059`, running
`/tmp/qiii-next-canonical-and-local-checks.sh` from `formal/`. The queue is:

1. Final diagonal-foundation audits and missing dependency oleans.
2. The two repaired cutoff/augmentation proofs (only if step 1 passes).
3. Unit/finite canonical resume, common-family eigenvector scratch, Wiener
   jet-linear-functional scratch, and pole canonical audits.
4. Boundary canonical audits (only if step 1 passes).
5. Raw unreset-origin Gram and boundary continuum-index scratches (only if
   boundary canonical audits pass).

Do not start another Lean process until session `90975` exits. Source and
log paths are in the queue scripts. Every unresolved card remains open.

### Additional exact corollaries queued with the canonical audit

Session `90975` remains the only active Lean session. Exact pronic dilation
blocks and receiver energy crossings have passed their canonical build and
final source checks with standard axioms. The diagonal foundation audit
has moved to actual energy ratios. No other canonical batch is complete.

The tied-torus approximation remains pending; conjugation is complete:

- `/tmp/qiii-tied-torus-character-limits-check.lean`: reusable finite-prime
  approximation, one vertical sequence converging on all Wiener elements
  for a common radial modulus, and augmentation as Re(s) tends to infinity.
  The corpus proof in `AKernelBoundedBelowOnTheHalfPlaneIsAUnit` supplies the
  prime approximation mechanism; `HTGeometry/LSeriesRightLimit` supplies the
  augmentation endpoint. The finite actual application is separately
  drafted and awaits the operator-order and finite-hull modulus proofs.
- `ArithmeticDefectRigidity/ActualCofactorHullsRespectConjugation.lean`:
  real source rows imply conjugation of complete Wiener pairings, equal
  cyclic norms, invariance of the actual annihilator and conjugation symmetry
  of each module hull. Final canonical audit `78866` passed with standard axioms.

The [finite-hull approximation card](../3-formalized/finite-cofactor-hulls-approach-the-half-plane-curve.md)
remains in progress; the [conjugation card](../3-formalized/actual-cofactor-hulls-preserve-complex-conjugation.md)
is formalized. Curve approximation is not exact curve
membership and does not restrict approximants to translated zeta zeros.
Conjugation symmetry does not exclude real hull points or prove an even
index. The full arithmetic classification remains open.

The mixed paid-jet index scratch now also contains exact unit-orbit and
Liouville corollaries in `/tmp/qiii_visible_jet_index_unit_orbit_body.lean`.
They are UNVERIFIED and are not yet in the live queue.

### Exact finite-horizon and sign corollaries retained for Lean completion

Session `90975` remains active. Exact dilation blocks, energy crossings,
actual diagonal energy ratios and the generic multiplicative power law have
passed their final canonical source checks with standard axioms. Rank-one,
cutoff, unit/finite, pole and boundary checks remain in the sequential queue.
The rank-one sign factorization is also in its later scratch stage.

The diagonal card's exact terminal-fibre formula was still paper-only.
`/tmp/qiii_exact_horizon_remainder_body.lean` now states both its finite-sum
remainder and closed telescoped correction, including quotient zero.
`/tmp/qiii_mixed_horizon_error_body.lean` consumes this identity and states
the full bound C*D/p for rows bounded by C*n and D*n, plus the unit-bound
corollary needed by actual contractions. These parts lead the contracted
horizon assembler and remain UNVERIFIED. Do not promote the diagonal card
before these and its mixed consequences pass canonical Lean checks.

Guarded small-proof promoter: `/tmp/qiii-promote-verified-small-followups.py`
with arguments `family`, `jets`, `conjugation`, or `signs`; all UNRUN.
Guarded tied-torus promoter `/tmp/qiii-promote-verified-tied-torus.py` is also
UNRUN. It extracts the finite-prime approximation into its existing owner
and reuses that helper in the existing tied-torus bound, before installing
the common-sequence theorem. Its final checks are prepared in
`/tmp/qiii-tied-torus-canonical-audit.sh`. None may run before the associated
scratch finishes cleanly with standard axioms.

### Diagonal foundation canonical batch complete

All six leaves in `/tmp/qiii-diagonal-foundations-canonical-audit.sh` passed
canonical source checks with standard axioms. Session `90975` has advanced
to `/tmp/qiii-diagonal-cutoff-augmentation-check.lean` (lake PID `20994`).
No other Lean process is running for this task. The cutoff survivor,
augmentation and sign corollaries still need their own completion; the
corresponding cards remain open.

The complete kernel-family development is now formalized in
`../3-formalized/actual-cofactor-kernel-limits-have-no-discrete-branching.md`.
Generic late crossings, actual Gram-step bounds, prescribed-horizon common
limits, intermediate-coordinate kernels, the exact singleton/continuum
alternative and nonuniqueness forcing escape all passed canonical source
checks with standard axioms. The final application audit was `79971`.

The contracted module draft now proves full Wiener-operator intertwining,
not only its cyclic-vector identity. Its guarded promoter
`/tmp/qiii-promote-verified-contracted-horizons.py` is prepared, UNRUN;
regenerate the contracted scratch after the cutoff dependency is installed.

### Cutoff/augmentation local retry still pending

The cutoff/augmentation stage finished with three local errors, preserved
in `/tmp/qiii-diagonal-cutoff-augmentation-check.log`. Multiplication
cancellation resolved to an unrelated namespaced lemma; it now uses the
direct contradiction between positivity of q*K(q,q) and its nonpositivity.
The PNat augmentation proof's two natural-number rewrites now use
`Nat.le_mul_of_pos_right/left` followed by the exact product equality.
The repaired standalone scratch is
`/tmp/qiii-diagonal-cutoff-augmentation-retry-check.lean`, NOT RUN.
Its guarded promoter now reads the corresponding retry log. No proof with
these reported `sorryAx` dependencies has been promoted.

Session `90975` continues in the common-vector/pole child queue (root child
PID `26922` at transition). Do not start another Lean process. The next
independent Lean queue must retry cutoff/augmentation before attempting the
contracted-state bundle; current unit/finite and later pole/boundary checks
continue independently.

The obsolete all-eight diagonal promoter and obsolete diagonal canonical
script have been removed from `/tmp` to prevent reuse. The completed
foundation audit and guarded two-leaf cutoff promoter are the valid paths.

### USER OVERRIDE: direct Lean calls only; finish existing findings

The user explicitly stopped scripted builds and required formalization of
all findings currently only on paper. This overrides every historical queue
instruction above. Do not run or recreate compilation scripts. Every Lean
invocation must be one direct `lake --old env lean ...` command from
`formal/`, with at most one owned Lean process active. No `lake build`,
umbrella build, heartbeat change or whole-tree checker.

The entire owned script process group `83059` was terminated and verified
absent. Session `90975` exited 143. It had completed all six diagonal
foundation source audits, failed the three recorded local cutoff/augmentation
steps, and built the real Wiener convolution olean successfully. Its later
finite joint-character build was interrupted before any olean was written.
No unit/finite final source batch, small scratch batch, pole canonical batch
or boundary canonical batch ran to completion. All obsolete `/tmp/qiii*.sh`
compilation drivers have been removed.

The first direct cutoff/augmentation check was session `73496`; its failed
local cancellation step was subsequently repaired. The successful direct
retry and canonical cutoff audit are recorded in the completion ledger.

Formalization now takes precedence over further conjecture generation.
All already drafted findings remain in scope: cutoff/augmentation and signs;
actual Wiener unit transport; finite joint multiplicity; pole orders and
critical boundary; moving/reset/raw origin modules and continuum index;
contracted horizons, principal ideals, full intertwining, matrix order and
index loss; finite-hull radial moduli and half-plane approximation; complete
jet interpolation and paid-index bounds; actual conjugation; and the drafted
singleton/continuum kernel-family alternative. Every card stays open until
its exact declarations, canonical source checks and transitive axioms pass.
The user subsequently prohibited Python helpers as well. All owned Python
assemblers and promoters were deleted. Edit Lean sources directly and invoke
the compiler directly; do not recreate helper scripts.

### Current stopping instruction and completion ledger

The user paused the research goal and then explicitly required: finish started
Lean work, formalize every outstanding paper proof, then pause. Continue only
that completion scope; do not resume conjecture generation or the open full
classification problem. The current per-batch status and active compiler are
in [the Lean completion ledger](q-iii-existing-findings-lean-completion.md),
which supersedes historical session and queue instructions above.

The repaired cutoff/augmentation scratch passed directly with standard axioms.
The cutoff's canonical source-only audit also passed, and its card moved to
`3-formalized`. The old antipodality route moved to `5-failed` with its
formalized unique-extension survivor. All finite joint-index and actual
unit-transport canonical checks have now passed; both cards are in
`3-formalized`. The expanded augmentation scratch includes its singleton
character hull, first-coefficient action and exact scalar Gram; their canonical
source audit `79225` passed with standard axioms. Rank-one multiplicative signs,
actual conjugation, the singleton/continuum kernel-family alternative, visible
pole orders and boundary values, and all thirteen reset-origin boundary leaves
also passed their final canonical checks. The completion ledger records the
remaining raw-origin/index, contraction, finite-hull and interpolation work.
