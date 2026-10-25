# Q-III: actual escape states and the Kronecker curve

- **ID:** q-iii-escape-state-classification
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / active research programme
- **Source:** `docs/reports/review-2410/opus.md`, Q-III and Mechanism A.
- **Statement:** Classify every actual common cofactor limit of the damped Möbius receiver, its signed data, Wiener annihilator, spectral hull, and index; decide generation by translated off-line zeros on the Kronecker curve.

## Goal and remaining mathematical gaps

**Full Q-III remains open. Do not mark the persistent goal complete.**
The attachment is `/Users/michael/.codex/attachments/4336a717-ce0a-4c1f-8abb-88688fc210a7/pasted-text-1.txt`.
It and the complete report have been read. No hgtl7 skill, numerical experiments,
new analytic assumptions, or unproved interfaces are allowed.

The following still require an answer, not merely structural necessary conditions:

- Which kernels actually occur along escaping Möbius receiver subsequences?
- Is the module annihilator equal to the paid ideal or its closure? What is the exact hull relation?
- Are hull points on the Kronecker curve, in a closure of translated zero points, or elsewhere?
- Which dimensions occur, and how do arithmetic zero multiplicities enter an index?
- What source property controls mixed dilation scaling and nonzero moving translations?
- Complete actual Möbius–Liouville module transport and other relevant corpus applications.

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
[the joint multiplicity card](../2-fully-proven/finite-cofactor-index-counts-joint-spectral-multiplicity.md).
The corpus's `MatrixPrincipalSymbolAbelianSpectrum` supplies independent,
exhaustive joint generalized eigenspaces for commuting finite-dimensional
families. Their nonzero joint functions are algebra characters, and a finite
annihilating product proves they exhaust the actual module hull. The finite
index is the sum of their positive sector dimensions. Lean is pending;
identifying these module multiplicities with arithmetic zero orders remains open.
The next source audit is recorded in
[visible poles and module multiplicity](q-iii-visible-poles-and-module-multiplicity.md).
The inspected literal Fermi Mellin quotient has both numerator and shifted
denominator zeta factors. Further inspection found the direct paid-receiver
cleared continuation identity already in AOT
`TheOffLineZerosObstructTheMoebiusReceiver`. Its existing noncancellation
criterion can be sharpened on paper to a kernel zero-order lower bound by the
denominator order minus the numerator order. This extends the paid-ideal
obstruction, not the hull of each individual actual module.

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
These boundary consequences still need Lean and do not construct actual b!=0.
See [origin/translation card](../2-fully-proven/square-root-energy-translations-still-disappear.md).

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
proved. Source comparison and transport remain to be formalized. Reuse
`HTGeometry.DenseFeatureGramUnitary`; see
[unit card](../2-fully-proven/wiener-units-transport-the-complete-escape-module.md).

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
[the admitted-module card](../2-fully-proven/admitted-cofactor-modules-are-faithful.md).
The further dimension and full-horizon uniqueness consequences are in
`/tmp/qiii_admitted_dimension_body.lean` and
`/tmp/qiii_admitted_kernel_unique_check.lean`, both queued for their first check.
The draft `/tmp/qiii_unit_gram_equivalence_check.lean` uses
`ContinuousLinearEquiv.unitsEquiv` and the existing total-feature Gram unitary
to identify every unit-twisted Gram completion with the same Hilbert space.
Its unitary and dilation-intertwining proofs passed with standard axioms.
A local nonzero-vector rewrite was fixed for the normalization; the retry
also checks positive source-energy ratio and normalized unit source Gram
convergence in `/tmp/qiii_unit_source_gram_body.lean`.
`/tmp/qiii_wiener_source_dilation_body.lean` proves continuous coefficient
evaluation and exact complete source dilation by point-mass multiplication;
its local scalar/conditional rewrites were fixed for the same retry.
`/tmp/qiii_paid_gram_perturbation_check.lean` is a first-check draft of the
quantitative paid-correction Gram estimate needed for actual unit convolution.

## Scaling and parallel programme evidence

Exact pronic fibre dilation at complete blocks compares K_T(pj,pk) with the
state at T/p. Scalar regular variation can determine diagonal scaling without
identifying mixed horizon states. Logarithmic horizon averages may restore
stationarity; they need not be individual source tangents. No actual regular
variation or mixed-stationarity premise is available.

The independently formalized Biarithmetic `DiagonalScalingCountermodel` supplies
a rank-three calibration with all critical constraints and exact diagonal
scaling but unequal mixed scaling, plus a stationary averaged positive survivor.
The logarithmic-chirp source-tangent counterexample remains paper only. Neither
is an actual Möbius counterexample. The weighted faithful family above separately
refutes inferring annihilator-hull radii from operator growth alone.

The golden Beurling datum at q=5 is not itself an integer-prefix source. The
parallel `biarithmetic-golden-digital-module.md` develops an explicit arithmetic
source and distinguishes its infinite ordinary-floor module from a rank-one
intrinsic norm-lattice module. Its full tangent/hull classification and critical
paid-ideal nonclosedness remain unverified. Preserve that work; do not import
paper conclusions or identify the two ambient actions. Parallel paid-source
perturbation ideal stability is formalized; full Gram stability is still paper.

## Current verification handoff

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

- `2-fully-proven/resetting-the-moving-origin-adds-a-faithful-step-module.md`
  gives the dependency-closed paper limit and faithful-step argument when a
  moving origin trace is prescribed.
- `2-fully-proven/escape-records-realize-a-faithful-moving-origin-boundary.md`
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
to `2-fully-proven/escape-records-realize-a-faithful-moving-origin-boundary.md`.
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

A new boundary-pole candidate is recorded in
`critical-boundary-poles-also-obstruct-paid-kernels.md`. A first generic
complex paid Mellin bound is drafted separately in
`/tmp/qiii_complex_paid_mellin_bound_body.lean`; it is not in the running
check script. It uses generic energy rather than a half-damped coefficient
assumption.

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
`2-fully-proven/cofactor-diagonals-read-horizon-energy-ratios.md`: every
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
`2-fully-proven/horizon-order-excludes-prime-deleted-white-noise.md`.
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

A rank-one modulus lead is recorded in
`1-in-progress/rank-one-cofactor-moduli-are-archimedean.md`; corpus search
for monotone completely multiplicative power laws is pending. It concerns
magnitudes only and must not be promoted to a phase/Kronecker claim.

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

The rank-one magnitude card is now `2-fully-proven/rank-one-cofactor-moduli-are-archimedean.md`.
Its complete paper proof derives the real cyclic character from K(p,1),
proves the multiplicative energy profile is augmentation or a single power
by integer-power/ceiling comparison, and obtains |chi(p)|=p^(-s), s>=1/2.
No phase selection is claimed. The generic and actual Lean drafts are now
included at the end of the diagonal scratch in the next queue, still unverified.
The final canonical source checks have reached their last leaf,
`AdmittedCofactorModulesAreFaithful`; the previous four checks passed.

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
`2-fully-proven/rank-one-horizon-order-does-not-select-kronecker-points.md`.
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
