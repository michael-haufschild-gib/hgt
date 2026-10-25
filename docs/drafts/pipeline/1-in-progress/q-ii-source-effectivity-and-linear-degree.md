# Q-II: source effectivity, Riemann–Roch, and linear degree

- **ID:** q-ii-source-effectivity-and-linear-degree
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-2410/opus.md, Q-II and Mechanism B
- **Statement:** Determine a source-defined cone on the original scaling surface satisfying Riemann–Roch at every aperture, and determine whether its Bézout axiom follows from an independent linear degree law.

## Goal

Answer Q-II in full; formalize the answer and its corollaries without extra analytic assumptions, and apply results across the existing programmes. A reformulation of RH, a compensated pairing, a restricted test space, or a degree-positive cone without Bézout does not complete this goal.

## Gates

- [x] Read the full review and inspect the current source frontier.
- [x] Search the Lean corpus before mathlib.
- [ ] Dependency-closed paper proof of the full answer.
- [ ] Lean proofs, individual foreground `lake --old env lean` audits, and transitive axiom checks.
- [ ] Umbrella imports and applications to relevant existing programmes.

<!-- qii-live-status -->
## Current verification checkpoint

Full Q-II remains open. User requires every significant finding to be formalized;
paper arguments alone are unverified, not completed results. Prioritize clearing
the existing Lean candidates before developing further paper-only findings.
User repeated the instruction: no build scripts; formalize everything still
only on paper now. Finish the entire existing Q-II candidate queue and the older
actual-file final audits before pursuing new findings. Each Lean invocation
gets its own direct `lake --old env lean ...` command, without wrappers, loops,
or a batch runner.

User then paused the research goal and explicitly requested completion of all
started Lean work and existing paper-proof formalizations before pausing.
Finish this verification queue and its older final audits, then stop research.
Do not open new conjectures or resume the broader Q-II research goal.

User explicitly prohibited scripts for checking Lean. Session **51780** and its
owned shell/lake/Lean processes were terminated and their exit verified. The
active and prepared check wrappers were deleted. Do not recreate or run wrappers,
check loops, or batch scripts. Run each `lake --old env lean ...` command directly,
from `formal/`, one foreground Lean process at a time.

`FaithfulPositiveMeyerDegrees.lean` passed direct check **90918**, including all six
transitive axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`.
The local binder-substitution error from **6529** is fixed. Temporary prints are
removed; the module is wired, its README and review entries updated, and its card
moved to stage 3. Missing olean build **96410** passed for actual importers
`ArithmeticSharpAndTheHilbertAdjoint`, `MeyerFiniteJetAlgebra`, and
`MeyerCriticalTopAlgebra`. Its olean now exists; never rebuild it.

`PositiveMeyerDegreesCanForgetClasses.lean` passed direct check **85919** and all
four standard transitive axiom audits. The numeral-coercion error from **60922**
is fixed. It is cleaned, wired, and documented in the README, review, and stage-3
faithful-degree card. Missing olean build **20153** passed for the actual
critical-trace and finite-algebra importers. Its olean now exists; never rebuild it.
Historical results remain in
`/tmp/qii-verify-followup.tsv`; that log will no longer update automatically.

`GlobalArithmeticMajorantsSupplyBezout` now passed its actual-file check and all
eight standard transitive axiom audits. It is cleaned, wired, documented in the
review, and its card is stage 3. Global reserve gives Bézout, strict ampleness,
pointedness, convexity and generation on every compact source, and provably fails
RR. No olean needed yet. Aperture cone geometry failed only its pointedness proof: negative fibre
readings were not normalized. Explicit flipped-linear-map negation proofs now
replace that simplification, pending a direct recheck. Subsequent dependent leaves
have not yet been checked; the cancelled script did not reach them.

`MeyerSourceIntersectionSurface` has now passed its actual-file check and all
nine standard axiom audits, and is wired and documented. Its missing olean
for the actual degree/flow importers also passed and now exists. Temporary axiom
prints are removed. Never rebuild the olean.
Stage-3 card: `genuine-meyer-source-surface-has-linear-degree-riemann-roch.md`.

Also certified and wired: `MeyerHilbertSchmidtSource`,
`MeyerSharpConvolutionAlgebra`, HT `HilbertSchmidtTraceDefect`, and
HT `L2TranslationCyclicity`. Numerical-radical recheck passed. Missing numerical,
exponential-mass and positive-quadratic-cone oleans now exist; do not rebuild.

Two API files failed before their source corrections: smooth finite function sums
now use an explicit extensional rewrite; compact-open quotient separation now
uses actual `deningerArithmeticXiRangeClosed` as a local closedness instance.
`/tmp/QIISmoothCoercionAPIs.lean` and `/tmp/QIIRestrictedSurfaceAPIs.lean` need
direct rechecks. The latter now also probes the norm approximation extracted
from `Metric.mem_closure_iff`; the installed statement confirms the distance
orientation used in the boundary-density draft, so that draft needs no change.
The adjoint norm, adjoint characterization, and coordinate inner-product names
are now in a separate `/tmp/QIIAdjointAPIs.lean` probe, following the import
collision recorded below.
Corrected actual `SmoothFiniteReadingKernels` also needs a direct
check. The inverse, global-comparison injectivity, and high
simple critical-point input axiom audits already passed with standard axioms.

Significant unverified findings awaiting Lean: algebraic characters have no infinite tail; arbitrary
finite Xi projectors split every positive degree's energy; on the bounded source
carrier faithful-reserve RR is exactly critical simplicity, while reserve-flow
invariance there is unconditional. The general positive-degree infinite tail
remains open. Certified card
`../3-formalized/the-critical-meyer-trace-is-positive-but-selective.md`
describes the full critical-value trace degree.
`CriticalMeyerTraceDegree.lean` passed direct recheck **61269** and all ten
standard transitive axiom audits; it is cleaned and wired. Its API probe passed
direct check **87678**, including
the standard transitive axiom audit of the actual quasi-inverse theorem. This canonical
degree is positive and descended, but original-trace domination is exactly RH
and faithfulness additionally requires simplicity. It is not an arbitrary-degree
classification. The restricted theorem does not imply RH or critical simplicity.

New actual candidates, unverified and unwired:
`MeyerCriticalTopAlgebra`, `BoundedMeyerSourceSurface`,
`MeyerHilbertReserveFlowRigidity`, `BoundedMeyerFaithfulReserve`,
`OriginHilbertCohomologyObstruction`,
`InvariantOriginMassDoesNotBoundTheWeilTrace`, `MeyerHermitianDegreePart`,
`EveryFiniteMeyerJetGraphIsDenseInOriginHilbertSpace`,
and `FiniteMeyerProjectorsSplitPositiveEnergy`.
`MeyerQuasiInverseRadical` is now certified; its inversion/radical classification is in
`../3-formalized/meyer-trace-radical-is-the-quasi-inverse-radical.md`.
Their scratch copies and the earlier actual
candidate scratch copies remain until verification succeeds. The bounded-faithful
leaf has twelve axiom audit endpoints, including existence of any faithful positive
linear degree restricted to bounded classes iff critical simplicity. Paper cards record their current status.

Pending direct checks include bounded-orbit, adjoint/reserve,
finite algebra/projector/degree/character, boundary-density, and the eleven older
actual-file final checks previously listed in this card. Build a missing dependency
olean only for its actual importer, with a direct command. The boundary-density leaf
now also audits the exact classwise lower-bound criterion for origin square
mass: every representative has mass at least b iff b<=0.
No existing olean is rebuilt; no umbrella is compiled.

The flow module, its dependency olean, and the actual critical-trace importer
are certified. Static review of all
remaining new source candidates is complete; no additional paper-only finding
was developed during this verification pass.

The actual `FaithfulHilbertSchmidtSourceReserves.lean` candidate now also contains
`exists_meyerHilbertReserve_linear_degree_iff` and
`meyerHilbertSourceCone_riemannRoch_iff_linear_degree`, with twelve total audit
endpoints. They target exact representation of the reserve by a complex-linear
degree on arithmetic sharp squares, equivalent to RH plus simplicity and to RR.
Corpus novelty search and dependency-closed argument are recorded on its existing
unverified card. These are Lean candidates, not certified findings; use the actual
module, since its older scratch copy lacks these two corollaries.

The bounded-faithful actual module likewise includes
`exists_meyerBoundedHilbertReserve_linear_degree_iff` and
`meyerBoundedHilbertSourceCone_riemannRoch_iff_linear_degree`.
They target exact representation of the reserve on bounded sources iff critical
simplicity, equivalently its restricted RR condition. Its existing card records
the seven equivalent candidate assertions and the corpus novelty audit. Its older
scratch copy also lacks these two corollaries. No new analytic premise is added.

Flow check **24096** failed at three Lean normalization steps: unfolding a local
real multiplicity before casting, eliminating a trailing zero in the imaginary
probe, and beta-reducing the Mellin-injectivity goal before rewriting. These are
corrected. The same beta reduction is added to the unverified reserve-flow leaf.
Its older scratch copy lacks this correction.

`FlowInvariantMeyerMajorantsForceCriticality.lean` passed direct actual-file
recheck **28957**, including all five transitive audits with only the standard
three axioms. Prints are removed; it is wired, documented in the README and
review, and its card moved to stage 3. Its missing olean is needed by the actual
`CriticalMeyerTraceDegree` importer. No owned Lean process remains from this check.

Direct missing-olean build **6563** passed for
`FlowInvariantMeyerMajorantsForceCriticality.lean`. Its olean now exists; never
rebuild it. The actual critical-trace importer is now being checked directly.
The old `/tmp/QIIMeyerInvariantMajorantDraft.lean` and
`/tmp/QIIMeyerFlowNames.lean` files are already absent.

Actual critical-trace check **42274** failed. Required corrections: finish the
scalar-linearity reduction; replace the nonexistent `tsum_eq_zero` at three
zero-sum proofs; give the indicator function explicitly in the RH comparison.
Its failed audit output contains `sorryAx` from these errors and is not a
certificate. No owned Lean process remains from this check.

`/tmp/QIICriticalTraceZeroSums.lean` passed direct check **70311**, verifying
`tsum_congr`, `tsum_zero`, and the explicit indicator-function argument. All
reported critical-trace errors are corrected in the actual module. Its old
scratch copy lacks these corrections.

`CriticalMeyerTraceDegree.lean` passed direct recheck **61269** with only
`propext`, `Classical.choice`, and `Quot.sound` in all ten audits. Temporary
prints are removed; it is wired, documented in the README and review, and its
card is stage 3. No olean build is needed yet. Its old scratch draft and both
API scratch files have been deleted after verification.

Quasi-inverse check **62163** failed only on an unreduced `if True` in the
point-source probe. Its first endpoint audit was standard; the downstream
failed audits are not certificates. The actual proof now uses `↓reduceIte`.
The same visible simplification pattern was corrected in two point readings
of the unverified actual `MeyerAlgebraicCharacters.lean` candidate; its older
scratch copy lacks these corrections.

`MeyerQuasiInverseRadical.lean` passed direct recheck **13602** with only the
standard three axioms in all four audits. Prints are removed; it is wired,
documented in the README and review, and its card is stage 3. Its old scratch
draft is deleted. No olean build is needed yet. No owned Lean process remains.

The installed quotient Hausdorff instance explicitly takes
`[IsClosed (H : Set G)]`; the prepared local instance matches that API.
The actual global Xi closed-range theorem is certified and was read. The
corrected `/tmp/QIIRestrictedSurfaceAPIs.lean` probe is now checking directly;
next target is `ArithmeticSharpAndTheHilbertAdjoint.lean`.

Combined API check **40471** failed on an import collision:
`LambdaRingEffectivityAndHeckeLefschetzRigidity` and
`SectionEffectivityAndTheUniversalFloorLaw` both declare `PolarSurface.polarLift`
in their actual source files. The AOG `SectionsOnTheOrbitOfACycle` import brings
in the latter. Existing oleans are preserved.

The bounded-source candidate uses AOG only for `PolarSurface.restrict`.
Its surface can be constructed directly from the original pairing and the
proved fibre membership fields, avoiding that unrelated import. The corrected
restricted API probe removes AOG and checks `LinearMap.compl₁₂`; after that
probe passes, replace the candidate's restriction definition by those fields.
No theorem statement or analytic premise changes. The adjoint names are split
into a separate probe using exactly the actual adjoint module's root import.

Adjoint API check **46670** passed, verifying the norm identity, adjoint
characterization, and coordinate inner-product declarations.
Actual adjoint check **3494** failed at four proof steps: rewriting a dependent
Fin bound, an extra tactic after simplification had closed the goal, conversion
of the operator norm product to a square, and normalization of `starRingEnd`.
All four are corrected in the actual file; failed axiom output is not a certificate.
Direct adjoint recheck **35594** failed only at the lower-coordinate equality:
`congr 1` is required and itself closes the goal; only the subsequent explicit
lower-coordinate proof was redundant. Restored this one tactic in the actual
adjoint and bounded-adjoint candidates. The same dependent-index rewrite issue is corrected in
the actual bounded-orbit, bounded-surface, and bounded-faithful-reserve candidates.
The bounded adjoint proof also uses the corrected scalar conjugation step and
removes the redundant lower-coordinate proof. Their scratch copies are stale.
The corrected restricted API probe
and direct bounded-surface construction are required before the bounded-surface
branch is checked.
The restricted API probe now includes the full generic restriction constructor,
matching the existing source construction without importing the conflicting module.
Direct adjoint recheck **96392** passed with only `propext`, `Classical.choice`,
and `Quot.sound` in all three audits. The module is cleaned, wired, documented,
and its card moved to stage 3. Its old scratch draft and API probe are removed.
Its missing olean build **95594** passed for the actual
`FaithfulHilbertSchmidtSourceReserves` importer. That olean now exists; never rebuild it.
The certified `MeyerHilbertSchmidtSource` missing-olean build **47729** passed
for the actual reserve and bounded-orbit importers. Its olean now exists; never
rebuild it. The certified HT `HilbertSchmidtTraceDefect` missing-olean build
**31303** also passed for the actual reserve importer; its olean now exists and
must not be rebuilt. Direct actual-file reserve check **27716** failed only in
the bilinear self-value proof: generic `RCLike.re` did not match concrete
`Complex.re` during rewriting with an implicit source. A typed local identity
with explicit source now supplies that rewrite. The independent norm-defect,
zero-kernel, class-descent, ample-zero and pointedness audits were standard;
the failed file as a whole is not certified. Recheck now includes explicit
ampleness, additive-closure and scalar-closure audits, fifteen endpoints total.
Direct actual-file reserve recheck **4030** passed with only the standard three
axioms in all fifteen endpoint audits. The module is cleaned, wired, documented,
and its card moved to stage 3. Its old scratch draft is deleted. Missing-olean
build **80282** passed for the actual reserve-flow importer. Its olean now exists;
never rebuild it. Actual bounded-orbit check **23633** failed only because
`omega` treated the coerced newly constructed jet index as a separate variable.
The proof now explicitly changes its goal to `i + 1 < xiSupportMultiplicity rho`
before arithmetic. Failed endpoint audits are not certificates. Direct recheck
**20136** passed with the standard three axioms in all six audits. The core
bounded-orbit module is cleaned, wired, and documented; its old scratch draft
is deleted. Its card remains stage 2 because the algebra and reserve-flow
extensions are still unverified. The core's olean was explicitly confirmed
missing. Direct missing-olean build **75806** passed for the actual
`MeyerCriticalTopAlgebra` importer. Its olean now exists; never rebuild it.
Actual critical-top algebra check **47078** failed only at another newly
constructed-index coercion, in the highest-jet witness. Its equality is now
explicitly changed to `j.val = xiSupportMultiplicity rho - 1` before arithmetic.
The existing paper also states a complex subspace of genuine quotient classes;
the source-only submodule did not explicitly package that claim. The actual file
now defines `meyerCriticalTopCohomologySubmodule` and proves representative
membership, sharp and convolution closure, and nontriviality. These formalize
the already stated paper claim, with no new mathematical premise. Its audit
list now has fifteen endpoints. Direct actual-file recheck **71562** passed with
the standard three axioms in every audit. The module is cleaned, wired and
documented; its old scratch draft is deleted. The bounded-orbit card now awaits
only the reserve-flow extension. Missing-olean build **39547** passed for the
actual reserve-flow, bounded-surface and finite-energy importers. Its olean now
exists; never rebuild it. Direct actual-file check **72805** of
`MeyerHilbertReserveFlowRigidity.lean`, with seven endpoint audits, is the sole
owned Lean process. Wait for exit before any further Lean invocation.

The existing bounded-faithful paper explicitly asserts a strictly positive
adjoint-defect witness at any multiple critical zero. Its actual candidate now
packages that assertion as `exists_bounded_meyer_source_adjoint_defect_pos`,
including bounded/isometric membership, a nonprincipal class, zero ordinary
trace, and strictly positive reserve and squared adjoint defect. The trace
comparison criterion reuses this witness. This is formalization of the existing
paper assertion, not a new research direction; the candidate now has thirteen
audits and remains unverified. Its old scratch copy is stale.
The same visible newly constructed-index pattern is normalized explicitly in
the two unverified nilpotent-order inductions in `MeyerAlgebraicCharacters` and
`PositiveMeyerDegreesSeeReducedCriticalJets`. Their old scratch copies are stale.
User reiterated: write no Python scripts; use direct Lean edits
and direct `lake --old env lean ...` commands.

Reserve-flow check **72805** ended, but its output was unavailable after
compaction. Recovery check **50685** exposed only the final definitional
`conj`/`star` equality. Added `rfl`; direct check **35848** passed with only
the standard three axioms in all seven audits. Temporary prints and the
stale scratch draft are removed; the module is wired and documented, and
the bounded-orbit card is now stage 3. Its olean is confirmed missing and
needed by the existing `BoundedMeyerFaithfulReserve` importer.
Restricted-surface API check **26932** verified the direct restriction
constructor, all named APIs, the norm-approximation example and the three
dependency axiom audits. Only the quotient Hausdorff example failed: the
additive-subgroup coercion was not elaborated. Its local closedness instance
now uses the source submodule as a set directly, pending a recheck.
The verified direct restriction constructor now replaces the conflicting
AOG import in `BoundedMeyerSourceSurface`. No theorem statement changed.
Direct missing-olean build **31048** passed for the certified reserve-flow module.
Its olean now exists; never rebuild it. Direct bounded-surface check **56753**
failed at the source submodule's addition field: a term lambda consumed the
two membership hypotheses before the intended variables. Replaced it with
explicit tactic introductions. Downstream errors involved this failed
definition; its failed audit output is not a certificate. The independent
high simple-critical trace-one witness audit was standard.

### Remaining verification queue

All modules below are actual files under `ArithmeticCastelnuovoSeveri/`.
Rows explicitly marked certified have passed; all other rows remain unverified.

| Module | State |
|---|---|
| `ArithmeticMajorantConeGeometry` | Pointedness correction awaits direct recheck |
| `SmoothFiniteReadingKernels` | Corrected smoothness API probe, then actual recheck |
| `ArithmeticSharpAndTheHilbertAdjoint` | CERTIFIED: direct 96392, three standard axiom audits, missing-olean build 95594 passed |
| `FaithfulHilbertSchmidtSourceReserves` | CERTIFIED: direct 4030, fifteen standard audits, missing-olean build 80282 passed |
| `MeyerBoundedCenteredOrbits` | CERTIFIED: direct 20136, six standard audits, missing-olean build 75806 passed |
| `MeyerCriticalTopAlgebra` | CERTIFIED: direct 71562, fifteen standard audits, missing-olean build 39547 passed |
| `BoundedMeyerSourceSurface` | Direct 42119 cleared the binder cascade; only zeroth-jet/Mellin normalization remained, now explicitly rewritten; thirteen audits await recheck |
| `MeyerHilbertReserveFlowRigidity` | CERTIFIED: direct 35848, seven standard audits, missing-olean build 31048 passed; cleaned, wired, documented; bounded-orbit card moved to stage 3 |
| `BoundedMeyerFaithfulReserve` | Thirteen endpoints; includes explicit positive adjoint-defect witness and exact linear-degree representation |
| `MeyerFiniteJetAlgebra` | Seven endpoints; requires missing sharp-algebra olean |
| `MeyerFiniteProjectorAlgebra` | Four endpoints; requires finite-jet olean |
| `PositiveMeyerDegreesSeeReducedCriticalJets` | Six endpoints, including finite-weight converse |
| `MeyerAlgebraicCharacters` | Eight endpoints; point-reading normalization corrected |
| `PoissonBoundariesAreDenseInOriginMass` | Seven endpoints; requires missing HT translation-cyclicity olean |
| `OriginHilbertCohomologyObstruction` | Four endpoints; corrected closedness instance awaits API check |
| `InvariantOriginMassDoesNotBoundTheWeilTrace` | Seven endpoints; requires smooth-kernel olean |
| `MeyerHermitianDegreePart` | Seven endpoints; requires finite positive-degree olean |
| `EveryFiniteMeyerJetGraphIsDenseInOriginHilbertSpace` | Ten endpoints; requires boundary-density olean |
| `FiniteMeyerProjectorsSplitPositiveEnergy` | Fourteen endpoints; requires finite-degree, critical-top and projector oleans |

Older actual-file final checks also remain: `SourceConeBoundaryRigidity`,
`SourceConeBoundaryApplications`, `WeilEnergyIsUnboundedAtEveryAperture`,
`GradedSourceConeBoundaryRigidity`, `SourceConePrimitiveFaithfulness`,
`NumericalEquivalenceOnTheScalingSurface`, `SourceRiemannRochWithoutSymmetry`,
`ExactArithmeticSourceEffectivity`, `FiniteDegreeConesCannotSatisfyBezout`,
`PoissonPrincipalCyclesOnTheScalingSurface`, and AOT
`SourceSectionBoundaryRigidity`. Their oleans already exist and must not be rebuilt.
<!-- /qii-live-status -->

## Current evidence

Existing `AllApertureSourceRiemannRochAndCoercivityLaws` proves all-aperture RR for graded cones with negative reserves, and RR on compensated surfaces. Neither provides the requested cone with an independent Bézout law on the original surface. The existing nonnegative source-cone theorem identifies RR with the lower bound `Φ ≤ defect`.

The actual theorem `sourceCone_bezout_of_defect_le` uses the opposite bound `defect ≤ Φ`, together with Hodge index. Corrected the overview's reversed inequality and its unsupported Bézout claims for coercive mass cones; the Lean statements were unchanged.

## Conjecture loop

1. **Boundary rigidity.** For a nonnegative fibre-invariant source functional, RR and Bézout together force `Φ(x) = defect(x,x)` pointwise. Test this by translating each primitive source to the exact determinantal boundary `2 deg_H deg_V = Φ`.
2. **Linear degree limitation.** Fibre degrees alone do not see primitive negative-square directions. Identify the exact positive survivor: all degree-linear tests determine only the fibre quadrant, while Bézout requires the source boundary.
3. **Further source construction.** Use the rigidity result to test candidate source section theories, principal divisors, and payment cohomology; do not stop at the negative result.
4. **Full Bézout classification.** For nonnegative even fibre-invariant `Φ`, conjecture
   `Bezout(EΦ) ↔ ∀x y, δ(x,y)²≤Φ(x)Φ(y)`. Necessity uses balanced fibre lifts with
   degrees `sqrt(Φ(x)/2)` and the two source signs; sufficiency is hyperbolic AM–GM.
   This would identify the exact source contraction obligation without assuming Hodge index.
5. **No finite L² reserve at any aperture.** The Weil Rayleigh quotient is unbounded above
   on `realTestsAt r` for every `r>0`, even in every finite-dimensional reading kernel.
   Use an energy-dependent low grid within the fixed support aperture, together with
   the pole condition. The concentration and grid bounds force the contradiction `π≤1`
   if a mass-normalized energy ceiling holds. This proves failure of Bézout for every
   finite constant `c`, not just for a strict known lower floor.
6. **Signed reserves do not evade rigidity.** Prove that Bézout on a graded source cone
   itself forces `Φ≥0`, without assuming `Φ(0)=0`. Then RR and Bézout on the graded cone
   are equivalent to exact representation of the nonnegative defect.

## Open obligations

- An original-surface, all-aperture source section theory with RR supply and an independently proved Bézout/degree mechanism remains unproved.
- The proposed payment cohomology must have genuine additive/dimensional content; a Boolean rank encoding of a quadratic inequality does not discharge that obligation.
- Preserve unrelated work already present in this worktree.

## Boundary-rigidity paper proof

[PROVED HERE, paper and Lean; core and low-blind modules compile; transitive axiom audit clean.]
Write `δ(x,y)=polar(x,y)-pair(x,y)`.
Let `Φ` be nonnegative, even, and unchanged by adding either fibre. The source cone is
`EΦ={x: deg_H(x)≥0, deg_V(x)≥0, Φ(x)≤2 deg_H(x)deg_V(x)}`.

For any source `x`, translate its fibres to degrees `(Φ(x),1/2)`. This keeps both `Φ` and `δ`
unchanged and produces a member `y` of `EΦ` with `y²=Φ(x)-δ(x,x)`. Hence Bézout forces
`δ≤Φ`. Existing RR classification gives `Φ≤δ`. Both axioms therefore force `Φ=δ`.
Conversely exact equality and nonnegativity give Hodge index, RR, and Bézout by the existing
polar-surface theorems. The resulting cone is exactly the positive cone.

The strict cone has the same rigidity: when `Φ(x)<δ(x,x)`, put its polar capacity strictly
between these two values. The resulting class lies strictly inside the source cone but has
negative square. Thus removing the boundary cannot repair Bézout.

The full mixed classification is also proved on paper: Bézout is equivalent to
`δ(x,y)²≤Φ(x)Φ(y)` for all source pairs. For necessity lift `x,y,-y` to balanced degrees
`sqrt(Φ(x)/2)` and `sqrt(Φ(y)/2)`. Bézout bounds `δ(x,y)` above and below by
`sqrt(Φ(x)Φ(y))`. For sufficiency, hyperbolic AM–GM bounds the mixed polar capacity
below by the geometric mean of the two self capacities. No Hodge-index premise is
needed for this classification.

All fibre-linear degrees are nonnegative on every `EΦ`, irrespective of the defect. With
`Φ=0`, Bézout holds exactly when `δ` vanishes identically: both `prim(x)` and `-prim(x)`
belong to this cone, so their self and mixed intersections force `δ(x,x)=0`. Conversely
zero defect leaves just the nonnegative hyperbolic pairing in the fibre quadrant.

For `Φ=c∫f²`, the simultaneous RR/Bézout criterion is the exact identity `W(f,f)=c∫f²`
on the entire source subspace, not a lower bound. A concrete counterexample family uses
the existing `lowBlindTests a` at every `a>0`: choose `c=lowBlindCoercivity(a)/2`.
RR and ampleness hold by the proved coercive floor, while a nonzero test has strictly
greater Weil energy and supplies the strict negative-square cycle above. This is an
unconditional example on the original, uncompensated subsurface.

### Unbounded-energy strengthening

[PROVED HERE, paper and Lean; module compiles; transitive axiom audit clean.] At each `r>0`, prescribe zeros at the pole and
the finite grid `lowGridOf (horizonFreqEps r (max M 0)) r`. A nonzero real test with this
support and these zeros exists: take `2k+1` independent translates of a bump against
`k` complex conditions. If its Weil energy were at most `max(M,0)∫f²`, the proved
near-radical concentration law would give `π∫f²≤bandMass`. The grid bound gives
`bandMass≤∫f²`, a contradiction since `π>1` and `∫f²>0`. Thus the Rayleigh quotient
exceeds every `M` at every positive aperture. The energy-dependent grid avoids enlarging
the support aperture. Any additional finite set of transform zeros can be imposed.

Consequences: every finite `c∈ℝ` fails Bézout on `l2SourceCone c`, its strict interior,
and `gradedL2SourceCone c` over `realTestsAt r`. The all-aperture negative Chebyshev
reserve is an unconditional RR cone that unconditionally fails Bézout. This refutes
the review's inference from existence of some RR/Bézout cone to equivalence between RH
and Bézout on an arbitrary chosen RR cone.

More generally, no postprocessing `F(samples(f))` of a finite set of transform samples
defines a Bézout source cone. On the finite-blind source fibre its reserve is the constant
`F(0)`, whereas scaling a positive-energy blind test makes its Weil energy arbitrarily large.
Lift such a test to polar capacity `max(F(0),0)`. It is source-effective and has negative
square. This also excludes arbitrary offsets and the normalized reading
`F(samples(f))-F(0)`. The positive survivor is unbounded Weil energy even after finitely
many prescribed transform zeros, not merely failure of one proposed cone.

### Signed-source rigidity

[PROVED HERE, paper and Lean; module compiles; transitive axiom audit clean.] Suppose `Φ(x)<0`. Set
`p=√(-Φ(x)/2)>0` and lift `x` to fibre degrees `(p,-p)`. Its ample degree is zero
and its polar capacity equals `Φ(x)`, so it belongs to the graded source cone.
Let `c=2+max(Φ(0),0)`. The pure-fibre lift of zero with degrees `(c,1)` also belongs
to the cone: its ample degree is positive and its polar capacity `2c` pays `Φ(0)`.
Their defect is zero, and their intersection is `p(1-c)<0`. Thus graded Bézout
forces `Φ≥0`; normalization at zero is unnecessary.

Consequently, for every even fibre-invariant real-valued source functional, graded
Bézout is exactly nonnegativity plus the mixed contraction law. Graded RR and Bézout
together are exactly `0≤Φ=δ`. A negative reserve supplies unconditional RR but cannot
repair Bézout. This gives the sharp positive replacement for the signed-reserve route.

### Section-count application

[PROVED HERE, paper and Lean; transitive axiom audit clean; final plain-file audit pending.] The AOT `1×1` source obstruction matrix has
`sourceH0∈{0,1}` and defines exactly `sourceCone`. The boundary classification therefore
transfers unchanged. Moreover, for every additive constant `M`, pure-fibre degrees `(c,1)`
with `c=2+max(Φ(0),0)+max(M,0)` give a source-effective class with
`sourceH0(x)+M<x²=2c`. Thus the Boolean membership count cannot provide a surface RR
dimension-growth estimate. This does not invalidate its existing role as a cone encoding.

The obstruction is independent of the canonical class and Euler constant. For every `K,χ`
and every reserve, the Boolean counts fail the classical dimension inequality
`h⁰(x)+h⁰(K-x) ≥ x·(x-K)/2+χ` somewhere. Along `x=t(H+V)` the left side is at most two,
while the right side is `t²-t((H+V)·K)/2+χ`. Taking
`t=|((H+V)·K)|+|χ|+4` makes the right side strictly greater than two. No invariance or
positivity property of the reserve is needed for this stronger obstruction.

### Principal-divisor direction

The curve-side numerical radical is classified by the Frobenius ideal
(`radical_iff_eq_frobPolyTest`). The compact scaling surface instead has zero numerical radical.
Do not confuse the spectral vanishing radical with the kernel of every Weil pairing, or
use RH to identify them. An independently constructed motion relation must preserve the
intersection pairings needed by its degree argument; the necessary numerical-equivalence
bridge below compiles, with a clean transitive axiom audit. The later Meyer construction
provides actual principal representatives on a larger source carrier.

The broader corpus supplies a stronger lead: `RHTower.compactXiWeilPairing_left_radical_iff_zero`
in `RHTower/XiCompactPolarWeilRealization.lean` proves zero numerical radical on complex compact
polar tests unconditionally, using density in the absolute folded Xi divisor Hilbert space.
It is not merely the conditional positive-definiteness theorem in `InfiniteGenusLaw`.
Extending the density argument to unrestricted compact source inputs and identifying
its literal polarization with the real scaling `weilPair` proves numerical equivalence
on the existing scaling cycle space is equality. Genuine divisor movement must occur on a
richer source space before passage to these numerical classes.

The finite-reading conjecture has a dependency-closed paper proof and Lean draft: Weil energy
is unbounded in the kernel of every linear map from `realTestsAt r` to a finite-dimensional
real space, not only finite Fourier sampling. The translated-bump kernel construction applies
jointly to the given map, the pole, and the energy-dependent grid. This excludes arbitrary
postprocessing of finitely many linear observations (values, moments, nodes, or transform
samples) as a Bézout source reserve. The exact survivor is unbounded Rayleigh quotient in every
such kernel. The full generalized module compiles; its transitive axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

### Numerical-equivalence separation theorem

[PROVED HERE, paper and Lean; transitive axiom audit clean; final plain-file audit pending.] The literal real scaling pairing is
nondegenerate, without RH. Its proof uses the existing compact-polar density theorem:

1. A compact complex `C²` source has a square-summable Xi evaluation vector. Critical-line
   reflection is an isometry, and its reflected vector belongs to the folded divisor Hilbert
   space. Compact polar tests are dense in that space.
2. If its Weil pairing against every compact polar test vanishes, the reflected vector is
   orthogonal to a dense subspace containing itself. Its norm is zero. Injectivity of compact
   Xi evaluation then makes the source zero. The tested source need not itself satisfy the
   pole constraints; only the testing family does.
3. The Xi-copy polarization equals the zeta-carrier Weil pairing by the explicit
   `xiDivisorZetaCarrierEquiv` and its multiplicity identity. Absolute summability follows from
   the two square-summable evaluation vectors. This bridge retains the full complex mixed form.
4. For real compact sources the full mixed Weil pairing is real: the convolution is real and
   `WeilWorkPBAP.weilFullFunctional_ofReal_im` applies. A real source annihilating every real
   compact test therefore annihilates the real and imaginary parts of every complex compact
   test. Step 2 makes it zero.
5. A scaling cycle annihilating every cycle has both fibre degrees zero. Pairing it with pure
   test cycles then annihilates its real source, so step 4 makes that source zero. Its two
   remaining pole coefficients are zero as well.

Thus equality of all intersection readings is equality of the existing scaling cycles.
Any intersection-preserving translation in this cycle space is trivial. This is a necessary
scope restriction for a principal-divisor construction, not a proof that richer divisor
presentations cannot exist. The positive survivor is unconditional separation of every
scaling class by the intersection pairing, plus separation by compact polar tests on the
source side. The module compiles; its transitive dependency audit and Hecke applications remain pending.

The mixed defect radical is consequently exactly the fibre plane: a cycle annihilates every
source defect pairing precisely when its compact source is zero. Combining this with the
primitive-faithfulness criterion gives an exact AOT application on the full scaling surface:
for any fibre-invariant reserve, section-cone ampleness is equivalent to strict positivity
of the reserve on every nonzero compact source. The bridge and this corollary are drafted.

### Primitive faithfulness and ampleness

[PROVED HERE, paper and Lean; transitive axiom audit clean; final plain-file audit pending.] For any fibre-invariant reserve `Φ`,
ampleness of the nonnegative-fibre source cone is equivalent to the exact condition
`Φ(x)≤0 ⇒ δ(x,y)=0 for every y`. Necessity follows by translating `x` and `y` to zero
fibre degrees: the first lift is effective with ample degree zero, and their intersection
is `-δ(x,y)`. Conversely, an effective class of ample degree zero has both fibre degrees
zero. Its reserve is nonpositive, so the stated condition kills its defect and hence every
intersection. No evenness or nonnegativity premise is needed for this classification.

Consequently, a normalized reserve `F(Lf)-F(0)` from any finite-dimensional linear reading
fails ampleness at every positive aperture. The unbounded-energy theorem supplies a source
in `ker L` with positive Weil energy; its zero-degree lift is effective and not numerically
trivial. Together with the preceding Bézout obstruction, this excludes both required
intersection axioms for every such normalized finite reading. An arbitrary positive offset
may remove the ampleness obstruction, so the normalization is essential to this conclusion.
Strict source cones have positive ample degree and satisfy the stated ampleness axiom
vacuously; they remain subject to the independently proved Bézout obstruction.

### Exact arithmetic source cone at every aperture

[PROVED HERE, paper; Lean implementation pending.] The existing literal box-node identity
identifies `chebyshevSourceEnergy r R` with the diagonal defect on the odd source surface for
every `0<r<R`. Use this exact arithmetic reserve in the **graded** source cone. Its defining
formula refers only to fibre degrees, the archimedean gauge, and the Chebyshev/node-correlation
source. The cone equals the closed positive cone as a proved theorem, so it has RR at every
aperture without an aperture-dependent loss. Unlike the negative finite-mass reserve, its
Bézout condition is exactly the corresponding Hodge-index condition. Its ampleness condition
has the same equivalence. Over every positive aperture, either condition is equivalent to RH
by the existing odd-source exhaustion theorem.

This supplies an exact arithmetic presentation of the RR cone, but no independent positivity
mechanism: the required nonnegativity is the unresolved source-payment inequality itself.
The original nonnegative-fibre `chebyshevSectionCone` requires that inequality even for RR;
the graded cone moves it into Bézout/ampleness. This distinction corrects the review's
existential-cone inference without claiming that a renamed exact identity forces its sign.

The all-parity critical-deficit identity gives the same construction on **every**
`realTestsAt r`, not only the odd sector. Its reserve is
`(gammaBracket(0)-2)∫f² + biScaleLevyEnergy(f) + 4 horizonEnergy(f)` plus
`2∫_[0,2r] ccmPrimeDeficitIncoming(t) doubleGaugeDerivative(autocorr(f))(t) dt`.
Every term is an explicit arithmetic or archimedean source reading; the existing exact
identity proves equality to the defect without a sign premise. The graded cone therefore
has unconditional RR, while Bézout and ampleness are exactly source nonnegativity. This is
an exact all-parity presentation of the desired RR supply, not an independent proof of
positivity or the missing sheaf duality.

The exact arithmetic reserve cannot factor through any finite-dimensional linear reading,
even with arbitrary nonlinear postprocessing: such a factorization would make its value
constant on that reading's kernel, contradicting the proved unbounded Weil energy there.
The Lean draft includes this irreducibility statement and the all-aperture RH dictionaries.

The global cone itself is also irreducible to finitely many linear degrees, independently
of whether Bézout holds. It contains the ample class, whose square is positive. Every finite
reading fibre through that class contains a negative-square class, which is outside the exact
source cone. Thus membership cannot be constant on those fibres. More strongly, no effective
class's finite readings force effectivity: the same readings always admit an ineffective
class. This is a direct obstruction for the specific arithmetic RR construction, not merely
an implication contingent on its unresolved Bézout property.

### Arbitrary finite degree descriptions

[PROVED HERE, paper; Lean implementation pending.] Strengthen the source-reserve obstruction:
at every positive aperture, **every fibre of every finite-dimensional linear reading of
the entire scaling cycle space has self-intersection unbounded below**. Consequently no
nonempty effective set whose membership is determined by finitely many linear degrees
can satisfy Bézout, even with arbitrary nonlinear postprocessing of those degrees.

For a reading `L` of scaling cycles, impose jointly on a compact source `f` the conditions
`L(0,0,f)=0`, `pair((0,0,f),H)=0`, and `pair((0,0,f),V)=0`. The finite-kernel energy theorem
supplies such an `f` with positive Weil energy. Its source cycle `p` lies in `ker L` and
has `p²=-W(f,f)<0`. Given any `x` and target `M`, put
`t²=(max(x²-M,0)+1)/(-p²)`. The average of `(x+tp)²` and `(x-tp)²` is
`x²+t²p²<M`; at least one is below `M`, and both retain `L(x)`. Any nonempty union of
reading fibres therefore contains negative-square classes and fails Bézout on self-pairs.

This conclusion does not exclude infinitely many degree inequalities or a degree law on a
richer divisor presentation. Its positive survivor is the exact affine-fibre unboundedness
law, stronger than failure of any one finite-rank reserve or finite polyhedral cone.

[NEXT STRENGTHENING, paper argument to formalize.] The same affine-fibre obstruction can be
made arbitrarily small in source `L²` mass. Jointly constrain the finite reading, both pole
degrees, and pairing with a fixed base cycle `x`. The Rayleigh-kernel theorem supplies a
primitive `p=(0,0,f)` with `x·p=0` and arbitrarily large `W(f,f)/∫f²`. Rescale to
`t²∫f²=ε/2`; then `y=x+tp` has the same finite readings, source displacement mass below `ε`,
and `y²=x²-t²W(f,f)` below any prescribed target. This would show that even arbitrarily
small `L²` source changes preserving all chosen finite readings can destroy exact arithmetic
effectivity. The positive replacement must therefore retain stronger source regularity,
consistent with the Meyer topology distinction above.

## Next source questions

- The source-native theta-convolution lead already has a sharp topology obstruction in
  `RHTower/XiThetaConvolutionDefectTrilemma.lean`: theta convolution is injective with dense,
  nonclosed range on `L²`. Any continuous degree vanishing on that proposed principal image
  must vanish identically. A Hausdorff Hilbert quotient therefore loses the divisor data.
  The analytic entire quotient retains it, but its definition builds in `XiC` and is explicitly
  a comparison carrier. A principal-divisor construction must specify a stronger source
  topology and prove its comparison with compact scaling classes, not silently replace the
  analytic quotient by the zero reduced Hilbert cokernel.
- A stronger source carrier is already available: `DeningerMeyerSourceConvolution.lean`
  constructs literal convolution on the original all-weight Meyer source space and proves
  that the actual Poisson boundary range is an ideal. `DeningerMeyerConvolutionWeilTrace.lean`
  identifies the ordinary composition trace of compact source convolutions with the literal
  mixed Weil form, retaining both polar terms. This is more than the bare entire comparison
  quotient. Audit and build its direct scaling-surface application: for a Poisson boundary
  `g`, use the cycle `(-Re Mellin(g)(1), -Re Mellin(g)(0), g)`. Its two fibre degrees vanish;
  faithfulness identifies the boundary's convolution operator with zero, so its mixed Weil
  traces vanish. Sharp-stability of the boundary is required for the right radical. This
  should produce genuine source-defined principal representatives on a larger carrier,
  while compact-source injectivity prevents those representatives from lying in the original
  compact cycle space.
- Keep ordinary Weil trace and the full Hasse pairing distinct. The former reads eigenvalue
  values with multiplicity; the latter retains Jordan jets. The existing theta trilemma makes
  a local full Jordan block Hermitian only at a real **simple** divisor point. Identifying
  arithmetic sharp with the Hilbert adjoint could therefore demand more than RH. Search and
  audit the trace radical versus the actual Poisson ideal before treating this as a positive
  Hodge realization.

[PROVED HERE, paper; Lean draft.] Let `Z` be the literal Meyer Poisson map. On
`ℝ × ℝ × DeningerMeyerStrongLogTarget`, define degrees
`dH(a,b,g)=b+Re M(g)(0)` and `dV(a,b,g)=a+Re M(g)(1)`, and pair by their hyperbolic product
minus `Re Tr(Tg T(g′ sharp))`. The source-defined cycle
`P(f)=(-Re M(Zf)(1),-Re M(Zf)(0),Zf)` has both degrees zero. Faithful convolution gives
`T(Zf)=0`; source reflection sends `Zf` to `Z(Fourier(conj f))`, so both left and right trace
terms vanish. Adding `P(f)` therefore preserves every intersection reading. For the explicit
Xi-cap source, `M(Zf)(1)=Xi(1)=1/2`, hence `P(f)≠0`.

On compact smooth real sources, centered source Mellin moments are precisely the original
two pole moments, and the existing whole-source trace theorem gives exactly the original
scaling intersection. No identification of the entire C² carrier with the all-weight Meyer
source is claimed. A centered compact smooth source in `range Z` has Fourier transform zero
at every Xi zero, by the proved entire-quotient identity; compact Xi evaluation injectivity
then forces that source to vanish. Thus the larger carrier supplies actual nonzero principal
representatives while preserving the earlier compact rigidity. It does not yet construct
an effective sheaf or prove positivity of the descended pairing.

[NEXT STRUCTURAL STEP.] Package this representative pairing as a real `PolarSurface`,
using genuine source convolution bilinearity and critical-line divisor reindexing for
Hermitian symmetry. The centered Meyer Mellin map compares its trace directly with the
already proved `xiWeilPolarization_conj_symm`; no identification of arithmetic sharp with
the Hasse Hilbert adjoint is needed. Then its defect is the ordinary source trace, so the
source-trace sign criterion transfers to the enlarged intersection surface. The compact
comparison currently covers smooth real sources only; do not claim an embedding of every
compact C² test into the smooth Meyer carrier.

[NEXT CONJECTURE.] The polynomial Xi-cap orbit should give infinitely many independent
principal representatives, since its Mellin transforms are `P(s)Xi(s)`. Audit this exact
source statement, and distinguish the ordinary trace radical (zeroth values) from the
full Poisson kernel (all Hasse jets) at possible multiple zeros.

[PROVED HERE, paper argument; Lean pending.] The finite causal splitting supplies an exact
description of that distinction. At each Xi divisor point, its source section realizes an
arbitrary local jet packet and has zero jets at every other divisor point. Choose the packet
with value one and higher jets zero; an actual source representative `eρ` then has Mellin
values `1` at `ρ` and `0` elsewhere. The ordinary convolution trace satisfies
`Tr(Tg Teρ)=mρ M(g)(ρ)`. Testing the real Weil trace against `sharp(c eρ)` for arbitrary
complex `c` therefore detects the complete complex value `M(g)(ρ)`. Conversely, if every
such value vanishes, every ordinary product trace vanishes termwise. Thus the source trace
radical is exactly the kernel of all zeroth-value readings.

The genuine Poisson kernel requires all Hasse jets below each multiplicity to vanish.
Consequently these two kernels coincide exactly when every Xi zero is simple. If `mρ>1`,
the local packet with value zero and first derivative one supplies an actual source in the
ordinary trace radical but outside the Poisson boundary. If all multiplicities are one,
zeroth-value vanishing is the whole jet condition and faithful convolution forces a boundary.
The previously proved inserted Paugam trace detects the complete class and is the positive
replacement for this loss of information, but its alternating product is not the symmetric
Weil intersection. No simplicity or positivity hypothesis may be silently supplied.

[NEXT SOURCE AUDIT.] A linear degree on the actual source convolution algebra is different
from membership determined by finitely many linear degrees. Ordinary convolution trace is
complex-linear on the entire Meyer source space (all source operators are proved trace class),
vanishes on the Poisson boundary, and therefore descends to genuine source cohomology.
The Weil defect is its real value on the literal product `g * sharp(h)`. Formalize this positive
linear-degree representation while keeping its order obligation explicit: linearity does not
show that those product degrees are nonnegative. In particular ordinary sharp-square trace
positivity should require only RH, whereas identifying the full Hasse sharp with a Hilbert
adjoint would additionally constrain Jordan blocks. Do not confuse numerical removal of
higher jets with an assumption that the zeros are simple.

[PROVED HERE, paper; Lean draft.] The genuine source quotient has a nonzero square-zero
class at every multiple Xi point. At a point of multiplicity `m>1`, choose the actual finite
causal source with only its `(m-1)`st jet equal to one. It is not a Poisson boundary, since
that jet survives. Every jet of its convolution square below order `m` vanishes: the Hasse
product sum can have a nonzero summand only at total order `2(m-1)≥m`. At every other
point all jets vanish. Full-jet injectivity therefore makes the square a genuine boundary.
Conversely, when all multiplicities are one, a principal square has squared Mellin values
zero, hence all Mellin values zero, hence its source is principal. Thus square-root closure
of the actual Poisson ideal is exactly simplicity. This gives an algebraic positive survivor
for the information lost by ordinary degree; it is independent of the RH positivity issue.

[PROVED HERE, paper; Lean extension pending.] Ordinary source sharp-square degree is
nonnegative for every actual Meyer source exactly when RH holds, without any simplicity
condition. Under RH, every divisor point obeys `conj(1-rho)=rho`; the absolutely summable
trace expansion is therefore a sum of `|M(g)(rho)|²`, repeated by multiplicity. Conversely,
nonnegativity for all Meyer sources applies to centered smooth compact sources. The proved
CCM trace comparison identifies their diagonal trace with the literal source quadratic;
the existing all-aperture polar-multiplier criterion yields RH. This establishes the exact
order obligation on the genuine linear degree, separately from the higher-jet radical.

[PROVED HERE, paper; Lean extension pending.] Off-line negativity has an explicit actual
two-point source producer. For a divisor point `rho`, let `sigma=conj(1-rho)` and assume
`sigma≠rho`. The finite causal point sources `e_rho,e_sigma` have self trace zero and mixed
traces equal to the respective positive multiplicities: the first point source reads the
second source's Mellin value at the reflected point. Therefore
`Tr_W(e_rho-e_sigma,e_rho-e_sigma)=-(m_rho+m_sigma)<0`.
This gives a literal finite causal packet witnessing the order obstruction, rather than
only extracting a source existentially through the compact polar-multiplier criterion.
The packet proof needs the real trace bilinearity and exact reflected point evaluation;
it assumes neither simplicity nor unproved analytic admission.

[PROVED HERE, paper; Lean construction pending.] The enlarged Meyer representative carrier
itself has an unconditional real polar-surface structure. Centering Mellin transforms
identifies the complex source product trace with `xiWeilPolarization`; its proved Hermitian
symmetry gives symmetry of the real trace. Source convolution and its linear degree give
real bilinearity. The two compensated Mellin pole degrees then define the hyperbolic plane
exactly as in the compact scaling surface. Its defect is the real source product trace,
so Hodge index is equivalent to the sharp-square order condition above. Genuine Poisson
principal representatives lie in its numerical radical without a positivity assumption.
This packages the source extension within the existing surface machinery; it does not
identify the ordinary radical with the full Poisson ideal unless simplicity holds.

[PROVED HERE, paper; Lean draft pending.] Evaluation at the source origin supplies
a different, strictly positive square degree:
`(g * sharp(g))(0) = integral(exp(t) * normSq(g(t)))`.
This follows formally from literal convolution and `sharp(g)(t)=exp(-t)*conj(g(-t))`.
`deningerMeyerSourceConvolution_integrable` gives integrability of this literal product;
all-weight source smoothness gives continuity. A zero nonnegative integral forces zero
almost everywhere, then everywhere by continuity, hence `g=0`. Its exact obstruction to cohomological descent
is then concrete: choose the nonzero Xi-cap Poisson boundary `g`; the convolution ideal
makes `g * sharp(g)` a boundary as well, but its origin value is positive. Thus a faithful
source-mass degree cannot vanish on genuine principal boundaries. The source admission
dependency is now checked; `/tmp/QIIMeyerOriginDraft.lean` contains the complete proof draft,
including an explicit positive-degree boundary and the failure of cohomological descent.

[CONJECTURE; full sharp-jet proof to formalize.] A faithful positive linear degree on the
entire genuine Meyer cohomology exists exactly when RH and simplicity both hold. Here
faithful means positive real degree on every sharp square of a nonprincipal source.
For an off-line point, its actual one-point source is nonprincipal, but its sharp square
is principal because reflection moves its full jet support to a disjoint point. At a
multiple point, the top-jet source is nonprincipal and its sharp square is principal:
either reflection moves the block, or both factors start at order `m-1`, so their product
vanishes below order `m`. The full sharp-jet formula follows from the already proved
`deningerMeyerStrongLogMellinJetLM_J` and `deningerMeyerStrongLogMellinJetLM_conj`.
Conversely RH makes ordinary trace a sum of nonnegative squared values, and simplicity
makes some value nonzero for every nonprincipal source, hence its trace strictly positive.
This concerns faithful positivity on the full quotient; ordinary semidefinite trace
positivity alone requires only RH and must not be strengthened silently to simplicity.

The associated algebraic criterion to test is sharp-square-root closure of the genuine
Poisson ideal: `g * sharp(g)` principal should force `g` principal exactly under RH plus
simplicity. Ordinary square-root closure, already in the radical-module draft, requires
only simplicity. Passing instead to the zeroth-value numerical ideal removes the extra
simplicity requirement. This identifies the precise quotient on which a positive faithful
intersection degree should live; retaining all higher jets changes the required theorem.

[PROVED HERE, paper; Lean draft.] The exact arithmetic RR set is closed under addition
if and only if Hodge index holds. This separates membership-level RR supply from an
effective-section monoid. On any polar surface, if a primitive `p` has `p²>0`, set
`t=√(p²/2)` and `d=H-V`. Both `p+td` and `-p+td` have square zero and ample degree zero,
so both lie in the full positive cone. Their sum is `2td` with square `-8t²<0`, contradicting
additive closure. Conversely Hodge index gives pairwise Bézout, so expanding `(x+y)²`
proves closure. Applying the exact arithmetic identity gives the local Hodge-index criterion
and the global equivalence with RH. A source-only RR formula therefore must not be presented
as an independently established additive theory of sections.

- [PROVED HERE, paper; Lean draft written.] Glue the exact all-parity source cones over aperture into a source-defined subset of the
  original `ScalingCycle` space, using compact-support exhaustion. Its equality to the global
  positive cone follows from the exact arithmetic formula. Audit the precise remaining
  Hecke/Adams stability obligation using `scalingSurface_adams_riemannRoch_iff`: stability
  at one scale greater than one, together with RR and nonnegative ample degree, already
  forces Hodge index. Thus the new RR supply must not be described as an independently
  proved motion-compatible effective theory.
- [PROVED HERE, paper; Lean draft written.] The Hecke principal-difference test is strengthened
  below to exact fixed spaces and freedom of every finite distinct-scale orbit. Numerical
  nondegeneracy rules out nonzero principal numerical relations inside those compact orbits.
  A richer representative carrier remains necessary.

### Scaling and Hecke fixed classes

[PROVED HERE, paper; Lean draft written.] The corpus already proves that a compact
source satisfying `f(u)=c f(u+t)` at any nonzero lag is zero. Hence every eigenvector of
`scalingAction t`, for `t≠0`, lies in the fibre plane. Its coordinates obey exactly
`(exp(t/2)-c)a=0` and `(exp(-t/2)-c)b=0`. In particular its fixed space is zero.
For positive `q≠1`, the normalized Adams fixed space is therefore zero. The unnormalized
Hecke operator fixes exactly the vertical fibre line: its source must vanish, its horizontal
raw coordinate scales by `q`, and `heckeCorrespondence_V` supplies the converse.

With numerical nondegeneracy, these are also the exact numerically fixed spaces. Thus
nontrivial compact Hecke or Adams motion cannot be mistaken for principal numerical
equivalence. This distinguishes an isometry acting simultaneously on both intersection
arguments from a principal move preserving every reading with the other argument fixed.

The corpus's `linearIndependent_real_translate` strengthens this to every finite motion
relation. If a scaling class has nonzero compact source, its images under any distinct
logarithmic scales are linearly independent: project a putative relation to the compact
source and apply translation independence. Distinct positive Adams scales inherit this by
injectivity of the logarithm; Hecke scales inherit it after multiplying coefficients by the
nonzero square roots. Numerical nondegeneracy then makes every numerically trivial finite
Adams or Hecke combination have all coefficients zero. This excludes polynomial principal
relations on a nonzero compact source, not only individual fixed differences. Its positive
survivor is the exact freedom of every finite distinct-scale orbit.

## Verification queue

### Finite-field calibration and absolute spectral reserves

[PROVED HERE, paper; Lean draft pending verification.] The existing Rosati source cone has
Bézout for every finite `CurveDatum`, including the golden datum: the mixed defect is the
inner product of one Frobenius evaluation vector with the reflected second vector, and the
reflection permutes the finite spectrum. Cauchy–Schwarz therefore bounds its square by the
two Rosati masses without a unitarity premise. Its RR condition remains exactly vanishing
of the reflection defect; over all windows this is the existing unitarity criterion. If one
mass vanishes, the mixed bound forces that source into the defect radical, so ampleness is
also unconditional. At window `{1}`, the golden datum therefore has Bézout and ampleness but
fails RR. The matrix-section cone equals this Rosati cone, so the same conclusion applies
to its source reading. The draft proves the mixed pairing identity directly from the graph
entry formula and reflected power sums; it does not infer mixed control from a diagonal
upper bound alone. The finite complex Cauchy–Schwarz scratch proof compiled successfully.

The compact Xi Hilbert realization suggests the parallel infinite-dimensional calibration:
the squared absolute evaluation norm defines a cone with unconditional Bézout and ampleness,
whereas RR would require its reflection gap to vanish. This reserve is spectral, so it does
not supply the independently arithmetic degree mechanism requested by Q-II. The comparison
should explain why finite Frobenius readings can suffice for the curve quotient while the
proved affine-fibre obstruction excludes finite readings of the full scaling surface.

[FURTHER ARITHMETIC PRODUCER TO AUDIT.] An independent Bézout cone alone should also come
from an arithmetic quadratic majorant of the absolute Weil form, using Lévy energy,
squared pole moments, and an absolute prime-correlation budget. The missing equality with
the signed reserve would remain the RR obligation. The relevant generic paper lemma is:
if a quadratic form `Q` dominates `|δ(v,v)|` for every `v`, then
`δ(x,y)²≤Q(x)Q(y)`. Indeed, add `δ(x+ty,x+ty)≤Q(x+ty)` to
`-δ(x-ty,x-ty)≤Q(x-ty)`; polarization cancels the mixed terms of `Q` and gives
`0≤Q(y)t²-2δ(x,y)t+Q(x)` for all real `t`, so the discriminant is nonpositive.
This argument requires a genuine quadratic majorant, not an arbitrary nonlinear diagonal
bound.

[PROVED HERE, paper; Lean draft pending.] The corpus's unconditional floor supplies an
actual arithmetic majorant without another analytic premise. Put `C(r)=10+72*exp(r)` and
`Q_r(f)=criticalDeficitSourceEnergy(r,f)+2*C(r)*integral(f²)`. The proved
`realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp` says
`δ(f,f)≥-C(r)*integral(f²)`. Thus `Q_r(f)-δ(f,f)=2*C(r)*integral(f²)≥0` and
`Q_r(f)+δ(f,f)=2*(δ(f,f)+C(r)*integral(f²))≥0`. The exact arithmetic identity makes
`Q_r` a genuine quadratic reserve; the preceding polarization argument gives mixed Bézout.
Zero reserve forces the defect radical, giving ampleness as well. In fact
`Q_r≥C(r)*integral(f²)`, so zero reserve has zero source. RR fails at every positive aperture:
the sharp RR criterion would require `2*C(r)*integral(f²)≤0` for every source, contradicted
by any nonzero compact test. This yields an independent arithmetic Bézout cone on the
original pairing, with its precise RR obstruction. Unlike a finite L² reserve alone, it
retains the full unbounded arithmetic source energy. No claim of simultaneous RR and Bézout
is made.

### Removing source symmetry

[PROVED HERE, paper and Lean; transitive axiom audit clean; final plain-file audit pending.] Evenness of the reserve is unnecessary
for the RR classification. For every fibre-invariant real reserve, graded RR is equivalent
to `Φ(x)≤δ(x,x)` for every source. For necessity, if `δ(x,x)<Φ(x)`, choose a polar
capacity `c` strictly between them and fibre degrees `b=|c|+1`, `a=c/(2b)`.
Then `2ab=c` and `a+b>0`. The resulting lift has positive square but is not effective;
its negative has negative ample degree and is also not effective. For sufficiency, apply
the source bound to whichever of `x` and `-x` has nonnegative ample degree. No comparison
between the two reserve values is used.

Nonnegative-fibre closed and strict cones only see `Φ₊=max(Φ,0)`, since their polar
capacity is nonnegative (strictly positive in the strict cone). Their RR condition is
therefore exactly `Φ₊≤δ`. Both RR and Bézout hold exactly when `Φ₊=δ`; for graded cones,
both hold exactly when `0≤Φ=δ`. These statements impose neither source evenness nor an
initial sign premise. Negative reserves on zero-defect sources are invisible to the
nonnegative-fibre construction, but graded Bézout excludes them.

For Bézout alone the corresponding asymmetric mixed law is
`max(δ(x,y),0)²≤Φ₊(x)Φ₊(y)` for all sources. Balanced boundary lifts give necessity;
hyperbolic AM–GM gives sufficiency. Only when the reserve is even can this law be replaced
by the symmetric square bound `δ(x,y)²≤Φ(x)Φ(y)`. This identifies exactly where symmetry
was used in the earlier classification. Formalization must retain this distinction.

| Module | Status |
|---|---|
| ACS `SourceConeBoundaryRigidity` | Compiled; main transitive axiom endpoints clean. |
| ACS `SourceConeBoundaryApplications` | Compiled; main transitive axiom endpoint clean. |
| ACS `WeilEnergyIsUnboundedAtEveryAperture` | Compiled; generalized finite-kernel and no-go endpoints axiom-clean. |
| ACS `GradedSourceConeBoundaryRigidity` | Compiled; RR/Bézout endpoint axiom-clean; umbrella wired. |
| ACS `SourceConePrimitiveFaithfulness` | Olean compilation and transitive axiom audit passed; final plain-file audit pending. |
| ACS `NumericalEquivalenceOnTheScalingSurface` | Revised olean compilation and transitive axiom audit passed. Explicit source functions and split realification avoid elaboration timeouts without raised limits. Final plain-file audit pending. |
| ACS `HeckeClassesDoNotMoveNumerically` | Direct plain-file check and transitive axiom audit passed. Exact eigen/fixed spaces and freedom of every finite distinct-scale orbit checked; temporary directives removed; umbrella wired. |
| ACS `FiniteDegreeConesCannotSatisfyBezout` | Olean compilation and transitive axiom audit passed, including the small-L² affine-fibre strengthening. Final plain-file audit pending. |
| ACS `ExactArithmeticSourceEffectivity` | Olean compilation and transitive axiom audit passed, including global aperture gluing, exact all-parity arithmetic RR, finite-reading obstruction, additive-closure criterion, and one-scale Adams criterion. Final plain-file check pending. |
| ACS `ExactSourceEffectivityRequiresInfinitelyManyDegrees` | Direct plain-file check and transitive axiom audit passed. Temporary audit directives removed; umbrella wired. |
| AOT `SourceSectionBoundaryRigidity` | Olean exists and import/transitive axiom audit passed. Includes signed/asymmetric boundaries and the canonical-class-independent Boolean dimension obstruction. Final plain-file audit pending. |
| AOT `AllApertureChebyshevSourceEffectivity` | Direct plain-file check and transitive axiom audit passed. All-aperture odd arithmetic RR and exact payment criteria checked; temporary directives removed; umbrella wired. |
| ACS `SourceRiemannRochWithoutSymmetry` | Scalar scratch, olean compilation, and transitive axiom audit passed; umbrella wired; final plain-file audit pending. |
| ACS `PoissonPrincipalCyclesOnTheScalingSurface` | Olean compilation and transitive axiom audit passed. Genuine linear trace degree, nonzero principal representatives, compact-boundary rigidity, and the exact compact smooth comparison are checked. Final plain-file audit pending. |
| AOT `RosatiSectionsHaveBezoutWithoutUnitarity` | Paper proof and Lean draft. Mixed reflected evaluation, universal Bézout and ampleness, exact local RR condition, and golden matrix-section counterexample; compile pending. |
| ACS `MeyerNumericalRadicalAndMultiplicity` | Paper proof and Lean draft. Actual single-jet sources, exact ordinary source and cycle trace radicals, equality with the principal kernel iff simplicity, source sharp-square positivity iff RH, and nonprincipal square-zero classes at every multiple zero. Its import requires the principal-cycle module's olean. |
| ACS `FiniteReadingsAndMassCannotSupplyBezout` | Paper proof and Lean draft. Unit-mass unbounded energy in each finite linear kernel; arbitrary nonlinear functions of finite readings and exact L² mass fail closed, strict, and graded source-cone Bézout. |

`/tmp/QIIBatchAudit.lean` completed successfully. All queried endpoints in the numerical,
primitive-faithfulness, graded, asymmetric, and section modules use only `propext`,
`Classical.choice`, and `Quot.sound`. The same holds transitively for the Meyer source trace,
faithful convolution representation, Poisson ideal, and entire-quotient comparison used below.

`/tmp/QIIMeyerNames.lean` also passed. Finite causal source sections, their off-block
vanishing, full-jet cohomology injectivity, and the explicit Xi-cap Mellin identity all have
the same clean transitive axiom list. Thus the local jet producers used by the new radical
comparison do not import an unproved analytic input.

The small-source-mass affine-fibre strengthening compiled in the finite-degree module.
Its global and exact-effectivity consequences in
`ExactSourceEffectivityRequiresInfinitelyManyDegrees` passed the final plain-file check and
transitive axiom audit. The exact source, finite-degree, global exclusion, and principal-cycle
modules are now wired into the ACS umbrella; the umbrella is not compiled.

`/tmp/QIIMeyerPrincipalAudit.lean` passed: every queried endpoint in the principal-cycle,
exact arithmetic RR, and finite-degree modules depends only on `propext`, `Classical.choice`,
and `Quot.sound`. Remaining leaves are queued for direct checks with temporary axiom
directives; remove those directives once the corresponding file passes.

Further proof drafts awaiting their first Lean checks:

- `/tmp/QIIMeyerSurfaceNames.lean`: centered Mellin polarization and real scalar bilinearity.
- `/tmp/QIIMeyerSurfaceDraft.lean`: full Meyer polar surface, actual degree source RR,
  principal/numerical distinction, and explicit negative reflected two-point packets.
  Imports the radical/multiplicity module, whose olean will be needed when this draft is
  promoted to its source module.
- `/tmp/QIIArithmeticMajorantNames.lean` passed, including the generic quadratic-majorant
  proof. Its application is now `ACS/ArithmeticMajorantsSupplyBezout.lean`: independent
  arithmetic Bézout/ample cone, strict mass floor, and failure of RR. Direct source check
  and temporary axiom audit remain pending; it is not wired yet.
- `/tmp/QIIMeyerOriginNames.lean` passed, including the actual convolution integrability
  and boundary-ideal axiom audits. The application is now
  `ACS/OriginDegreeDoesNotDescendThroughPoissonBoundaries.lean`: exact positive origin
  degree, positive-degree Poisson boundary, and failure of descent. Direct source check
  and temporary axiom audit remain pending; it is not wired yet.
- `ACS/FaithfulPositiveMeyerDegrees.lean`: reflected full jets, exact single-jet sharp-square
  classification, sharp-square-root closure of the actual Poisson ideal iff RH plus
  simplicity, and existence of any faithful positive linear cohomological degree iff
  those same two conditions. Direct actual-file check and all six standard axiom
  audits passed. The formalized card is
  `../3-formalized/faithful-positive-meyer-degrees-require-simple-critical-zeros.md`.
- `/tmp/QIIMeyerPointDegreeDraft.lean`: an unconditional positive linear degree on the
  genuine quotient, with an explicit nonprincipal null source. Hardy supplies a critical
  divisor point; its zeroth Mellin evaluation sends sharp squares to squared norms.
  The conjugate divisor point is distinct, since the Xi divisor misses `1/2`, and its
  actual point source has degree zero while remaining nonprincipal. Thus existence of
  some nonzero positive linear degree is already unconditional; it does not supply the
  original mixed intersection or faithfulness.
- `/tmp/QIIGlobalPrimeMajorantDraft.lean`: the weighted correlation estimate and its
  full prime-sum bound. `/tmp/QIIGlobalMajorantNames.lean` checks their supporting APIs.
- `/tmp/QIIQuadraticSourceConeStructure.lean`: positive quadratic reserves give additive
  source cones containing zero and closed under nonnegative scaling. Its direct scratch
  check is queued; the pointed/generating arguments remain on the global-majorant paper card.
- `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BezoutCostsTwiceTheNegativeReserve.lean`: complete proof attempt for the exact factor-two
  boundary, its compensated Hodge-index equivalence, and closed/graded RR criteria.
  It imports the new majorant leaf and has not run. Promote it to an actual module
  before building that missing dependency olean; never rebuild an olean that exists.

These drafts have no placeholders. Scratch names must pass before the corresponding
source modules are installed, and each installed module still needs its direct file check,
axiom audit, and umbrella import.

[PROVED HERE, paper; Lean pending.] The aperture-gluing limitation of the first majorant
can be removed. Exponentially weighted source mass bounds every translated correlation
by `exp(-|a|)` times that mass. The actual prime sum is then bounded by twice the
summable three-halves von Mangoldt mass. Together with the archimedean Lévy lower bound
and the exact two pole moments, this gives one global quadratic arithmetic reserve
dominating both signs of the original defect. Its source cone has global mixed Bézout
and ampleness and fails RR by a strict positive reserve. Exact formulas and the complete
paper proof are in `../2-fully-proven/a-global-arithmetic-majorant-for-the-scaling-surface.md`.
The weighted correlation, actual prime-sum landing, and global cone still need Lean proofs.

[PROVED HERE, paper; Lean pending.] The factor two in the majorant has an exact
structural meaning. For a nonnegative symmetric fibre-annihilating quadratic form `R`,
the original closed or graded source cone with reserve `delta+2R` has Bézout iff
`delta+R>=0`, equivalently Hodge index for the pairing compensated by `R`.
Graded RR holds iff `R=0` on the diagonal; closed RR additionally requires
`delta>=0`. The proof uses the absolute diagonal majorant criterion and the exact
positive-part boundary laws. Full paper proof and scalar threshold interpretation:
`../3-formalized/bezout-costs-twice-the-negative-reserve.md`. This exact theorem
must be formalized after the majorant leaf passes; no optimal-floor attainment is assumed.

Verification continuation: the first Meyer surface scratch audit found a missing
`ContinuousLinearMap` namespace opening and a conjugated-half simplification failure.
Both have explicit source-based fixes; real scalar linearity itself passed. The Rosati
audit was stopped before completion to replace its implicit permutation reindexing
function by an explicit one. It still requires a complete direct check, as do the
radical/multiplicity and unit-mass leaves. The quadratic-majorant scratch audit passed and its application source is installed.
The current sequential scratch audit continues with the origin, corrected surface,
sharp-root, and global-majorant APIs before promoting those drafts. No new application theorem in those drafts is yet reported as Lean-checked.
The corrected Meyer polarization scratch proof then reduced to the definitional
`star`/`starRingEnd` equality; an explicit `rfl` is added and still awaits its retry.
The current serial direct-check batch starts with `ArithmeticMajorantsSupplyBezout`,
then origin descent, Rosati, numerical radical, and the unit-mass obstruction, followed
by the remaining scratch API checks. It stops at the first error; do not assume later
files ran. Temporary axiom directives remain until their corresponding source passes.
The first direct majorant check found only a right-scalar `mul`/`smul` normalization
goal in `defectLinearMap`. It is corrected with `smul_eq_mul`; the direct check is
running again before the remaining files. The generic majorant, mass floor, strict
ample-zero result, and RR obstruction printed clean standard axiom lists, but the
mixed bound and Bézout result must not be certified until this corrected check passes.

[PROVED HERE, paper; Lean draft written.] Normalizing the positive-mass
finite-kernel witnesses gives unit-L²-mass sources of arbitrarily large Weil energy in
every finite linear reading kernel. Therefore even an arbitrary nonlinear reserve
`F(L(f), integral(f²))` fails source-cone Bézout: on these witnesses its value is the fixed
number `F(0,1)`, while the defect is unbounded. This is stronger than excluding finite
scalar L² coefficients. It does not exclude every arbitrary membership rule using mass:
for example, a rule supported only at source mass zero can retain the pure fibre quadrant.
The precise target remains a source cone with an available fibre lift for every source.

The `/tmp/QIIBoundaryAudit.lean` run printed clean axiom lists but exited nonzero because a
scratch `#check` incorrectly qualified the global name `integral_complex_ofReal`. That scratch
name is corrected; no theorem failed. `/tmp/QIINumericalNames.lean` passed with the global
integral lemma and the exp/log names. Final plain Lean audits, remaining
umbrella imports, and the finite-degree failed-route closure are still pending.

## Related ongoing work

### Flow-invariant majorant frontier

[CONJECTURE; exact source landing pending.] A finite nonnegative reserve on the
actual Meyer source which supplies the absolute mixed trace bound and is invariant
under centered dilation should already force RH, without an RR premise or a
faithfulness premise. Fixed point sources and their imaginary multiples recover the
real and imaginary parts of each Mellin evaluation from the mixed trace. The mixed
bound therefore controls that evaluation by a finite multiple of the square root of
the reserve. The evaluation has centered character `exp(t*(rho-1/2))`, so a nonzero
real exponent contradicts invariance.

The corpus already proves the abstract eigenfunctional step and its quotient version
in `RHTower/Deninger/DeningerMeyerInvariantEvaluationGaugeFrontier.lean`, read in full.
Do not duplicate that argument. The new obligation is the exact point-source trace
landing and the reserve-to-gauge construction, then an unconditional equivalence
using ordinary trace for the converse under RH. Applying the same boundary to the
original compact carrier requires a separate bridge to the proved universal-probe
translated-pairing criterion in
`BiScaleUncertainty/WeilLagPacketCancellationAndPositivity.lean:1269`.
No such bridge or invariance of the new exponential-weight majorant is assumed.

### Further source-sign conjecture

[CONJECTURE; dependency audit pending.] The continuous `apertureH1ChebyshevCorrection`
should have a sharp first-prime signature transition, rather than being a nonnegative
cohomology dimension. For odd tests supported below `log(2)/2`, its prime correlations
vanish and the correction is exactly the nonnegative rank-one pole charge. Above that
aperture, localize two small packets about `±log(2)/2`; keep their total correlation support
below `log(3)` so every node except `2` vanishes. An even local packet, extended oddly about
the origin, has correlation at `log(2)` equal to minus its squared mass. An odd local packet,
extended oddly with the opposite sign convention, gives plus its squared mass. Imposing
the one pole moment does not remove the infinite-dimensional local packet space. This
suggests infinite positive and negative index for the continuous correction immediately
after the first prime. Search and verify the exact source constructors, support exclusions,
and pole constraint before claiming this theorem. It would distinguish weighted aperture
correction from the genuinely finite prime-node count and from any new sheaf obstruction.

The proposed positive survivor is sharper than mere indefiniteness. With
`a=log(2)/2` and a sufficiently small local packet `h`, the two constructions
`F_-(t)=h(t-a)-h(t+a)` for even `h` and `F_+(t)=h(t-a)+h(t+a)` for odd `h`
have source mass `2 integral(h²)` and prime-two correlation respectively
`-integral(h²)` and `integral(h²)`. Keep their total correlation support below `log(3)`
and impose the single odd pole moment. The exact correction then equals
`-vonMangoldtAtom(2)*integral(F_-²)` or
`vonMangoldtAtom(2)*integral(F_+²)` on the corresponding packet subspace.
Disjoint reflection of arbitrarily many small translates in a positive half-interval
produces independent even or odd local packets; one linear pole condition leaves
arbitrarily large finite-dimensional subspaces. At and below `r=a`, all prime
correlations vanish, including the endpoint overlap, so only the rank-one pole charge
remains. Exact support, parity, mass, correlation, and finite-kernel constructors are
the remaining formal proof obligations.

The independent `biarithmetic-geometry-foundations` card audits the proposed ordinary
dimension identity `h⁰-h¹=E(s)` and its weighted arithmetic replacement. It already records
the completed `BiarithmeticGeometry/ArithmeticEulerCharacteristic.lean` result, with direct
checks and clean axiom audits. Read that module fully. Its `no_dimension_model_for_boxDefect`
refutes literal B1, and `boxDefect_eq_degree_sub_log_card` / `boxDefect_all_apertures` give
the exact integer-degree-minus-log-torsion replacement and continuous cell evolution.
Applied this correction to the review's Mechanism B and action list. No duplicate formalization
was added. These identities do not themselves construct the requested payment sheaf or prove duality.

## Log

- 2026-10-25 — Read attachment and full review; discovered existing all-aperture RR results and the opposite inequalities governing RR versus Bézout. Began boundary-rigidity audit.

Verification update: `ArithmeticMajorantsSupplyBezout` passed its direct file check and
all six main axiom audits with only the standard axioms. It is wired, documented,
and its card is in `3-formalized`. The origin-degree check stopped on a reducible
`RCLike.re`/`Complex.re` integrability normalization; an explicit `change` repairs
that mismatch. Later files in that serial batch did not run.

The factor-two draft is now an actual module, still unchecked and unwired.
`/tmp/QIIGlobalArithmeticMajorantDraft.lean` now contains the complete global
reserve, weighted bilinear construction, original-pair mixed bound, Bézout,
ampleness, strict ample-zero conclusion, RR obstruction, addition/scaling closure,
generation, and pointedness proof attempts. The generic cone scratch file now
also proves generation for every finite fibre-invariant threshold with `Phi(0)<=0`.
These drafts still require their serial direct checks and axiom audits.

`OriginDegreeDoesNotDescendThroughPoissonBoundaries` passed its corrected direct
check and all five main axiom audits, with only standard axioms. It is wired and
documented; exact proof and positive survivor are recorded in
`../3-formalized/positive-origin-degree-does-not-descend-through-poisson-boundaries.md`.
Current serial checks have advanced to the Rosati leaf.

Further positive survivor, paper proved: finite causal jet blocks admit an exact
classification of positive Hermitian degree restrictions. All off-line blocks and
all positive-order critical jets are invisible; the remaining critical values have
nonnegative real weights. See
`../2-fully-proven/positive-degrees-see-only-reduced-critical-jet-blocks.md`.
The proof uses normalized actual jet classes, Hasse convolution, Cauchy–Schwarz,
and descending nilpotent order. Its scope is finite packets; arbitrary discontinuous
degrees on the whole quotient are not claimed to be determined by these restrictions.
The finite-block algebra identities and classification remain to be formalized.

The Meyer invariant-majorant conjecture now has a dependency-closed paper proof:
`../3-formalized/flow-invariant-meyer-majorants-force-criticality.md`.
Two fixed sharp point sources read real and imaginary Mellin values. Their mixed
bounds control squared evaluation, and `Phi+1` gives the existing abstract invariant
gauge theorem its norm bound. This avoids any assumed quotient descent or norm law.
The converse uses ordinary trace under RH; centered trace invariance itself is an
exact reflected-Mellin cancellation, independent of RH. Exact Lean source landing
and the separate compact-source bridge remain pending.

`/tmp/QIIMeyerInvariantMajorantDraft.lean` now contains the complete actual-source
flow, two-point evaluation bound, invariant-majorant criticality theorem, exact
centered trace invariance, and converse proof attempts. Its additional API audit is
`/tmp/QIIMeyerFlowNames.lean`; neither has run. The quadratic cone scratch now
reuses the existing `HTGeometry.bilinForm_sq_le` instead of duplicating Cauchy–Schwarz.
`HTGeometry/NonnegFormRadical.olean` already exists and must not be rebuilt.

Rosati direct check failed: the newer `CurveDatum.frobPoly` shadows the scalar
evaluation polynomial, and the Rosati reserve owner was not imported. All uses
now explicitly name the scalar polynomial, the owner import is added (its olean
already exists), and mixed reindexing has explicit source coefficients. An owner
API scratch check is `/tmp/QIIRosatiOwnerNames.lean`; the corrected Rosati leaf
awaits retry. The serial audit now runs the independent radical and unit-mass leaves
before the remaining scratch checks. No Rosati axiom list was clean in the failed run.

`/tmp/QIIArithmeticMajorantConeGeometryDraft.lean` adds the exact aperture-majorant
bilinear form and its zero, addition, nonnegative scaling, convexity, pointedness,
and generation corollaries. It is unrun. The generic cone scratch and global
majorant draft now also state convexity explicitly.

Broader-corpus audit: `DeningerMeyerConvolutionQuotient.lean` already supplies the
actual descended convolution product, commutativity, and associativity. Reuse this
product for the finite-jet degree classification. `DeningerMeyerPaugamInsertedTrace.lean`
was read fully: bounded top-Hasse insertion recovers a nondegenerate alternating
pairing, but explicitly does not prove positivity or a geometric cup identification.
The positive-degree classification must distinguish that alternating inserted trace
from Hermitian sharp-square positivity. Recent off-line-multiplicity corpus results
are density bounds and alternatives; they do not prove all zeros simple or all
multiple zeros critical. No simplification of the simplicity obstruction follows.

The first radical/multiplicity check certified actual single-jet realization,
trace positivity iff RH, and the multiple-zero convolution-square witness, but
the full file failed on explicit zeroth-jet normalization, multiplicity unfolding,
a scalar/source coercion in the point reading, and rewriting a dependent Fin bound.
The fixes unfold only the named transform definitions, type the scalar source
explicitly, and let arithmetic use the multiplicity equality without dependent
rewriting. A serial retry starts with this corrected leaf and stops on first error.

A further dependency-closed positive survivor is recorded in
`../3-formalized/pole-blind-poisson-boundaries-have-positive-origin-degree.md`.
The actual cap `E²(fXi)-E(fXi)` has boundary transform `s(s-1)xi(s)`,
vanishing at both poles but nonzero at 2. Its sharp square is a genuine
positive-origin-degree boundary with zero pole values, hence a nonzero
pure-source principal cycle. This refutes every normalized correction using
only those two values, even nonlinear corrections. The actual new leaf
`PoleBlindPoissonBoundariesHavePositiveOriginDegree.lean` is written but unrun.
It imports the certified origin module; that missing olean may now be built
once when the serial compile slot is free.

`MeyerNumericalRadicalAndMultiplicity.lean` passed its corrected actual-file
check and all nine main axiom audits with only `propext`, `Classical.choice`,
and `Quot.sound`. The two remaining zeroth-jet coercions were resolved by
explicitly changing the statement to the raw Mellin transform, without
expanding the linear-map constructor. Temporary audits and one unused simp
argument were removed; the module is wired and documented. Its complete
proof card is `../3-formalized/meyer-numerical-radical-and-multiplicity.md`.
`MeyerSourceIntersectionSurface`, `FaithfulPositiveMeyerDegrees`, and
`ExponentialSourceMassControlsTheFullPrimeSum` are now actual unchecked
modules, with their old draft files removed. The surface imports the radical
module, so its missing olean may now be built once for that dependency.

The finite positive-degree classification is being split into reusable exact
algebra and its finite-jet application. `/tmp/QIIMeyerDegreeAlgebraDraft.lean`
constructs descended arithmetic sharp from the existing quotient conjugation
and Paugam involution, proves convolution compatibility by actual Mellin
injectivity, and derives complex null-pair annihilation for every positive
Hermitian linear degree. The corresponding API check is
`/tmp/QIIMeyerDegreeAlgebraNames.lean`; neither has run. The draft makes no
continuity assumption or claim about arbitrary infinite-packet degree recovery.

`FiniteReadingsAndMassCannotSupplyBezout.lean` passed its actual-file check
and all three main axiom audits with only standard axioms. Temporary audits
removed; umbrella and README wired. The exact unit-mass positive survivor
and restricted reserve no-go are recorded in
`../5-failed/finite-readings-and-exact-mass-source-reserves.md`. This does not
rule out arbitrary sets selected by mass: the theorem concerns fibre-threshold
source cones with every source available after a finite fibre lift.

The normalized finite algebra and positive restriction now have explicit
proof drafts: `/tmp/QIIMeyerFiniteJetAlgebraDraft.lean` constructs factorial
normalized Hasse source classes, exact cross-block zero products, same-block
truncated products, local identities, and sharp reflection with parity.
`/tmp/QIIMeyerPositiveFiniteJetDegreeDraft.lean` uses the complex null-pair
lemma to kill off-line blocks and descend through higher critical jets, then
proves the weighted-value formula for finite sums of these actual classes.
Still pending: direct checks, exact identification of the finite causal
section with this Hasse-class span, and the converse finite positive-weight
construction. These files remain drafts and are not cited as certified.

The surface API examples and sharp-root APIs passed. The global-majorant
API check stopped because the guessed bare `tsum_le_tsum` identifier does
not exist in this mathlib. Its actual prime-sum proof remains unchecked;
a corpus-first lookup is resolving the correct summable monotonicity lemma.
The next serial batch starts with the remaining point, cone, flow, Rosati,
and sharp-algebra checks, then the Rosati leaf and missing dependency builds
for the factor-two, pole-blind, and actual surface leaves. It stops on the
first failure; no existing olean is rebuilt.

The point-degree API check passed, including clean axioms for Hardy's
critical-point existence and exclusion of the central real point. The point
draft is now the actual unrun module `PositiveMeyerDegreesCanForgetClasses`,
with its old draft removed. The finite positive-degree draft now also includes
the converse finite nonnegative critical weighting on the whole actual
quotient and exact prescribed value weights.

A further paper theorem is
`../2-fully-proven/invariant-origin-mass-does-not-bound-the-weil-trace.md`.
The smooth version of the finite-kernel construction is drafted in
`/tmp/QIISmoothFiniteReadingKernelsDraft.lean`; the original bump can be chosen
C-infinity and finite sums preserve that regularity. This supplies actual
compact Meyer witnesses for unit-origin-mass unboundedness. The compact
origin identity and final trace obstruction remain to be written and checked.

`/tmp/QIIInvariantOriginMassDraft.lean` now contains positive origin square
mass, centered-flow invariance from literal product invariance, the exact
compact real mass identity, smooth unit-mass trace-unbounded witnesses at
every aperture, and failure of every nonlinear function of that mass as a
mixed-trace majorant. The extra API scratch is `/tmp/QIIOriginMassNames.lean`.
All are unrun. The strengthened finite-degree classification also now includes
the exact finite causal expansion and converse finite critical weight degree;
its remaining obligations are serial checks and audits.

The positive-quadratic-cone scratch passed its substantial arguments but
failed its zero-membership simplification: the remaining term was
`0 <= 2*0*0`, needing `mul_zero` rather than `zero_mul`. That targeted fix
and removal of an unused helper premise are in place. The next serial
batch starts with the corrected summable-order API check, then retries
the cone scratch and proceeds through the queued actual leaves. The
sharp-algebra, origin-mass API, and smooth-kernel scratch checks follow
those leaves if all preceding checks pass.

Removed the completed API/audit scratch files for the surface, sharp-root,
point-degree, aperture-majorant, origin-degree, earlier finite-Cauchy/source
checks, and earlier principal audit. Their passing results are recorded
above; actual source modules retain the implementations. Current queued
checks and every unverified proof draft are preserved.

Further corpus audit: `GaussHodgeWeilKreinDecomposition.lean` was read fully.
It already gives the abstract square-summable value-space signature split;
`XiWeilLineConjHilbert.norm_xiWeilPolarization_le` already gives its mixed
Cauchy bound. Do not duplicate either result. A proposed actual-source
Rosati mass and exact exponential flow-growth classification remain only
a frontier investigation; square-summability of the centered Meyer transform
and quantitative transport must be linked before claiming a new theorem.

The full source Hilbert convolution jets, faithfulness, and actual boundary
sharp-root obstruction expose another dependency-closed paper result:
`../3-formalized/arithmetic-sharp-is-the-hilbert-adjoint-exactly-for-simple-critical-zeros.md`.
Adjoint identification forces sharp-square-root closure by the Hilbert Gram
norm identity; conversely RH and simplicity make every actual block scalar
and sharp conjugates its multiplier. No Lean draft yet. This sharpens the
existing source warning that arithmetic sharp is not automatically Hilbert
adjoint, and separates operator positivity from ordinary trace positivity.

The corrected summation API is `Summable.tsum_le_tsum`, used as
`hf.tsum_le_tsum hterm hg`. Its dedicated scratch example passed; the
actual global prime-mass leaf now uses that verified form. All other
APIs in its earlier scratch check had already passed.

The positive quadratic source-cone scratch passed. It is now the actual module
`PositiveQuadraticSourceCones.lean`, with five temporary axiom audits; its
actual-file final check is pending. The old scratch was removed. The active
serial batch has advanced to the flow API check.

The centered-flow APIs passed, including the exact exponential conjugation
orientation and clean invariant-evaluation-gauge axioms. The implementation
is now `FlowInvariantMeyerMajorantsForceCriticality.lean`; its old draft was
removed. The actual-file check awaits the actual surface dependency.

Corpus search located the existing centered source flow in
`DeningerMeyerHalfDensityL1Completion`. The new trace-majorant leaf now uses
that exact existing map instead of defining a duplicate. The origin-mass
draft uses the same map. Its half-density L2 embedding is already supplied
by `FrankensteinMeyerHalfDensityL2KoszulDescent`; the boundary-density
conjecture is tracked separately in `poisson-boundaries-are-dense-in-origin-mass.md`.

The adjoint classification has a complete unrun proof draft in
`/tmp/QIIMeyerSharpAdjointDraft.lean`, including the exact equivalence with
existence of an arbitrary faithful positive linear quotient degree.

The global majorant and aperture cone-geometry drafts are now actual unrun
leaves `GlobalArithmeticMajorantsSupplyBezout.lean` and
`ArithmeticMajorantConeGeometry.lean`, with temporary axiom audits. Their
old drafts were removed. The Rosati-owner API check passed; the active batch
is now checking the actual Rosati leaf. Completed sum-order, flow, and
Rosati-owner API scratch files were removed after recording their results.

`RosatiSectionsHaveBezoutWithoutUnitarity.lean` passed its actual-file final
check and all six main axiom audits, each using only propext, Classical.choice,
and Quot.sound. Temporary prints removed; AOT umbrella and README wired;
Q-II review updated. Its exact positive survivor and paper proof are recorded
in `../3-formalized/rosati-sections-have-bezout-without-unitarity.md`.
The active batch has advanced to the missing aperture-majorant olean required
by the actual factor-two theorem.

The origin-mass boundary-density candidate now has a dependency-closed paper
proof and has moved to `../2-fully-proven/poisson-boundaries-are-dense-in-origin-mass.md`.
Its actual Xi-cap Fourier profile is nonzero almost everywhere; exact centered
flow supplies a dense orbit of genuine boundaries. Every genuine class has
representatives with arbitrarily small origin square mass, and every continuous
linear L2 boundary-annihilating reporter is zero. The general cyclicity and
actual boundary-density proofs are drafted in `/tmp/QIIL2TranslationCyclicityDraft.lean`
and `/tmp/QIIPoissonBoundaryDensityDraft.lean`; APIs are in
`/tmp/QIIBoundaryDensityNames.lean`. All three remain unchecked.

The aperture-majorant dependency olean was built successfully for the actual
factor-two importer. That importer failed only on its hand-expanded bilinear
fibre expression (wrong expansion order) and two redundant `dsimp` calls.
The expansion is now normalized by the direct defect-map evaluation identity;
the two no-progress calls are removed. Remaining queued leaves did not run.

The finite-degree audit exposed a qualification worth making exact: positivity
of only the real sharp-square degree does not force the original complex
degree to be Hermitian. The canonical Hermitian part has exactly the same
real square readings, so the finite critical-value classification applies
to that part. The complete paper proof is recorded in
`../2-fully-proven/real-positive-meyer-degrees-are-controlled-by-their-hermitian-part.md`.
No infinite-packet classification or automatic continuity is claimed.

Boundary density gives a stronger exact graph theorem, recorded in
`../2-fully-proven/every-finite-meyer-jet-graph-is-dense-in-origin-hilbert-space.md`.
Every surjective normed cohomological reading has full product graph closure
with the origin Hilbert coordinate. In particular all actual finite Xi-jet
packets become maximally multivalued, even critical value coordinates. This
applies the existing finite-packet surjection and distinguishes the actual
L1 critical graph law from L2 collapse. Lean draft pending.

The factor-two core passed its corrected actual-file check and all five
transitive axiom audits with standard axioms only. The two scalar-coefficient
corollaries explicitly stated on its paper card have now been added to the
same leaf; they require a final check before the whole card is promoted.
The active serial batch has advanced to the actual positive-quadratic-cone
leaf. No factor-two olean was built.

Complete unrun drafts now include the canonical degree decomposition and
its finite restriction (`/tmp/QIIMeyerHermitianDegreePartDraft.lean`) and the
full product graph closure of every finite jet packet
(`/tmp/QIIMeyerOriginJetGraphDraft.lean`). The latter also proves that its
closed graph is single-valued exactly when the packet is empty.

`PositiveQuadraticSourceCones.lean` passed its actual-file final check and
all five standard-axiom audits. Temporary prints removed; ACS umbrella and
README wired. Its complete certificate is
`../3-formalized/positive-quadratic-source-cones-are-convex-and-generating.md`.
The active serial batch has advanced to the actual full prime-sum leaf.

The full prime-sum actual check failed only at the compact-support multiplication
elaboration. An explicit intermediate function fixes its inferred pointwise
product; the corrected file heads the active serial queue (session 62192).
The preceding queue stopped there, so the later pole-blind, surface, and API
checks have not yet run. Factor-two scalar corollaries are now second in queue.

A further dependency-closed paper survivor is recorded in
`../3-formalized/hilbert-schmidt-reserves-measure-the-arithmetic-adjoint-defect.md`.
The actual full-Hasse convolution resolvent factorization proves unconditional
Hilbert–Schmidt admission. The average source/sharp HS squared norm descends
faithfully to genuine cohomology, gives Bézout and ampleness, and exceeds the
ordinary source form by exactly half the squared adjoint defect. RR is therefore
equivalent to simple critical zeros. A generic operator proof is drafted in
`/tmp/QIIHilbertSchmidtDefectDraft.lean`; no check has run. Corpus audit found the
existing `HilbertSchmidtRankOne.hsNormSq_add` and reuses it, and identified the
special diagonal-kernel predecessor in `XiThermalQuadraticReflectionDefectSpectrum`.
No infinite Hasse-coordinate norm expansion is claimed.

`ExponentialSourceMassControlsTheFullPrimeSum.lean` passed its corrected
actual-file check and both endpoint axiom audits with standard axioms only.
Temporary prints removed; ACS umbrella and README wired; standalone certificate
`../3-formalized/exponential-source-mass-controls-the-full-prime-sum.md` added.
The obsolete global-majorant API scratch was removed. The active serial queue
has advanced to the actual factor-two leaf with its scalar corollaries.

The faithful Hilbert–Schmidt reserve now has a complete unrun source draft,
`/tmp/QIIMeyerHilbertSchmidtReserveDraft.lean`: actual admission from the
resolvent factorization; a real bilinear reserve; exact plus/minus adjoint
squares; genuine-class descent and faithfulness; mixed Bézout and ampleness;
ample-zero iff principal; convexity, generation, and pointedness modulo
principal cycles; RR iff actual adjoint compatibility and hence simple
critical Xi zeros. Its planned imports are `ArithmeticSharpAndTheHilbertAdjoint`
(from the existing adjoint draft) and HT `HilbertSchmidtTraceDefect` (from the
new generic draft). Neither is yet an actual module or verified result.

`BezoutCostsTwiceTheNegativeReserve.lean` passed its final actual-file check,
including both scalar-coefficient corollaries. All seven transitive axiom audits
use only propext, Classical.choice, and Quot.sound. Temporary prints removed;
card moved to `../3-formalized/bezout-costs-twice-the-negative-reserve.md`; ACS
umbrella and README wired. The active serial queue is building the previously
missing origin-degree dependency olean for the actual pole-blind importer.

The origin graph theorem now also covers the entire faithful convolution
operator range, endowed with its inherited operator norm. Its range restriction
is surjective, so the same boundary-density argument makes the full graph dense
in the product. Every nonprincipal source supplies a nonzero vertical operator.
Paper proof and `/tmp/QIIMeyerOriginJetGraphDraft.lean` updated; range APIs added
to the queued boundary API check. This is still unverified Lean draft work.

The origin-degree dependency olean was built successfully (previously absent),
and the active serial batch is now checking
`PoleBlindPoissonBoundariesHavePositiveOriginDegree.lean`. Before that check,
the cap Mellin calculation was normalized with targeted `simp only` so all
negative-Euler occurrences are rewritten. No other origin olean rebuild is allowed.

A new bounded-flow candidate is recorded in
`bounded-meyer-flow-orbits-live-in-critical-top-jets.md`. Corpus search found
exact centered full-jet packet transport, the generic `opNorm_le_hsNorm`, and
the fixed Xi-avoiding source eigenfunctional criterion. The candidate selects
critical highest jets, not the reduced critical values seen by positive linear
degrees. Its necessity can use induction on jet order and a bounded affine
function argument, avoiding a general exponential-polynomial asymptotic input.

The bounded full-Hasse orbit candidate has a complete paper proof and moved to
`../3-formalized/bounded-meyer-flow-orbits-live-in-critical-top-jets.md`.
The exact jet flow formula and first-column recovery close the argument:
induction kills every off-line jet; bounded affine first-order shear kills
all but the highest critical jet; rowwise unit phases give the converse HS
isometry with no infinite-sum interchange. The paper also classifies products
and the trace radical on this carrier, proves unconditional nontriviality via
Hardy's critical point, and shows that the existing single Xi-avoiding compact
source has bounded full-HS orbit iff RH and simplicity. No Lean draft yet.

The first pole-blind actual check failed only at two `rw [q]` calls on a local
let value. Both now use the explicit convolution expression before rewriting.
Its Mellin identity audited with standard axioms; the dependent endpoints await
the corrected check. The previous serial batch stopped, so its surface and API
checks never ran. New owned serial batch is session 50477 and records each
completed file's exit code in `/tmp/qii-verify-current.tsv`; independent checks
continue after failures. Queue: pole-blind actual; missing Q olean then surface
actual; consolidated `/tmp/QIICohomologyAndHilbertAPIs.lean`; smooth-kernel draft;
L2 cyclicity draft; generic HS trace-defect draft. No parallel owned Lean process.

Four API scratches were consolidated into one narrow import/check file; originals
remain until the combined check passes, then can be removed. The combined file
also checks the exact full-jet flow, Hilbert–Schmidt, and finite-sum APIs needed
by the new source draft. `/tmp/QIIMeyerHilbertSchmidtSourceDraft.lean` now isolates
actual HS admission, first-column factorial jet bounds, centered raw jet transport,
and the character/affine forms after lower coefficients vanish. The faithful
reserve draft imports this planned base module instead of duplicating admission.
This new source draft is not yet queued or checked.

`PoleBlindPoissonBoundariesHavePositiveOriginDegree.lean` passed the corrected
actual-file check. All five transitive axiom audits use only propext,
Classical.choice, and Quot.sound. Temporary prints removed; card moved to
stage 3; ACS umbrella and README wired. The active queue has advanced to the
previously missing numerical-radical dependency olean for the actual surface.

`/tmp/QIIMeyerBoundedCenteredOrbitsDraft.lean` now contains a complete unrun
proof of the four-way bounded-jet/critical-top/HS-bounded/HS-isometric law and
the fixed Xi-avoiding source and global simple-critical criteria. It imports
the planned source HS base. Product, trace-radical, and nontriviality corollaries
from the paper still need their exact Lean endpoints; the draft is not queued.

The numerical-radical olean attempt failed: its vertical fibre simplification
had lost `zero_add`, while the horizontal fibre simplification retained that
unused rewrite. The rewrite is now correctly placed. No Q olean was produced;
the surface check was therefore skipped. The previously certified Q source
requires a fresh actual-file check of this corrected text before the missing
olean attempt is retried. The active batch continues with consolidated APIs
and independent drafts. This is a local proof-rewrite repair, not a new premise.

The consolidated cohomology/Hilbert API audit passed, including range restriction,
full raw jet flow, first-column recovery, HS operator norm, and exact lp norm APIs.
Its three dependency axiom audits use only standard kernel axioms. Five superseded
API files and completed search outputs were removed. The existing off-line
multiple-zero census gives bounds, not exclusion; no stronger premise is imported.
The HS source base and sharp convolution algebra now have actual candidate files
with endpoint axiom audits, still unchecked and unwired. The corrected numerical
radical file has its nine endpoint audits restored for the required fresh check.

The smooth finite-reading draft reached a smoothness-index coercion error at
`(hvd i).of_le le_top`: the target is `2 ≤ (⊤ : ℕ∞)` coerced into `WithTop ℕ∞`.
Its next check must use an explicit cast of the inner order comparison. No mathematical
premise changes. The bounded-orbit algebra and trace-radical corollaries have an
unrun draft `/tmp/QIIMeyerCriticalTopAlgebraDraft.lean`; no new result is certified.

Serial session 50477 finished: generic HS trace-defect draft passed; smooth-kernel
draft failed only the explicit smoothness-order cast; L2 cyclicity failed three
zero-function coercions. Both local repairs are in actual candidate files with
endpoint audits. The generic HS leaf now also has an actual candidate file,
awaiting its required actual-file audit. No failed or scratch-only result is wired.

Current owned serial audit is session 15986, logged in `/tmp/qii-verify-next.tsv`.
Queue: corrected Q actual then missing Q olean and actual surface; actual HS source
base; actual sharp convolution algebra; corrected smooth-kernel actual; actual
HS trace defect; corrected L2 cyclicity actual; missing prime and quadratic oleans
for the actual global majorant and cone-geometry importers, then those actual files.
Missing-olean checks preserve existing files. There is one owned Lean process.

Boundary-density paper and draft now also classify all continuous nonlinear
cohomological readings into a Hausdorff target: they are constant. The linear
reporter result accordingly has a general Hausdorff topological-vector target.
No completion or positive Hodge interface is assumed.

The corrected actual numerical-radical file passed session 15986. All nine
endpoint axiom audits again contain only propext, Classical.choice, and Quot.sound.
The stage-3 repair note is resolved. Its missing olean build is now active for
the surface importer; temporary axiom prints remain until that build finishes.

The existing faithful compact-open comparison was located in
`DeningerMeyerXiSpectralInclusion` and its injection in `DeningerMeyerGlobalXiSynthesis`.
Boundary density now has an unrun companion draft excluding continuous recovery
of this comparison or of the full faithful convolution operator from origin L2,
even by nonlinear maps: `/tmp/QIIOriginHilbertCohomologyObstructionDraft.lean`.
The full-HS reserve flow corollaries are drafted in
`/tmp/QIIMeyerHilbertReserveFlowRigidityDraft.lean`: local boundedness equals local
invariance equals critical highest jets; global invariance equals the reserve
cone RR criterion. All remain paper proofs and unverified drafts.

The corrected numerical-radical olean build also passed and the missing artifact
now exists. Never rebuild it. Temporary axiom prints were removed; the actual
source intersection surface is now checking in session 15986.

The bounded-source restricted surface has a dependency-closed paper proof and
complete unrun draft `/tmp/QIIBoundedMeyerSourceSurfaceDraft.lean`. Its card moved
to `../2-fully-proven/bounded-meyer-source-surface-has-riemann-roch-and-bezout.md`.
It proves actual restricted RR/Bézout/ampleness; numerical/principal equality
and pointedness exactly under critical simplicity; full-carrier coverage
exactly under RH plus simplicity; cofinal source witnesses of trace one from
the existing unconditional simple-critical census. Existing restriction APIs
are reused. The focused API file `/tmp/QIIRestrictedSurfaceAPIs.lean` is unrun
and not in current serial queue. This is a restricted theorem, not full Q-II.

The actual source-surface audit failed only in `trace_sub_left`: simplification
did not normalize the restricted real `(-1)` action on the complex source.
It now uses the explicit equality `neg_one_smul ℝ g` before rewriting. Eight
printed endpoints had standard axioms; the negative packet endpoint inherited
the failed proof, so the entire file remains unverified and unwired pending
a corrected actual check. No surface olean was produced. The serial batch has
advanced to the actual HS source base.

The next infinite-degree question is now explicit in
`positive-meyer-degrees-and-the-infinite-source-tail.md`: finite packet
classification does not justify passing an arbitrary degree through an
infinite expansion. A complete paper finite-to-global energy decomposition
is recorded in `../2-fully-proven/finite-critical-projectors-split-positive-meyer-energy.md`.
Actual critical causal projectors split every positive degree square into
its finite weighted-value energy and a nonnegative residual. The residual
vanishing/automatic-continuity question remains open; no analytic input is
assumed. The projector product and orthogonality Lean endpoints are not drafted.

`MeyerHilbertSchmidtSource.lean` passed its actual-file check, with four
standard-axiom endpoint audits. Temporary prints and one certified unreachable
`ring` were removed; ACS umbrella/README wired; the stage-3 foundation card is
`meyer-hilbert-schmidt-admission-and-triangular-flow.md`. Its stale /tmp source
copy was removed. `MeyerBoundedCenteredOrbits.lean` is now an actual unverified
importer with six endpoint audits; this authorizes the missing HS-source olean
when that dependent audit is queued. It is not in the active 15986 queue.

The finite critical energy decomposition now has a complete unrun draft:
`/tmp/QIIFiniteCriticalProjectorEnergyDraft.lean`. It contains exact causal block
selection, central multiplication, sharp compatibility, genuine zero mixed
products, degree decomposition/saturation, and the finite weighted energy
formula and bound. The formula uses the existing full-jet slot type and keeps
only order zero, equivalent to one term per selected critical point. The
infinite-tail question remains active with no continuity or zero-tail premise.

`MeyerSharpConvolutionAlgebra.lean` passed actual-file verification and all
four endpoint axiom audits use only standard kernel axioms. Prints removed;
ACS umbrella/README wired; stage-3 card `arithmetic-sharp-and-positive-degree-radicals.md`
added; obsolete /tmp algebra source removed. `MeyerFiniteJetAlgebra.lean` is
now an actual unverified importer with seven endpoint audits. Its future check
requires the missing sharp-algebra and faithful-positive-degree oleans; the
latter must first pass after the corrected surface. This file is not in the
active 15986 queue, which now checks the corrected smooth-kernel actual file.

The smooth-source actual check still failed on the WithTop smoothness cast and
pointwise finite-sum elaboration. A narrow API scratch now isolates both fixes;
that file must pass before transferring the verified expressions. Generic
`HTGeometry/HilbertSchmidtTraceDefect.lean` and
`HTGeometry/L2TranslationCyclicity.lean` both passed actual-file checks and all
standard-axiom audits. Prints removed, HT umbrella wired, standalone stage-3
cards added. Their obsolete scratch copies were removed. The actual candidate
`PoissonBoundariesAreDenseInOriginMass.lean` now imports the certified cyclicity
leaf, with six endpoint audits; its missing dependency olean is authorized.
It remains unchecked and unwired. The global-majorant queue 15986 continues.

Session 15986 closed: the majorant cone geometry failed only a no-progress
simplification on the negative source degrees. Its other printed endpoints
were standard-axiom proofs. That call and an unused zero-map rewrite were
removed. The global majorant now reduces its pole-moment map by reflexivity
and normalizes the realTests zero coercion explicitly. Both corrected actual
files are queued in active session 51780. The new algebraic character proof
uses a public point-degree product lemma now placed in the pending point-degree
leaf, avoiding duplicate declarations.

The first check in 51780 verified `ENat.natCast_le_of_coe_top_le_withTop` but
found that finite function sums need a pointwise function-extensional equality
before `ContDiff.sum`. That explicit equality is now in the API scratch and
both smooth-source copies. Their next check remains pending; the active script
has advanced to the restricted-surface and original-inverse API audit.

The arbitrary finite-packet positive energy decomposition is now fully drafted
in `/tmp/QIIFiniteCriticalProjectorEnergyDraft.lean`: exact critical-value
weights, zero mixed degree, energy splitting, bound and saturation without
requiring all selected points critical. The original class-level zero-product
statement remains specific to reflection-stable/critical packets.

A new complete paper survivor is
`../2-fully-proven/faithful-reserves-on-the-bounded-meyer-surface.md`: on the
bounded carrier, faithful-reserve RR and equality with the ordinary degree
cone are exactly critical simplicity, while reserve-flow invariance always
holds there. No multiple critical zero is claimed to exist. It prevents
transferring a full-carrier equivalence to a restricted carrier without its
domain condition. This new leaf has no Lean draft yet.
