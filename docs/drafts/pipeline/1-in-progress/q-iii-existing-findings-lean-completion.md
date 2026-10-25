# Q-III existing findings: Lean completion

- **Stage:** 1-in-progress
- **Type:** FORMALIZATION AUDIT
- **Parent:** [Q-III](q-iii-escape-state-classification.md)
- **Scope:** Finish every existing paper finding before new research.
- **User stopping condition:** Finish started Lean work and every outstanding
  paper proof, then pause. Do not resume the open classification research.
- **Latest user instruction:** No Python helpers. Edit Lean files directly and
  invoke each Lean command directly. All owned `/tmp/qiii*.py` helpers were
  removed; their references below are historical and must not be followed.

Every compile is a direct `lake --old env lean ...` invocation from `formal/`,
one process at a time. No compilation scripts, umbrella builds or increased
Lean limits. Source promotion requires a successful check and transitive axiom
audit; final canonical checks remain necessary after changing import boundaries.
Accepted axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.

## Completed foundations

- All fourteen original cofactor-module, signed/antipodal, origin-trace,
  capped-pronic-cost and separability canonical checks passed in the recorded
  original-core audit. Do not repeat unchanged checks.
- Uniform small-budget, recentered energy-scale disappearance, signed Gram,
  source-power translation, continuum index and operator-hull refinements
  passed canonical checks.
- Complete source dilation, coefficient evaluation, admitted uniqueness,
  abstract Wiener-unit transport and admitted faithfulness passed final checks.
- Countable common covariance extraction passed its final check.
- Exact complete dilation blocks, energy crossings, actual diagonal energy
  ratios, multiplicative power classification, actual rank-one magnitudes and
  prime-deleted white-noise exclusion passed canonical checks.

## Open completion batches

| Finding | Current gate |
|---|---|
| Zero cofactor forces dimension at most p-1 | Final canonical source check passed; positive survivor and exclusion card moved to `3-formalized` |
| Augmentation countermodel and singleton character hull | Canonical source-only audit `79225` passed with standard axioms; countermodel complete |
| Actual unit transport, Möbius/Liouville equivalence | All canonical source-only checks passed with standard axioms; card moved to `3-formalized` |
| Finite joint spectral multiplicities and normalized Bohr representatives | All three canonical source-only checks passed with standard axioms; card moved to `3-formalized` |
| Rank-one multiplicative signs | Canonical audit `87736` passed with standard axioms; card in `3-formalized`, augmentation route retired with its checked positive survivors |
| Visible interior pole orders, paid jets, critical boundary values, unit orbits | All six canonical sources passed final audits with standard axioms; both paper cards moved to `3-formalized` |
| Reset moving origin, faithful step kernel and every positive boundary mass | Prescribed-horizon extraction and exact step Gram complete; eleven canonical leaves remain |
| Raw moving origin, exclusion from actual zero-origin limits | Draft scratch after boundary dependencies |
| Positive boundary modules have infinite dimension and continuum index | Draft scratch after boundary dependencies |
| Exact incomplete dilation fibre and mixed C*D/p bound | Draft scratch; required by contraction bundle |
| Actual horizon contraction, principal ideal quotient, full intertwining | Draft scratch after cutoff dependency |
| Closed dilation range, index loss, matrix/operator horizon order | Draft scratch in contraction bundle |
| Rank-one contraction fixes state | Draft scratch in contraction bundle |
| Arbitrary commuting family has a common eigenvector | Final canonical audit `15948` passed with standard axioms; required olean exists |
| Finite actual hull magnitudes and half-plane approximation | Draft scratch after operator order and generic eigenvector theorem |
| Tied-torus and augmentation character limits | Draft scratch; refactor existing owner after verification |
| Conjugation of actual source pairings, annihilator and hull | Final canonical audit `78866` passed with standard axioms; card moved to `3-formalized` |
| Interior Wiener jets, mixed interpolation and paid quotient lower bounds | Base scratch, then full application and canonical checks |
| Vanishing Gram steps, intermediate kernels, singleton/continuum alternative | Final canonical audit `79971` passed with standard axioms; card moved to `3-formalized` |

The square-root translation card contains completed origin-trace results plus
later raw/reset-boundary consequences; close it only after the latter are
checked. The visible-poles card retains its genuinely open identification of
actual module spectra with arithmetic zeros, separate from the paid-ideal
theorems being completed here. No complete actual escape classification is
claimed.

## Completed canonical audits

Every audit below exited successfully with only standard axioms. Do not repeat
unchanged checks. All required leaves are wired into their programme umbrellas.

| Batch | Final source-only sessions | Required oleans |
|---|---|---|
| Zero-cofactor finite cutoff | `34006` | `25746` passed |
| Joint characters, normalized Bohr characters, actual finite index | `27212`, `68534`, `49590` | `76210`, `35229`, `76428` passed |
| Paid corrections, real unit convolutions, Möbius–Liouville transport | `78335`, `56886`, `94844` | Existing required oleans passed |
| Augmentation countermodel, singleton hull, scalar Gram | `79225` | None needed |
| Rank-one multiplicative signs | `87736` | None needed |
| Arbitrary commuting-family common eigenvector | `15948` | `19547` passed |
| Vanishing-step intermediate cluster values | `21506` | `98674` passed |
| Actual normalized Gram steps | `86889` | `82801` passed |
| Common limits along prescribed increasing/cofinal horizons | `11914` | `34513` passed |
| Actual kernel interpolation and singleton/continuum alternative | `79971` | None needed |
| Explicit Mellin identity and translated-zero obstruction | `11733` | `23314` passed |
| Visible translated zero orders and paid interior jets | `55727` | `36737` passed |
| Paid complex Mellin bound and critical boundary rate | `3754` | `83196` passed |
| Generic analytic boundary-order cancellation | `38501` | `14888` passed |
| Actual critical-boundary paid-kernel obstruction | `46157` | `3574` passed |
| Visible constraints on Wiener unit orbits and Liouville | `9109` | `25737` passed |
| Actual source-pairing and module conjugation | `78866` | None needed |
| Exact max kernel of origin steps | `34661` | `12398` passed |

Recent final output files:
`/tmp/qiii-augmentation-canonical-final.log`,
`/tmp/qiii-rank-one-sign-canonical-final.log`,
`/tmp/qiii-common-family-canonical-final.log`,
`/tmp/qiii-intermediate-cluster-values-canonical-final.log`,
`/tmp/qiii-cofactor-gram-steps-canonical-final.log`,
`/tmp/qiii-common-horizons-canonical-final.log`,
`/tmp/qiii-actual-kernel-family-canonical-final.log`.

The rank-one card is in `3-formalized`; the augmentation no-go is in `5-failed`
with cutoff and full signed-power survivors checked. README and the Q-III
correction in `opus.md` now record those completed results, actual unit
transport and exact finite joint multiplicities.

## Active direct check

Prescribed-horizon final source-only audit `11914` passed with standard axioms
for both statements. Its canonical split now explicitly imports
`TheCofactorLimitCarriesACyclicDilationAction`. Source review found the same missing actual-limit dependency in
`PositiveOriginMixturesAreFaithful`; it now has the same explicit import.
`TheOriginStepModuleHasTheFullBohrHull` now explicitly imports
`HTGeometry/RealPositiveKernelComplexification` for its real-to-complex
positivity and packet comparison lemmas. These later leaves remain unchecked.
The positive-mixture module comment now says comparison **to** the step
module; its construction does not assert surjectivity, which faithfulness
does not need.
The complete pole batch passed final canonical checks; both paper cards are
in `3-formalized`. Its only split failure was the generic cancellation leaf's
missing complex-number import; adding `Mathlib.Analysis.Complex.Basic` fixed
it. The explicit Mellin owner was refactored through its new helper. The
unit-orbit leaf explicitly audits both Möbius nonpayment corollaries.
The completed combined boundary-pole scratch was removed; its canonical
sources and final logs remain.

Final pole logs: `/tmp/qiii-explicit-mellin-owner-canonical-final.log`,
`/tmp/qiii-visible-orders-canonical-final.log`,
`/tmp/qiii-paid-mellin-boundary-canonical-final.log`,
`/tmp/qiii-boundary-order-cancellation-canonical-final.log`,
`/tmp/qiii-critical-boundary-obstruction-canonical-final.log`,
`/tmp/qiii-visible-pole-unit-orbits-canonical-final.log`.

Conjugation scratch retry `19444` and final canonical audit `78866` passed
with standard axioms. `ActualCofactorHullsRespectConjugation` is installed
and umbrella-wired; its card moved to `3-formalized`. Final output:
`/tmp/qiii-actual-conjugate-hull-canonical-final.log`. No olean was needed.
Its redundant scratch check file was removed.

Boundary entry 2, `ArithmeticDefectRigidity/OriginStepsHaveTheMaxKernel`, passed
required olean `12398` and final source-only check `34661` with standard axioms.
Final output: `/tmp/qiii-origin-step-kernel-canonical-final.log`.
Boundary entry 3, `EscapeRecordsControlMovingOriginMass`, is under its required
olean check; output `/tmp/qiii-origin-records-olean.log`. No other owned Lean
process is active.
The eight remaining standalone/combined scratch sources listed below were
scanned for forbidden placeholders and raised limits: no matches. They still
require Lean checks; the syntax scan is not a proof audit. The eleven required
boundary oleans were confirmed absent; existing dependencies must not be
rebuilt. The completed common-horizon leaf is the first entry in
`/tmp/qiii-boundary-canonical-modules.txt`; entries 1–2 are complete and only
entries 3–13 remain.

## Direct source work remaining

All Python source assemblers and promoters were deleted at the user's request.
Read and edit Lean sources directly; copy a checked source into its mathematical
owner, add its umbrella import directly, and run the canonical check directly.

- `/tmp/qiii-contracted-horizons-check.lean` contains the current exact remainder,
  mixed bound and full operator intertwining drafts. It also explicitly states
  `scaled_diagonal_mem_Icc`, the previously recorded interval bound for the
  contracted-energy profile. Use this current scratch when splitting canonical
  leaves; the older part files do not include this last corollary.
- Rank-one sign, augmentation, common-family, crossing and Gram-step scratches
  have all been installed, wired and canonically checked. Their six completed
  scratch check files, including the actual kernel-family application, were
  removed; canonical sources and audit logs remain.
- `/tmp/qiii-finite-hull-moduli-check.lean` now directly combines the existing
  eigencharacter-power, finite-hull-modulus and half-plane-sequence bodies.
  It is unchecked and needs numeric-operator-order and tied-torus dependencies;
  the common-family dependency is complete. Its restricted commutation proof
  now omits the same redundant subtype-extensionality step repaired in the
  generic common-family theorem.
- `/tmp/qiii-visible-mixed-jet-index-check.lean` retains point separation,
  masked finite jets, interior rank bounds, mixed interior/boundary
  interpolation and rank bounds, and the unit-orbit/Liouville corollaries.
  It now imports the intended `InteriorWienerJets` owner rather than duplicating
  its body, and explicitly imports `AnIndexFormulaForTheActualReceiver`.
  Its Wiener character names, and the corresponding base-jet and part files,
  are explicitly qualified following the augmentation collision.
  It remains unchecked pending the base-jet dependency; pole dependencies
  and their final canonical audits are complete.
- The corresponding in-progress cards include
  `matrix-horizon-order-constrains-actual-cofactor-actions.md` and
  `visible-pole-jets-bound-the-paid-quotient-index.md`. Reconcile their exact
  statements and move them only after the relevant canonical audits pass.
- Raw-origin and boundary-index scratch files remain unchecked. Their exact
  source statements and canonical dependencies are retained in their Lean files.
- The actual kernel-family canonical application is complete, together with
  all three dependencies; its redundant scratch check was removed.
