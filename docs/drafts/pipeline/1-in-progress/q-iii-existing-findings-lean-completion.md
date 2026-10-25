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
| Visible interior pole orders, paid jets, critical boundary values, unit orbits | Canonical checks after successful combined scratch |
| Reset moving origin, faithful step kernel and every positive boundary mass | Prescribed-horizon extraction complete; twelve other canonical leaves still need their direct checks |
| Raw moving origin, exclusion from actual zero-origin limits | Draft scratch after boundary dependencies |
| Positive boundary modules have infinite dimension and continuum index | Draft scratch after boundary dependencies |
| Exact incomplete dilation fibre and mixed C*D/p bound | Draft scratch; required by contraction bundle |
| Actual horizon contraction, principal ideal quotient, full intertwining | Draft scratch after cutoff dependency |
| Closed dilation range, index loss, matrix/operator horizon order | Draft scratch in contraction bundle |
| Rank-one contraction fixes state | Draft scratch in contraction bundle |
| Arbitrary commuting family has a common eigenvector | Final canonical audit `15948` passed with standard axioms; required olean exists |
| Finite actual hull magnitudes and half-plane approximation | Draft scratch after operator order and generic eigenvector theorem |
| Tied-torus and augmentation character limits | Draft scratch; refactor existing owner after verification |
| Conjugation of actual source pairings, annihilator and hull | Draft scratch, then canonical placement/check |
| Interior Wiener jets, mixed interpolation and paid quotient lower bounds | Base scratch, then full application and canonical checks |
| Vanishing Gram steps, intermediate kernels, singleton/continuum alternative | All three dependencies complete; full application scratch `6026` passed, canonical leaf installed/wired, final source audit running |

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

Recent final output files:
`/tmp/qiii-augmentation-canonical-final.log`,
`/tmp/qiii-rank-one-sign-canonical-final.log`,
`/tmp/qiii-common-family-canonical-final.log`,
`/tmp/qiii-intermediate-cluster-values-canonical-final.log`,
`/tmp/qiii-cofactor-gram-steps-canonical-final.log`,
`/tmp/qiii-common-horizons-canonical-final.log`.

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
Application scratch `6819` passed the countable-table cardinal bound and
nonuniqueness-implies-escape with standard axioms. Its interpolation proof
failed because simplification left a function composition unexpanded under
`Tendsto`. That equality is now proved pointwise with `Tendsto.congr`.
Direct retry `6026` passed all five targets with standard axioms, output
`/tmp/qiii-actual-kernel-interpolation-retry.log`. The checked source is installed
as `ArithmeticDefectRigidity/ActualCofactorKernelFamiliesAreSingletonOrContinuum`
and wired into its umbrella. Exactly one final source-only audit is active from
`formal/`, output `/tmp/qiii-actual-kernel-family-canonical-final.log`.
No olean is needed because no written leaf imports this application.

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
  have all been installed, wired and canonically checked.
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
  It remains unchecked until the base jet and pole dependencies are complete.
- Raw-origin and boundary-index scratch files remain unchecked. Their exact
  source statements and canonical dependencies are retained in their Lean files.
- `/tmp/qiii-actual-kernel-interpolation-check.lean` now directly combines the
  intermediate-coordinate and singleton/continuum drafts. It is unchecked
  and has passed. Its canonical application is in final source-only audit;
  all three dependency oleans and final source audits are complete.
