# Arithmetic defect rigidity: source constraints on escaping critical energy

Status: completion of existing proofs and individual audits in progress.

## Objective

Develop the programme specified by §6 of `docs/reports/review-2410/astra.md`: construct quantitative tools retaining signed covariance, cofactor and successor data, moving forcing and source budgets; prove substantive unconditional arithmetic results; organize them under `GaloisForLFunctions.ArithmeticDefectRigidity` with a foundational README.

The full objective includes the exclusion problem for actual arithmetic defects. A normalized-profile framework alone does not complete it.

## Existing inputs

- Exact normalized Möbius receiver, energy ratios and cofactor inversion: `ArithmeticCompensationTheory.TheNormalizedReceiverBlowUpProfile`.
- Horizon escape at the source growth scale: `ArithmeticCompensationTheory.TheReceiverEnergyEscapesToTheHorizon`.
- Critical-energy, compensation, repairing-ideal and shared-budget programmes identified in the report.

## Research obligations

1. Preserve signed pairings and forcing on moving energy supports.
2. Obtain selective quantitative arithmetic relations and mixed covariance control.
3. Define and price source operations on repairing obstructions.
4. Control absolute horizon costs and global shared allocation.
5. Develop multiplicity-sensitive anti-collapse and correctly signed effectivity/counting certificates.
6. Identify which proved outputs are consumed by existing receivers, without placing the unpaid estimate in a premise.

## Current mathematical question

Can normalized cofactor forcing be retained in a useful defect state when its pointwise limit vanishes but its global pronic norm does not? Determine the exact forcing scale and which pairings, rather than separate norms, admit compactness or arithmetic bounds.

## Deliverables and verification

- Own Lean subfolder and umbrella, wired into the appropriate umbrella.
- Foundational README explaining motivation, objects, language, mechanisms, traps, research questions, tools, pillar theorems, programme relationships and contribution criteria.
- Substantive theorem modules, unconditional actual-source consequences and explicit remaining gaps.
- Foreground `lake --old env lean` checks of each new module; no umbrella/full build or raised limits.
- Persistent research evidence in `logs/arithmetic-defect-rigidity-research.txt`.

## Proof status

The forcing floor and actual-source VK comparison in `TheForcingDominatesTheReceiver.lean`
passed Lean. `ForcingScaleSeparation.lean` also passed: vanishing receiver/forcing ratio,
divergent inverse ratio, exact unsigned-majorant comparison and impossibility of one common
scalar normalization. `FixedSuccessorsDisappearFromEscapingProfiles.lean` passed with bounded
actual increments, quadratic successor cost and an admission-or-collapse dichotomy.
`TheCofactorTailCarriesTheForcing.lean` passed with uniform cutoff and VK budgets, and convergence
of every fixed signed cofactor tail to the complete forcing.
`TheForcingSplitsIntoAPowerAndAnAdmittedRemainder.lean` passed its required dependency build:
the explicit power subtraction and the global remainder budget are accepted.
`TheForcingHasFinitePronicMass.lean` also passed: its exact prime-power mass, least-upper-bound
property and logarithmic derivative identity are accepted.
`TheActualReceiverHasAnAbsolutePoleTrace.lean` passed its dependency build: absolute endpoint
trace, dominated boundary passage and exact forcing coefficient are accepted.
`TheRenormalizedCofactorIsAntipodalOnEscape.lean` passed: signed antipodality and total-variation
control of the localized signed density error are accepted.
Twelve further modules have paper arguments and Lean sources; their audits remain unfinished:

- `MovingLocalizationsRetainTheSignedDensity`: arbitrary bounded horizon-dependent cell
  multipliers retain the signed density with one uniform remainder budget.
- `TheResidualAndPoleTraceDetermineTheRow`: exact inverse reconstruction, injectivity of
  the residual/trace pair and containment of any residual kernel in one explicit row line.
- `CofactorRenormalizationHasABoundedDilationCommutator`: exact rank-one commutator and
  uniform source trace budget, including moving integer dilations.
- `CountableCofactorCovariancesHaveACommonLimit`: one common subsequence retaining every fixed
  signed cofactor covariance, unit receiver mass, finite packet positivity and simultaneous
  dilation contraction.
- `TheReceiverIsTheGramTangent`: exact signed Gram distance and determinant, degeneration in
  forcing normalization, unit distance in receiver normalization.
- `CofactorSuccessorWordsHaveABoundaryCost`: the word action's denominator/boundary sandwich,
  actual receiver energy cost, bounded forcing work and fixed-word collapse in both quantities.
- `ForcingEscapesAMovingCofactorWindow`: a source-defined growing cutoff
  `floor(log(F_T/E_T))` beyond which the signed tail still carries the complete forcing.
- `BoundedWordErrorsHaveAnAbsoluteHorizonTail`: absolute new-cell forcing and word-work
  budgets decaying with cutoff, uniformly in every final horizon.
- `ThePoleTraceDefinesALinearCofactorRenormalization`: a proved trace submodule, linear
  boundary functional and cofactor subtraction, with actual-source membership and paid residual.
- `FixedCofactorsHaveAHarmonicBoundaryTrace`: proved fixed-dilation domain stability and
  exact harmonic trace budget for finite damped cofactor packets.
- `EnergyQuantilesRetainDiffuseEscape`: source cell-energy and block budgets, first crossings,
  monotonicity, uniform overshoot and normalized interval errors.
- `EnergyQuantilesPreserveTheSignedCofactorPairing`: uniform transport of actual signed
  renormalized cofactor work to energy coordinates, with explicit error tending to zero on escape.

`EnergyQuantilesRetainDiffuseEscape` is being rechecked after repairs to finite-sum expansion,
a successor/cast simplification loop and a subtype-coercion mismatch. The prior failed check
generated no dependency object. Diagnostics are saved in
`logs/arithmetic-defect-rigidity-quantile-audit.txt`.

The foundational README explains these mechanisms and the complete programme. Its theorem
claims must be reconciled with the finished audits. The own umbrella and MainTheorems import
are wired for the eight accepted modules; remaining imports and final no-output-file audits remain. Global source exclusion, complete
joint extraction, stronger signed covariance,
repairing-module transport, global allocation, multiplicity-sensitive anti-collapse and source
effectivity remain open. These are substantive parts of the user's goal, not optional follow-ups.

## Next mathematical targets

The smooth-power asymptotic, first-pronic-moment law, Mellin-cell dilation law and bounded-energy
Mellin functional are existing THIM results, reused rather than reproposed. The forcing
subtraction defines an affine residual of the actual source. A linear operator on the absolute
trace domain is written but awaits audit; its boundedness and domain invariance are not proved.

The energy-quantile carrier and its signed renormalized cofactor pairing now have quantitative
paper proofs and Lean sources. Countable fixed-cofactor covariance extraction has a paper proof and a Lean source awaiting
audit. A complete joint state must additionally retain successor data, rates and moving support. The quantile transport does not provide
the missing arithmetic exclusion estimate.
