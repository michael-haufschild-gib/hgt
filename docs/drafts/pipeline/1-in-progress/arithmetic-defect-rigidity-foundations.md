# Arithmetic defect rigidity: source constraints on escaping critical energy

Status: research in progress.

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
Seven further modules have paper arguments and Lean sources; their audits are in progress:

- `TheReceiverIsTheGramTangent`: exact signed Gram distance and determinant, degeneration in
  forcing normalization, unit distance in receiver normalization.
- `CofactorSuccessorWordsHaveABoundaryCost`: the word action's denominator/boundary sandwich,
  actual receiver energy cost, bounded forcing work and fixed-word collapse in both quantities.
- `ForcingEscapesAMovingCofactorWindow`: a source-defined growing cutoff
  `floor(log(F_T/E_T))` beyond which the signed tail still carries the complete forcing.
- `TheForcingSplitsIntoAPowerAndAnAdmittedRemainder`: exact smooth-power subtraction,
  uniform global remainder norm, and the paid actual cofactor residual.
- `TheForcingHasFinitePronicMass`: uniform dual mass, exact prime-power mass
  `-zeta'(1+epsilon)/zeta(1+epsilon)`, and its least-upper-bound property.
- `TheRenormalizedCofactorIsAntipodalOnEscape`: the exact signed residual identity and
  normalized cofactor pairing approaching `-1` on the escaping branch.
- `TheActualReceiverHasAnAbsolutePoleTrace`: absolute Mellin trace at `1-epsilon`, its
  extension from the convergent side, and exact equality with the forcing power coefficient.

The foundational README explains these mechanisms and the complete programme. Its theorem
claims must be reconciled with the finished audits. Umbrella wiring and final no-output-file
audits remain. Global source exclusion, complete joint extraction, stronger signed covariance,
repairing-module transport, global allocation, multiplicity-sensitive anti-collapse and source
effectivity remain open. These are substantive parts of the user's goal, not optional follow-ups.

## Next mathematical targets

The smooth-power asymptotic, first-pronic-moment law, Mellin-cell dilation law and bounded-energy
Mellin functional are existing THIM results, reused rather than reproposed. The forcing
subtraction defines an affine residual of the actual source; a bounded linear operator has not
been constructed.

Two extraction targets remain under investigation: a source energy-quantile carrier with
explicit boundary error, and a joint state retaining signed cofactor covariances after the
forcing power is subtracted. Neither generic compactness nor quantile coordinates provide
the missing arithmetic exclusion estimate.
