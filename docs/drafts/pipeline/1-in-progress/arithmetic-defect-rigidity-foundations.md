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

No new theorem claimed yet. Existing normalization and fixed-window escape are inputs. Global source exclusion remains unpaid.
